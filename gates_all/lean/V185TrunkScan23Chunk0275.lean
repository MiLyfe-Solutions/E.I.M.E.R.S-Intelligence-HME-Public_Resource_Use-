import V185TrunkScan23Chunk0274

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1626793 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_1626793 : Nat := 118140960795 + 1626793 * 2 ^ 59
def prefixEnd_1626793 : Nat := 4983230072969 + 3 ^ 40 * 1626793 * 2
def baseEnd_1626793 : Nat := 835326734369758898606021

theorem tailTrace_1626793 : CollatzResearch.WordTrace tailWord_1626793 prefixEnd_1626793 835326734369758898606021 := by
  unfold tailWord_1626793
  simp only [CollatzResearch.WordTrace]
  refine ⟨59334015195414269970005033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39556010130276179980003355 59334015195414269970005033)
  ·
    refine ⟨44500511396560702477503775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59334015195414269970005033 44500511396560702477503775)
    ·
      refine ⟨66750767094841053716255663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44500511396560702477503775 66750767094841053716255663)
      ·
        refine ⟨100126150642261580574383495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66750767094841053716255663 100126150642261580574383495)
        ·
          refine ⟨150189225963392370861575243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100126150642261580574383495 150189225963392370861575243)
          ·
            refine ⟨225283838945088556292362865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150189225963392370861575243 225283838945088556292362865)
            ·
              refine ⟨168962879208816417219272149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225283838945088556292362865 168962879208816417219272149)
              ·
                refine ⟨3960067481456634778576691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 168962879208816417219272149 3960067481456634778576691)
                ·
                  refine ⟨5940101222184952167865037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960067481456634778576691 5940101222184952167865037)
                  ·
                    refine ⟨2227537958319357062949389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5940101222184952167865037 2227537958319357062949389)
                    ·
                      refine ⟨835326734369758898606021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227537958319357062949389 835326734369758898606021)
                      ·
                        rfl

theorem cell23_1626793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_1626793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626793 prefixEnd_1626793 := by exact prefixLift 1626793
  have htrace : WordTrace (prefixWord ++ tailWord_1626793) baseStart_1626793 baseEnd_1626793 := by
    simpa [prefixWord, tailWord_1626793, baseEnd_1626793] using wordTrace_append hprefix tailTrace_1626793
  have hstable : (prefixWord ++ tailWord_1626793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626793).length < 2 ^ (prefixWord ++ tailWord_1626793).sum := by decide
  have hdescent : baseEnd_1626793 < baseStart_1626793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626810 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_1626810 : Nat := 118140960795 + 1626810 * 2 ^ 59
def prefixEnd_1626810 : Nat := 4983230072969 + 3 ^ 40 * 1626810 * 2
def baseEnd_1626810 : Nat := 835335463540885332093443

theorem tailTrace_1626810 : CollatzResearch.WordTrace tailWord_1626810 prefixEnd_1626810 835335463540885332093443 := by
  unfold tailWord_1626810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833658809088170468343471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39556423490901787915582589 14833658809088170468343471)
  ·
    refine ⟨22250488213632255702515207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14833658809088170468343471 22250488213632255702515207)
    ·
      refine ⟨33375732320448383553772811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22250488213632255702515207 33375732320448383553772811)
      ·
        refine ⟨50063598480672575330659217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33375732320448383553772811 50063598480672575330659217)
        ·
          refine ⟨37547698860504431497994413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50063598480672575330659217 37547698860504431497994413)
          ·
            refine ⟨14080387072689161811747905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37547698860504431497994413 14080387072689161811747905)
            ·
              refine ⟨10560290304516871358810929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14080387072689161811747905 10560290304516871358810929)
              ·
                refine ⟨7920217728387653519108197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560290304516871358810929 7920217728387653519108197)
                ·
                  refine ⟨1485040824072685034832787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7920217728387653519108197 1485040824072685034832787)
                  ·
                    refine ⟨2227561236109027552249181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485040824072685034832787 2227561236109027552249181)
                    ·
                      refine ⟨835335463540885332093443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227561236109027552249181 835335463540885332093443)
                      ·
                        rfl

theorem cell23_1626810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_1626810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626810 prefixEnd_1626810 := by exact prefixLift 1626810
  have htrace : WordTrace (prefixWord ++ tailWord_1626810) baseStart_1626810 baseEnd_1626810 := by
    simpa [prefixWord, tailWord_1626810, baseEnd_1626810] using wordTrace_append hprefix tailTrace_1626810
  have hstable : (prefixWord ++ tailWord_1626810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626810).length < 2 ^ (prefixWord ++ tailWord_1626810).sum := by decide
  have hdescent : baseEnd_1626810 < baseStart_1626810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626844 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1626844 : Nat := 118140960795 + 1626844 * 2 ^ 59
def prefixEnd_1626844 : Nat := 4983230072969 + 3 ^ 40 * 1626844 * 2
def baseEnd_1626844 : Nat := 835352921883138199068287

theorem tailTrace_1626844 : CollatzResearch.WordTrace tailWord_1626844 prefixEnd_1626844 835352921883138199068287 := by
  unfold tailWord_1626844
  simp only [CollatzResearch.WordTrace]
  refine ⟨29667937659114752840055793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39557250212153003786741057 29667937659114752840055793)
  ·
    refine ⟨22250953244336064630041845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29667937659114752840055793 22250953244336064630041845)
    ·
      refine ⟨2086026866656506059066423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22250953244336064630041845 2086026866656506059066423)
      ·
        refine ⟨3129040299984759088599635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086026866656506059066423 3129040299984759088599635)
        ·
          refine ⟨4693560449977138632899453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129040299984759088599635 4693560449977138632899453)
          ·
            refine ⟨1760085168741426987337295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4693560449977138632899453 1760085168741426987337295)
            ·
              refine ⟨2640127753112140481005943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760085168741426987337295 2640127753112140481005943)
              ·
                refine ⟨3960191629668210721508915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640127753112140481005943 3960191629668210721508915)
                ·
                  refine ⟨5940287444502316082263373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960191629668210721508915 5940287444502316082263373)
                  ·
                    refine ⟨2227607791688368530848765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5940287444502316082263373 2227607791688368530848765)
                    ·
                      refine ⟨835352921883138199068287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227607791688368530848765 835352921883138199068287)
                      ·
                        rfl

theorem cell23_1626844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1626844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626844 prefixEnd_1626844 := by exact prefixLift 1626844
  have htrace : WordTrace (prefixWord ++ tailWord_1626844) baseStart_1626844 baseEnd_1626844 := by
    simpa [prefixWord, tailWord_1626844, baseEnd_1626844] using wordTrace_append hprefix tailTrace_1626844
  have hstable : (prefixWord ++ tailWord_1626844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626844).length < 2 ^ (prefixWord ++ tailWord_1626844).sum := by decide
  have hdescent : baseEnd_1626844 < baseStart_1626844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626870 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1626870 : Nat := 118140960795 + 1626870 * 2 ^ 59
def prefixEnd_1626870 : Nat := 4983230072969 + 3 ^ 40 * 1626870 * 2
def baseEnd_1626870 : Nat := 835366272380155097343167

theorem tailTrace_1626870 : CollatzResearch.WordTrace tailWord_1626870 prefixEnd_1626870 835366272380155097343167 := by
  unfold tailWord_1626870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708551476008457007534879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39557882410756874747038709 3708551476008457007534879)
  ·
    refine ⟨5562827214012685511302319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3708551476008457007534879 5562827214012685511302319)
    ·
      refine ⟨8344240821019028266953479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5562827214012685511302319 8344240821019028266953479)
      ·
        refine ⟨12516361231528542400430219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8344240821019028266953479 12516361231528542400430219)
        ·
          refine ⟨18774541847292813600645329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12516361231528542400430219 18774541847292813600645329)
          ·
            refine ⟨14080906385469610200483997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18774541847292813600645329 14080906385469610200483997)
            ·
              refine ⟨5280339894551103825181499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14080906385469610200483997 5280339894551103825181499)
              ·
                refine ⟨7920509841826655737772249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280339894551103825181499 7920509841826655737772249)
                ·
                  refine ⟨5940382381369991803329187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7920509841826655737772249 5940382381369991803329187)
                  ·
                    refine ⟨8910573572054987704993781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5940382381369991803329187 8910573572054987704993781)
                    ·
                      refine ⟨835366272380155097343167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8910573572054987704993781 835366272380155097343167)
                      ·
                        rfl

theorem cell23_1626870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1626870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626870 prefixEnd_1626870 := by exact prefixLift 1626870
  have htrace : WordTrace (prefixWord ++ tailWord_1626870) baseStart_1626870 baseEnd_1626870 := by
    simpa [prefixWord, tailWord_1626870, baseEnd_1626870] using wordTrace_append hprefix tailTrace_1626870
  have hstable : (prefixWord ++ tailWord_1626870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626870).length < 2 ^ (prefixWord ++ tailWord_1626870).sum := by decide
  have hdescent : baseEnd_1626870 < baseStart_1626870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626884 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1626884 : Nat := 118140960795 + 1626884 * 2 ^ 59
def prefixEnd_1626884 : Nat := 4983230072969 + 3 ^ 40 * 1626884 * 2
def baseEnd_1626884 : Nat := 835373461109318042568103

theorem tailTrace_1626884 : CollatzResearch.WordTrace tailWord_1626884 prefixEnd_1626884 835373461109318042568103 := by
  unfold tailWord_1626884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29668667119042296255783853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39558222825389728341045137 29668667119042296255783853)
  ·
    refine ⟨11125750169640861095918945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29668667119042296255783853 11125750169640861095918945)
    ·
      refine ⟨8344312627230645821939209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11125750169640861095918945 8344312627230645821939209)
      ·
        refine ⟨6258234470422984366454407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8344312627230645821939209 6258234470422984366454407)
        ·
          refine ⟨9387351705634476549681611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258234470422984366454407 9387351705634476549681611)
          ·
            refine ⟨14081027558451714824522417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387351705634476549681611 14081027558451714824522417)
            ·
              refine ⟨10560770668838786118391813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14081027558451714824522417 10560770668838786118391813)
              ·
                refine ⟨1980144500407272397198465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10560770668838786118391813 1980144500407272397198465)
                ·
                  refine ⟨1485108375305454297898849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1980144500407272397198465 1485108375305454297898849)
                  ·
                    refine ⟨1113831281479090723424137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1485108375305454297898849 1113831281479090723424137)
                    ·
                      refine ⟨835373461109318042568103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113831281479090723424137 835373461109318042568103)
                      ·
                        rfl

theorem cell23_1626884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1626884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626884 prefixEnd_1626884 := by exact prefixLift 1626884
  have htrace : WordTrace (prefixWord ++ tailWord_1626884) baseStart_1626884 baseEnd_1626884 := by
    simpa [prefixWord, tailWord_1626884, baseEnd_1626884] using wordTrace_append hprefix tailTrace_1626884
  have hstable : (prefixWord ++ tailWord_1626884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626884).length < 2 ^ (prefixWord ++ tailWord_1626884).sum := by decide
  have hdescent : baseEnd_1626884 < baseStart_1626884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626913 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1626913 : Nat := 118140960795 + 1626913 * 2 ^ 59
def prefixEnd_1626913 : Nat := 4983230072969 + 3 ^ 40 * 1626913 * 2
def baseEnd_1626913 : Nat := 835388352048298429105469

theorem tailTrace_1626913 : CollatzResearch.WordTrace tailWord_1626913 prefixEnd_1626913 835388352048298429105469 := by
  unfold tailWord_1626913
  simp only [CollatzResearch.WordTrace]
  refine ⟨59338391954979530464373393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39558927969986353642915595 59338391954979530464373393)
  ·
    refine ⟨44503793966234647848280045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59338391954979530464373393 44503793966234647848280045)
    ·
      refine ⟨16688922737337992943105017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44503793966234647848280045 16688922737337992943105017)
      ·
        refine ⟨12516692053003494707328763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16688922737337992943105017 12516692053003494707328763)
        ·
          refine ⟨18775038079505242060993145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12516692053003494707328763 18775038079505242060993145)
          ·
            refine ⟨14081278559628931545744859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18775038079505242060993145 14081278559628931545744859)
            ·
              refine ⟨21121917839443397318617289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14081278559628931545744859 21121917839443397318617289)
              ·
                refine ⟨15841438379582547988962967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21121917839443397318617289 15841438379582547988962967)
                ·
                  refine ⟨23762157569373821983444451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15841438379582547988962967 23762157569373821983444451)
                  ·
                    refine ⟨35643236354060732975166677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23762157569373821983444451 35643236354060732975166677)
                    ·
                      refine ⟨835388352048298429105469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35643236354060732975166677 835388352048298429105469)
                      ·
                        rfl

theorem cell23_1626913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1626913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626913 prefixEnd_1626913 := by exact prefixLift 1626913
  have htrace : WordTrace (prefixWord ++ tailWord_1626913) baseStart_1626913 baseEnd_1626913 := by
    simpa [prefixWord, tailWord_1626913, baseEnd_1626913] using wordTrace_append hprefix tailTrace_1626913
  have hstable : (prefixWord ++ tailWord_1626913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626913).length < 2 ^ (prefixWord ++ tailWord_1626913).sum := by decide
  have hdescent : baseEnd_1626913 < baseStart_1626913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626941 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 5]
def baseStart_1626941 : Nat := 118140960795 + 1626941 * 2 ^ 59
def prefixEnd_1626941 : Nat := 4983230072969 + 3 ^ 40 * 1626941 * 2
def baseEnd_1626941 : Nat := 92822525500736035506149

theorem tailTrace_1626941 : CollatzResearch.WordTrace tailWord_1626941 prefixEnd_1626941 92822525500736035506149 := by
  unfold tailWord_1626941
  simp only [CollatzResearch.WordTrace]
  refine ⟨59339413198878091246392677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39559608799252060830928451 59339413198878091246392677)
  ·
    refine ⟨11126139974789642108698627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59339413198878091246392677 11126139974789642108698627)
    ·
      refine ⟨16689209962184463163047941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11126139974789642108698627 16689209962184463163047941)
      ·
        refine ⟨3129226867909586843071489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16689209962184463163047941 3129226867909586843071489)
        ·
          refine ⟨2346920150932190132303617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3129226867909586843071489 2346920150932190132303617)
          ·
            refine ⟨1760190113199142599227713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346920150932190132303617 1760190113199142599227713)
            ·
              refine ⟨1320142584899356949420785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760190113199142599227713 1320142584899356949420785)
              ·
                refine ⟨990106938674517712065589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320142584899356949420785 990106938674517712065589)
                ·
                  refine ⟨92822525500736035506149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 990106938674517712065589 92822525500736035506149)
                  ·
                    rfl

theorem cell23_1626941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_1626941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626941 prefixEnd_1626941 := by exact prefixLift 1626941
  have htrace : WordTrace (prefixWord ++ tailWord_1626941) baseStart_1626941 baseEnd_1626941 := by
    simpa [prefixWord, tailWord_1626941, baseEnd_1626941] using wordTrace_append hprefix tailTrace_1626941
  have hstable : (prefixWord ++ tailWord_1626941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626941).length < 2 ^ (prefixWord ++ tailWord_1626941).sum := by decide
  have hdescent : baseEnd_1626941 < baseStart_1626941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626960 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_1626960 : Nat := 118140960795 + 1626960 * 2 ^ 59
def prefixEnd_1626960 : Nat := 4983230072969 + 3 ^ 40 * 1626960 * 2
def baseEnd_1626960 : Nat := 835412485639059745217753

theorem tailTrace_1626960 : CollatzResearch.WordTrace tailWord_1626960 prefixEnd_1626960 835412485639059745217753 := by
  unfold tailWord_1626960
  simp only [CollatzResearch.WordTrace]
  refine ⟨29670053092904628745667167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39560070790539504994222889 29670053092904628745667167)
  ·
    refine ⟨44505079639356943118500751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29670053092904628745667167 44505079639356943118500751)
    ·
      refine ⟨66757619459035414677751127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44505079639356943118500751 66757619459035414677751127)
      ·
        refine ⟨100136429188553122016626691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66757619459035414677751127 100136429188553122016626691)
        ·
          refine ⟨150204643782829683024940037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100136429188553122016626691 150204643782829683024940037)
          ·
            refine ⟨28163370709280565567176257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150204643782829683024940037 28163370709280565567176257)
            ·
              refine ⟨21122528031960424175382193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28163370709280565567176257 21122528031960424175382193)
              ·
                refine ⟨15841896023970318131536645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21122528031960424175382193 15841896023970318131536645)
                ·
                  refine ⟨2970355504494434649663121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15841896023970318131536645 2970355504494434649663121)
                  ·
                    refine ⟨2227766628370825987247341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2970355504494434649663121 2227766628370825987247341)
                    ·
                      refine ⟨835412485639059745217753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227766628370825987247341 835412485639059745217753)
                      ·
                        rfl

theorem cell23_1626960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_1626960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626960 prefixEnd_1626960 := by exact prefixLift 1626960
  have htrace : WordTrace (prefixWord ++ tailWord_1626960) baseStart_1626960 baseEnd_1626960 := by
    simpa [prefixWord, tailWord_1626960, baseEnd_1626960] using wordTrace_append hprefix tailTrace_1626960
  have hstable : (prefixWord ++ tailWord_1626960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626960).length < 2 ^ (prefixWord ++ tailWord_1626960).sum := by decide
  have hdescent : baseEnd_1626960 < baseStart_1626960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626967 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 3, 4]
def baseStart_1626967 : Nat := 118140960795 + 1626967 * 2 ^ 59
def prefixEnd_1626967 : Nat := 4983230072969 + 3 ^ 40 * 1626967 * 2
def baseEnd_1626967 : Nat := 278472026667880405943407

theorem tailTrace_1626967 : CollatzResearch.WordTrace tailWord_1626967 prefixEnd_1626967 278472026667880405943407 := by
  unfold tailWord_1626967
  simp only [CollatzResearch.WordTrace]
  refine ⟨59340361496783897686839155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39560240997855931791226103 59340361496783897686839155)
  ·
    refine ⟨89010542245175846530258733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59340361496783897686839155 89010542245175846530258733)
    ·
      refine ⟨33378953341940942448847025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89010542245175846530258733 33378953341940942448847025)
      ·
        refine ⟨25034215006455706836635269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33378953341940942448847025 25034215006455706836635269)
        ·
          refine ⟨4693915313710445031869113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25034215006455706836635269 4693915313710445031869113)
          ·
            refine ⟨3520436485282833773901835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4693915313710445031869113 3520436485282833773901835)
            ·
              refine ⟨5280654727924250660852753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520436485282833773901835 5280654727924250660852753)
              ·
                refine ⟨3960491045943187995639565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280654727924250660852753 3960491045943187995639565)
                ·
                  refine ⟨1485184142228695498364837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3960491045943187995639565 1485184142228695498364837)
                  ·
                    refine ⟨278472026667880405943407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485184142228695498364837 278472026667880405943407)
                    ·
                      rfl

theorem cell23_1626967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_1626967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626967 prefixEnd_1626967 := by exact prefixLift 1626967
  have htrace : WordTrace (prefixWord ++ tailWord_1626967) baseStart_1626967 baseEnd_1626967 := by
    simpa [prefixWord, tailWord_1626967, baseEnd_1626967] using wordTrace_append hprefix tailTrace_1626967
  have hstable : (prefixWord ++ tailWord_1626967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626967).length < 2 ^ (prefixWord ++ tailWord_1626967).sum := by decide
  have hdescent : baseEnd_1626967 < baseStart_1626967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626984 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1626984 : Nat := 118140960795 + 1626984 * 2 ^ 59
def prefixEnd_1626984 : Nat := 4983230072969 + 3 ^ 40 * 1626984 * 2
def baseEnd_1626984 : Nat := 278474936391589217105881

theorem tailTrace_1626984 : CollatzResearch.WordTrace tailWord_1626984 prefixEnd_1626984 278474936391589217105881 := by
  unfold tailWord_1626984
  simp only [CollatzResearch.WordTrace]
  refine ⟨29670490768861154795104003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39560654358481539726805337 29670490768861154795104003)
  ·
    refine ⟨44505736153291732192656005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29670490768861154795104003 44505736153291732192656005)
    ·
      refine ⟨8344825528742199786123001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44505736153291732192656005 8344825528742199786123001)
      ·
        refine ⟨6258619146556649839592251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8344825528742199786123001 6258619146556649839592251)
        ·
          refine ⟨9387928719834974759388377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258619146556649839592251 9387928719834974759388377)
          ·
            refine ⟨7040946539876231069541283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9387928719834974759388377 7040946539876231069541283)
            ·
              refine ⟨10561419809814346604311925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040946539876231069541283 10561419809814346604311925)
              ·
                refine ⟨990133107170094994154243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10561419809814346604311925 990133107170094994154243)
                ·
                  refine ⟨1485199660755142491231365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990133107170094994154243 1485199660755142491231365)
                  ·
                    refine ⟨278474936391589217105881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485199660755142491231365 278474936391589217105881)
                    ·
                      rfl

theorem cell23_1626984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1626984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626984 prefixEnd_1626984 := by exact prefixLift 1626984
  have htrace : WordTrace (prefixWord ++ tailWord_1626984) baseStart_1626984 baseEnd_1626984 := by
    simpa [prefixWord, tailWord_1626984, baseEnd_1626984] using wordTrace_append hprefix tailTrace_1626984
  have hstable : (prefixWord ++ tailWord_1626984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626984).length < 2 ^ (prefixWord ++ tailWord_1626984).sum := by decide
  have hdescent : baseEnd_1626984 < baseStart_1626984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626997 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 6]
def baseStart_1626997 : Nat := 118140960795 + 1626997 * 2 ^ 59
def prefixEnd_1626997 : Nat := 4983230072969 + 3 ^ 40 * 1626997 * 2
def baseEnd_1626997 : Nat := 92825720491475122272787

theorem tailTrace_1626997 : CollatzResearch.WordTrace tailWord_1626997 prefixEnd_1626997 92825720491475122272787 := by
  unfold tailWord_1626997
  simp only [CollatzResearch.WordTrace]
  refine ⟨59341455686675212810431245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39560970457783475206954163 59341455686675212810431245)
  ·
    refine ⟨22253045882503204803911717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59341455686675212810431245 22253045882503204803911717)
    ·
      refine ⟨4172446102969350900733447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22253045882503204803911717 4172446102969350900733447)
      ·
        refine ⟨6258669154454026351100171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4172446102969350900733447 6258669154454026351100171)
        ·
          refine ⟨9388003731681039526650257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258669154454026351100171 9388003731681039526650257)
          ·
            refine ⟨7041002798760779644987693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9388003731681039526650257 7041002798760779644987693)
            ·
              refine ⟨2640376049535292366870385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7041002798760779644987693 2640376049535292366870385)
              ·
                refine ⟨1980282037151469275152789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2640376049535292366870385 1980282037151469275152789)
                ·
                  refine ⟨92825720491475122272787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1980282037151469275152789 92825720491475122272787)
                  ·
                    rfl

theorem cell23_1626997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_1626997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626997 prefixEnd_1626997 := by exact prefixLift 1626997
  have htrace : WordTrace (prefixWord ++ tailWord_1626997) baseStart_1626997 baseEnd_1626997 := by
    simpa [prefixWord, tailWord_1626997, baseEnd_1626997] using wordTrace_append hprefix tailTrace_1626997
  have hstable : (prefixWord ++ tailWord_1626997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626997).length < 2 ^ (prefixWord ++ tailWord_1626997).sum := by decide
  have hdescent : baseEnd_1626997 < baseStart_1626997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627007 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 3]
def baseStart_1627007 : Nat := 118140960795 + 1627007 * 2 ^ 59
def prefixEnd_1627007 : Nat := 4983230072969 + 3 ^ 40 * 1627007 * 2
def baseEnd_1627007 : Nat := 835436619229821061330037

theorem tailTrace_1627007 : CollatzResearch.WordTrace tailWord_1627007 prefixEnd_1627007 835436619229821061330037 := by
  unfold tailWord_1627007
  simp only [CollatzResearch.WordTrace]
  refine ⟨59341820416638984518295275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39561213611092656345530183 59341820416638984518295275)
  ·
    refine ⟨89012730624958476777442913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59341820416638984518295275 89012730624958476777442913)
    ·
      refine ⟨66759547968718857583082185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89012730624958476777442913 66759547968718857583082185)
      ·
        refine ⟨50069660976539143187311639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66759547968718857583082185 50069660976539143187311639)
        ·
          refine ⟨75104491464808714780967459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50069660976539143187311639 75104491464808714780967459)
          ·
            refine ⟨112656737197213072171451189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75104491464808714780967459 112656737197213072171451189)
            ·
              refine ⟨10561569112238725516073549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112656737197213072171451189 10561569112238725516073549)
              ·
                refine ⟨3960588417089522068527581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10561569112238725516073549 3960588417089522068527581)
                ·
                  refine ⟨1485220656408570775697843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3960588417089522068527581 1485220656408570775697843)
                  ·
                    refine ⟨2227830984612856163546765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485220656408570775697843 2227830984612856163546765)
                    ·
                      refine ⟨835436619229821061330037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227830984612856163546765 835436619229821061330037)
                      ·
                        rfl

theorem cell23_1627007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_1627007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627007 prefixEnd_1627007 := by exact prefixLift 1627007
  have htrace : WordTrace (prefixWord ++ tailWord_1627007) baseStart_1627007 baseEnd_1627007 := by
    simpa [prefixWord, tailWord_1627007, baseEnd_1627007] using wordTrace_append hprefix tailTrace_1627007
  have hstable : (prefixWord ++ tailWord_1627007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627007).length < 2 ^ (prefixWord ++ tailWord_1627007).sum := by decide
  have hdescent : baseEnd_1627007 < baseStart_1627007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627017 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 1, 5, 2]
def baseStart_1627017 : Nat := 118140960795 + 1627017 * 2 ^ 59
def prefixEnd_1627017 : Nat := 4983230072969 + 3 ^ 40 * 1627017 * 2
def baseEnd_1627017 : Nat := 835441754036366022204991

theorem tailTrace_1627017 : CollatzResearch.WordTrace tailWord_1627017 prefixEnd_1627017 835441754036366022204991 := by
  unfold tailWord_1627017
  simp only [CollatzResearch.WordTrace]
  refine ⟨59342185146602756226159305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39561456764401837484106203 59342185146602756226159305)
  ·
    refine ⟨44506638859952067169619479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59342185146602756226159305 44506638859952067169619479)
    ·
      refine ⟨66759958289928100754429219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44506638859952067169619479 66759958289928100754429219)
      ·
        refine ⟨100139937434892151131643829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66759958289928100754429219 100139937434892151131643829)
        ·
          refine ⟨9388119134521139168591609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100139937434892151131643829 9388119134521139168591609)
          ·
            refine ⟨7041089350890854376443707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9388119134521139168591609 7041089350890854376443707)
            ·
              refine ⟨10561634026336281564665561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041089350890854376443707 10561634026336281564665561)
              ·
                refine ⟨7921225519752211173499171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10561634026336281564665561 7921225519752211173499171)
                ·
                  refine ⟨11881838279628316760248757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921225519752211173499171 11881838279628316760248757)
                  ·
                    refine ⟨1113922338715154696273321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11881838279628316760248757 1113922338715154696273321)
                    ·
                      refine ⟨835441754036366022204991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113922338715154696273321 835441754036366022204991)
                      ·
                        rfl

theorem cell23_1627017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 5, 2].length) (baseStart_1627017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627017 prefixEnd_1627017 := by exact prefixLift 1627017
  have htrace : WordTrace (prefixWord ++ tailWord_1627017) baseStart_1627017 baseEnd_1627017 := by
    simpa [prefixWord, tailWord_1627017, baseEnd_1627017] using wordTrace_append hprefix tailTrace_1627017
  have hstable : (prefixWord ++ tailWord_1627017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627017).length < 2 ^ (prefixWord ++ tailWord_1627017).sum := by decide
  have hdescent : baseEnd_1627017 < baseStart_1627017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627040 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_1627040 : Nat := 118140960795 + 1627040 * 2 ^ 59
def prefixEnd_1627040 : Nat := 4983230072969 + 3 ^ 40 * 1627040 * 2
def baseEnd_1627040 : Nat := 278484521363806477405795

theorem tailTrace_1627040 : CollatzResearch.WordTrace tailWord_1627040 prefixEnd_1627040 278484521363806477405795 := by
  unfold tailWord_1627040
  simp only [CollatzResearch.WordTrace]
  refine ⟨29671512012759715577123287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39562016017012954102831049 29671512012759715577123287)
  ·
    refine ⟨44507268019139573365684931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29671512012759715577123287 44507268019139573365684931)
    ·
      refine ⟨66760902028709360048527397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44507268019139573365684931 66760902028709360048527397)
      ·
        refine ⟨12517669130383005009098887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66760902028709360048527397 12517669130383005009098887)
        ·
          refine ⟨18776503695574507513648331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12517669130383005009098887 18776503695574507513648331)
          ·
            refine ⟨28164755543361761270472497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18776503695574507513648331 28164755543361761270472497)
            ·
              refine ⟨21123566657521320952854373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28164755543361761270472497 21123566657521320952854373)
              ·
                refine ⟨3960668748285247678660195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21123566657521320952854373 3960668748285247678660195)
                ·
                  refine ⟨5941003122427871517990293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960668748285247678660195 5941003122427871517990293)
                  ·
                    refine ⟨278484521363806477405795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5941003122427871517990293 278484521363806477405795)
                    ·
                      rfl

theorem cell23_1627040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_1627040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627040 prefixEnd_1627040 := by exact prefixLift 1627040
  have htrace : WordTrace (prefixWord ++ tailWord_1627040) baseStart_1627040 baseEnd_1627040 := by
    simpa [prefixWord, tailWord_1627040, baseEnd_1627040] using wordTrace_append hprefix tailTrace_1627040
  have hstable : (prefixWord ++ tailWord_1627040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627040).length < 2 ^ (prefixWord ++ tailWord_1627040).sum := by decide
  have hdescent : baseEnd_1627040 < baseStart_1627040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627094 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1627094 : Nat := 118140960795 + 1627094 * 2 ^ 59
def prefixEnd_1627094 : Nat := 4983230072969 + 3 ^ 40 * 1627094 * 2
def baseEnd_1627094 : Nat := 835481292046762220942137

theorem tailTrace_1627094 : CollatzResearch.WordTrace tailWord_1627094 prefixEnd_1627094 835481292046762220942137 := by
  unfold tailWord_1627094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709062097957737398544521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39563329044882532251141557 3709062097957737398544521)
  ·
    refine ⟨2781796573468303048908391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3709062097957737398544521 2781796573468303048908391)
    ·
      refine ⟨4172694860202454573362587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781796573468303048908391 4172694860202454573362587)
      ·
        refine ⟨6259042290303681860043881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4172694860202454573362587 6259042290303681860043881)
        ·
          refine ⟨4694281717727761395032911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259042290303681860043881 4694281717727761395032911)
          ·
            refine ⟨7041422576591642092549367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694281717727761395032911 7041422576591642092549367)
            ·
              refine ⟨10562133864887463138824051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041422576591642092549367 10562133864887463138824051)
              ·
                refine ⟨15843200797331194708236077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10562133864887463138824051 15843200797331194708236077)
                ·
                  refine ⟨5941200298999198015588529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15843200797331194708236077 5941200298999198015588529)
                  ·
                    refine ⟨4455900224249398511691397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941200298999198015588529 4455900224249398511691397)
                    ·
                      refine ⟨835481292046762220942137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4455900224249398511691397 835481292046762220942137)
                      ·
                        rfl

theorem cell23_1627094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1627094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627094 prefixEnd_1627094 := by exact prefixLift 1627094
  have htrace : WordTrace (prefixWord ++ tailWord_1627094) baseStart_1627094 baseEnd_1627094 := by
    simpa [prefixWord, tailWord_1627094, baseEnd_1627094] using wordTrace_append hprefix tailTrace_1627094
  have hstable : (prefixWord ++ tailWord_1627094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627094).length < 2 ^ (prefixWord ++ tailWord_1627094).sum := by decide
  have hdescent : baseEnd_1627094 < baseStart_1627094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627097 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_1627097 : Nat := 118140960795 + 1627097 * 2 ^ 59
def prefixEnd_1627097 : Nat := 4983230072969 + 3 ^ 40 * 1627097 * 2
def baseEnd_1627097 : Nat := 835482832488725709204623

theorem tailTrace_1627097 : CollatzResearch.WordTrace tailWord_1627097 prefixEnd_1627097 835482832488725709204623 := by
  unfold tailWord_1627097
  simp only [CollatzResearch.WordTrace]
  refine ⟨59345102986312929889071545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39563401990875286592714363 59345102986312929889071545)
  ·
    refine ⟨44508827239734697416803659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59345102986312929889071545 44508827239734697416803659)
    ·
      refine ⟨66763240859602046125205489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44508827239734697416803659 66763240859602046125205489)
      ·
        refine ⟨50072430644701534593904117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66763240859602046125205489 50072430644701534593904117)
        ·
          refine ⟨4694290372940768868178511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50072430644701534593904117 4694290372940768868178511)
          ·
            refine ⟨7041435559411153302267767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694290372940768868178511 7041435559411153302267767)
            ·
              refine ⟨10562153339116729953401651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041435559411153302267767 10562153339116729953401651)
              ·
                refine ⟨15843230008675094930102477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10562153339116729953401651 15843230008675094930102477)
                ·
                  refine ⟨5941211253253160598788429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15843230008675094930102477 5941211253253160598788429)
                  ·
                    refine ⟨2227954219969935224545661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5941211253253160598788429 2227954219969935224545661)
                    ·
                      refine ⟨835482832488725709204623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227954219969935224545661 835482832488725709204623)
                      ·
                        rfl

theorem cell23_1627097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_1627097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627097 prefixEnd_1627097 := by exact prefixLift 1627097
  have htrace : WordTrace (prefixWord ++ tailWord_1627097) baseStart_1627097 baseEnd_1627097 := by
    simpa [prefixWord, tailWord_1627097, baseEnd_1627097] using wordTrace_append hprefix tailTrace_1627097
  have hstable : (prefixWord ++ tailWord_1627097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627097).length < 2 ^ (prefixWord ++ tailWord_1627097).sum := by decide
  have hdescent : baseEnd_1627097 < baseStart_1627097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627165 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_1627165 : Nat := 118140960795 + 1627165 * 2 ^ 59
def prefixEnd_1627165 : Nat := 4983230072969 + 3 ^ 40 * 1627165 * 2
def baseEnd_1627165 : Nat := 835517749173231443154311

theorem tailTrace_1627165 : CollatzResearch.WordTrace tailWord_1627165 prefixEnd_1627165 835517749173231443154311 := by
  unfold tailWord_1627165
  simp only [CollatzResearch.WordTrace]
  refine ⟨59347583150066577502546949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39565055433377718335031299 59347583150066577502546949)
  ·
    refine ⟨11127671840637483281727553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59347583150066577502546949 11127671840637483281727553)
    ·
      refine ⟨8345753880478112461295665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11127671840637483281727553 8345753880478112461295665)
      ·
        refine ⟨6259315410358584345971749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8345753880478112461295665 6259315410358584345971749)
        ·
          refine ⟨1173621639442234564869703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6259315410358584345971749 1173621639442234564869703)
          ·
            refine ⟨1760432459163351847304555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173621639442234564869703 1760432459163351847304555)
            ·
              refine ⟨2640648688745027770956833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760432459163351847304555 2640648688745027770956833)
              ·
                refine ⟨1980486516558770828217625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2640648688745027770956833 1980486516558770828217625)
                ·
                  refine ⟨1485364887419078121163219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1980486516558770828217625 1485364887419078121163219)
                  ·
                    refine ⟨2228047331128617181744829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485364887419078121163219 2228047331128617181744829)
                    ·
                      refine ⟨835517749173231443154311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2228047331128617181744829 835517749173231443154311)
                      ·
                        rfl

theorem cell23_1627165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_1627165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627165 prefixEnd_1627165 := by exact prefixLift 1627165
  have htrace : WordTrace (prefixWord ++ tailWord_1627165) baseStart_1627165 baseEnd_1627165 := by
    simpa [prefixWord, tailWord_1627165, baseEnd_1627165] using wordTrace_append hprefix tailTrace_1627165
  have hstable : (prefixWord ++ tailWord_1627165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627165).length < 2 ^ (prefixWord ++ tailWord_1627165).sum := by decide
  have hdescent : baseEnd_1627165 < baseStart_1627165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627167 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1627167 : Nat := 118140960795 + 1627167 * 2 ^ 59
def prefixEnd_1627167 : Nat := 4983230072969 + 3 ^ 40 * 1627167 * 2
def baseEnd_1627167 : Nat := 835518776134540435329301

theorem tailTrace_1627167 : CollatzResearch.WordTrace tailWord_1627167 prefixEnd_1627167 835518776134540435329301 := by
  unfold tailWord_1627167
  simp only [CollatzResearch.WordTrace]
  refine ⟨59347656096059331844119755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39565104064039554562746503 59347656096059331844119755)
  ·
    refine ⟨89021484144088997766179633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59347656096059331844119755 89021484144088997766179633)
    ·
      refine ⟨66766113108066748324634725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89021484144088997766179633 66766113108066748324634725)
      ·
        refine ⟨12518646207762515310869011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66766113108066748324634725 12518646207762515310869011)
        ·
          refine ⟨18777969311643772966303517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12518646207762515310869011 18777969311643772966303517)
          ·
            refine ⟨7041738491866414862363819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18777969311643772966303517 7041738491866414862363819)
            ·
              refine ⟨10562607737799622293545729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041738491866414862363819 10562607737799622293545729)
              ·
                refine ⟨7921955803349716720159297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10562607737799622293545729 7921955803349716720159297)
                ·
                  refine ⟨5941466852512287540119473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7921955803349716720159297 5941466852512287540119473)
                  ·
                    refine ⟨4456100139384215655089605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941466852512287540119473 4456100139384215655089605)
                    ·
                      refine ⟨835518776134540435329301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4456100139384215655089605 835518776134540435329301)
                      ·
                        rfl

theorem cell23_1627167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1627167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627167 prefixEnd_1627167 := by exact prefixLift 1627167
  have htrace : WordTrace (prefixWord ++ tailWord_1627167) baseStart_1627167 baseEnd_1627167 := by
    simpa [prefixWord, tailWord_1627167, baseEnd_1627167] using wordTrace_append hprefix tailTrace_1627167
  have hstable : (prefixWord ++ tailWord_1627167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627167).length < 2 ^ (prefixWord ++ tailWord_1627167).sum := by decide
  have hdescent : baseEnd_1627167 < baseStart_1627167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627171 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 4, 2, 2]
def baseStart_1627171 : Nat := 118140960795 + 1627171 * 2 ^ 59
def prefixEnd_1627171 : Nat := 4983230072969 + 3 ^ 40 * 1627171 * 2
def baseEnd_1627171 : Nat := 835520830057158419679283

theorem tailTrace_1627171 : CollatzResearch.WordTrace tailWord_1627171 prefixEnd_1627171 835520830057158419679283 := by
  unfold tailWord_1627171
  simp only [CollatzResearch.WordTrace]
  refine ⟨59347801988044840527265367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39565201325363227018176911 59347801988044840527265367)
  ·
    refine ⟨89021702982067260790898051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59347801988044840527265367 89021702982067260790898051)
    ·
      refine ⟨133532554473100891186347077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89021702982067260790898051 133532554473100891186347077)
      ·
        refine ⟨25037353963706417097440077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133532554473100891186347077 25037353963706417097440077)
        ·
          refine ⟨9389007736389906411540029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25037353963706417097440077 9389007736389906411540029)
          ·
            refine ⟨3520877901146214904327511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9389007736389906411540029 3520877901146214904327511)
            ·
              refine ⟨5281316851719322356491267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520877901146214904327511 5281316851719322356491267)
              ·
                refine ⟨7921975277578983534736901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281316851719322356491267 7921975277578983534736901)
                ·
                  refine ⟨1485370364546059412763169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7921975277578983534736901 1485370364546059412763169)
                  ·
                    refine ⟨1114027773409544559572377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1485370364546059412763169 1114027773409544559572377)
                    ·
                      refine ⟨835520830057158419679283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114027773409544559572377 835520830057158419679283)
                      ·
                        rfl

theorem cell23_1627171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_1627171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627171 prefixEnd_1627171 := by exact prefixLift 1627171
  have htrace : WordTrace (prefixWord ++ tailWord_1627171) baseStart_1627171 baseEnd_1627171 := by
    simpa [prefixWord, tailWord_1627171, baseEnd_1627171] using wordTrace_append hprefix tailTrace_1627171
  have hstable : (prefixWord ++ tailWord_1627171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627171).length < 2 ^ (prefixWord ++ tailWord_1627171).sum := by decide
  have hdescent : baseEnd_1627171 < baseStart_1627171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627188 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1627188 : Nat := 118140960795 + 1627188 * 2 ^ 59
def prefixEnd_1627188 : Nat := 4983230072969 + 3 ^ 40 * 1627188 * 2
def baseEnd_1627188 : Nat := 835529559228284853166705

theorem tailTrace_1627188 : CollatzResearch.WordTrace tailWord_1627188 prefixEnd_1627188 835529559228284853166705 := by
  unfold tailWord_1627188
  simp only [CollatzResearch.WordTrace]
  refine ⟨29674211014491626215317109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39565614685988834953756145 29674211014491626215317109)
  ·
    refine ⟨2781957282608589957685979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29674211014491626215317109 2781957282608589957685979)
    ·
      refine ⟨4172935923912884936528969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781957282608589957685979 4172935923912884936528969)
      ·
        refine ⟨3129701942934663702396727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4172935923912884936528969 3129701942934663702396727)
        ·
          refine ⟨4694552914401995553595091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129701942934663702396727 4694552914401995553595091)
          ·
            refine ⟨7041829371602993330392637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694552914401995553595091 7041829371602993330392637)
            ·
              refine ⟨2640686014351122498897239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7041829371602993330392637 2640686014351122498897239)
              ·
                refine ⟨3961029021526683748345859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640686014351122498897239 3961029021526683748345859)
                ·
                  refine ⟨5941543532290025622518789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961029021526683748345859 5941543532290025622518789)
                  ·
                    refine ⟨1114039412304379804222273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5941543532290025622518789 1114039412304379804222273)
                    ·
                      refine ⟨835529559228284853166705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114039412304379804222273 835529559228284853166705)
                      ·
                        rfl

theorem cell23_1627188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1627188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627188 prefixEnd_1627188 := by exact prefixLift 1627188
  have htrace : WordTrace (prefixWord ++ tailWord_1627188) baseStart_1627188 baseEnd_1627188 := by
    simpa [prefixWord, tailWord_1627188, baseEnd_1627188] using wordTrace_append hprefix tailTrace_1627188
  have hstable : (prefixWord ++ tailWord_1627188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627188).length < 2 ^ (prefixWord ++ tailWord_1627188).sum := by decide
  have hdescent : baseEnd_1627188 < baseStart_1627188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627207 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1627207 : Nat := 118140960795 + 1627207 * 2 ^ 59
def prefixEnd_1627207 : Nat := 4983230072969 + 3 ^ 40 * 1627207 * 2
def baseEnd_1627207 : Nat := 278513105120240092943039

theorem tailTrace_1627207 : CollatzResearch.WordTrace tailWord_1627207 prefixEnd_1627207 278513105120240092943039 := by
  unfold tailWord_1627207
  simp only [CollatzResearch.WordTrace]
  refine ⟨59349115015914418675575875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39566076677276279117050583 59349115015914418675575875)
  ·
    refine ⟨89023672523871628013363813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59349115015914418675575875 89023672523871628013363813)
    ·
      refine ⟨16691938598225930252505715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89023672523871628013363813 16691938598225930252505715)
      ·
        refine ⟨25037907897338895378758573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16691938598225930252505715 25037907897338895378758573)
        ·
          refine ⟨9389215461502085767034465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25037907897338895378758573 9389215461502085767034465)
          ·
            refine ⟨7041911596126564325275849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9389215461502085767034465 7041911596126564325275849)
            ·
              refine ⟨5281433697094923243956887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7041911596126564325275849 5281433697094923243956887)
              ·
                refine ⟨7922150545642384865935331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281433697094923243956887 7922150545642384865935331)
                ·
                  refine ⟨11883225818463577298902997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7922150545642384865935331 11883225818463577298902997)
                  ·
                    refine ⟨278513105120240092943039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11883225818463577298902997 278513105120240092943039)
                    ·
                      rfl

theorem cell23_1627207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1627207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627207 prefixEnd_1627207 := by exact prefixLift 1627207
  have htrace : WordTrace (prefixWord ++ tailWord_1627207) baseStart_1627207 baseEnd_1627207 := by
    simpa [prefixWord, tailWord_1627207, baseEnd_1627207] using wordTrace_append hprefix tailTrace_1627207
  have hstable : (prefixWord ++ tailWord_1627207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627207).length < 2 ^ (prefixWord ++ tailWord_1627207).sum := by decide
  have hdescent : baseEnd_1627207 < baseStart_1627207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627234 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1627234 : Nat := 118140960795 + 1627234 * 2 ^ 59
def prefixEnd_1627234 : Nat := 4983230072969 + 3 ^ 40 * 1627234 * 2
def baseEnd_1627234 : Nat := 835553179338391673191493

theorem tailTrace_1627234 : CollatzResearch.WordTrace tailWord_1627234 prefixEnd_1627234 835553179338391673191493 := by
  unfold tailWord_1627234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14837524946704150571702189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39566733191211068191205837 14837524946704150571702189)
  ·
    refine ⟨5564071855014056464388321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14837524946704150571702189 5564071855014056464388321)
    ·
      refine ⟨4173053891260542348291241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5564071855014056464388321 4173053891260542348291241)
      ·
        refine ⟨3129790418445406761218431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173053891260542348291241 3129790418445406761218431)
        ·
          refine ⟨4694685627668110141827647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129790418445406761218431 4694685627668110141827647)
          ·
            refine ⟨7042028441502165212741471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694685627668110141827647 7042028441502165212741471)
            ·
              refine ⟨10563042662253247819112207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042028441502165212741471 10563042662253247819112207)
              ·
                refine ⟨15844563993379871728668311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10563042662253247819112207 15844563993379871728668311)
                ·
                  refine ⟨23766845990069807593002467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15844563993379871728668311 23766845990069807593002467)
                  ·
                    refine ⟨35650268985104711389503701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23766845990069807593002467 35650268985104711389503701)
                    ·
                      refine ⟨835553179338391673191493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35650268985104711389503701 835553179338391673191493)
                      ·
                        rfl

theorem cell23_1627234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1627234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627234 prefixEnd_1627234 := by exact prefixLift 1627234
  have htrace : WordTrace (prefixWord ++ tailWord_1627234) baseStart_1627234 baseEnd_1627234 := by
    simpa [prefixWord, tailWord_1627234, baseEnd_1627234] using wordTrace_append hprefix tailTrace_1627234
  have hstable : (prefixWord ++ tailWord_1627234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627234).length < 2 ^ (prefixWord ++ tailWord_1627234).sum := by decide
  have hdescent : baseEnd_1627234 < baseStart_1627234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627244 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 6, 2]
def baseStart_1627244 : Nat := 118140960795 + 1627244 * 2 ^ 59
def prefixEnd_1627244 : Nat := 4983230072969 + 3 ^ 40 * 1627244 * 2
def baseEnd_1627244 : Nat := 835558314144936634066447

theorem tailTrace_1627244 : CollatzResearch.WordTrace tailWord_1627244 prefixEnd_1627244 835558314144936634066447 := by
  unfold tailWord_1627244
  simp only [CollatzResearch.WordTrace]
  refine ⟨29675232258390186997336393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39566976344520249329781857 29675232258390186997336393)
  ·
    refine ⟨22256424193792640248002295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29675232258390186997336393 22256424193792640248002295)
    ·
      refine ⟨33384636290688960372003443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22256424193792640248002295 33384636290688960372003443)
      ·
        refine ⟨50076954436033440558005165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33384636290688960372003443 50076954436033440558005165)
        ·
          refine ⟨18778857913512540209251937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50076954436033440558005165 18778857913512540209251937)
          ·
            refine ⟨14084143435134405156938953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18778857913512540209251937 14084143435134405156938953)
            ·
              refine ⟨10563107576350803867704215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14084143435134405156938953 10563107576350803867704215)
              ·
                refine ⟨15844661364526205801556323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10563107576350803867704215 15844661364526205801556323)
                ·
                  refine ⟨23766992046789308702334485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15844661364526205801556323 23766992046789308702334485)
                  ·
                    refine ⟨1114077752193248845421929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23766992046789308702334485 1114077752193248845421929)
                    ·
                      refine ⟨835558314144936634066447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114077752193248845421929 835558314144936634066447)
                      ·
                        rfl

theorem cell23_1627244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_1627244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627244 prefixEnd_1627244 := by exact prefixLift 1627244
  have htrace : WordTrace (prefixWord ++ tailWord_1627244) baseStart_1627244 baseEnd_1627244 := by
    simpa [prefixWord, tailWord_1627244, baseEnd_1627244] using wordTrace_append hprefix tailTrace_1627244
  have hstable : (prefixWord ++ tailWord_1627244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627244).length < 2 ^ (prefixWord ++ tailWord_1627244).sum := by decide
  have hdescent : baseEnd_1627244 < baseStart_1627244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627264 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_1627264 : Nat := 118140960795 + 1627264 * 2 ^ 59
def prefixEnd_1627264 : Nat := 4983230072969 + 3 ^ 40 * 1627264 * 2
def baseEnd_1627264 : Nat := 835568583758026555816355

theorem tailTrace_1627264 : CollatzResearch.WordTrace tailWord_1627264 prefixEnd_1627264 835568583758026555816355 := by
  unfold tailWord_1627264
  simp only [CollatzResearch.WordTrace]
  refine ⟨29675596988353958705200423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39567462651138611606933897 29675596988353958705200423)
  ·
    refine ⟨44513395482530938057800635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29675596988353958705200423 44513395482530938057800635)
    ·
      refine ⟨66770093223796407086700953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44513395482530938057800635 66770093223796407086700953)
      ·
        refine ⟨50077569917847305315025715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66770093223796407086700953 50077569917847305315025715)
        ·
          refine ⟨75116354876770957972538573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50077569917847305315025715 75116354876770957972538573)
          ·
            refine ⟨28168633078789109239701965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75116354876770957972538573 28168633078789109239701965)
            ·
              refine ⟨10563237404545915964888237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28168633078789109239701965 10563237404545915964888237)
              ·
                refine ⟨3961214026704718486833089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10563237404545915964888237 3961214026704718486833089)
                ·
                  refine ⟨2970910520028538865124817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961214026704718486833089 2970910520028538865124817)
                  ·
                    refine ⟨2228182890021404148843613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2970910520028538865124817 2228182890021404148843613)
                    ·
                      refine ⟨835568583758026555816355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2228182890021404148843613 835568583758026555816355)
                      ·
                        rfl

theorem cell23_1627264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_1627264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627264 prefixEnd_1627264 := by exact prefixLift 1627264
  have htrace : WordTrace (prefixWord ++ tailWord_1627264) baseStart_1627264 baseEnd_1627264 := by
    simpa [prefixWord, tailWord_1627264, baseEnd_1627264] using wordTrace_append hprefix tailTrace_1627264
  have hstable : (prefixWord ++ tailWord_1627264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627264).length < 2 ^ (prefixWord ++ tailWord_1627264).sum := by decide
  have hdescent : baseEnd_1627264 < baseStart_1627264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627271 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 1, 4]
def baseStart_1627271 : Nat := 118140960795 + 1627271 * 2 ^ 59
def prefixEnd_1627271 : Nat := 4983230072969 + 3 ^ 40 * 1627271 * 2
def baseEnd_1627271 : Nat := 278524059374202676142941

theorem tailTrace_1627271 : CollatzResearch.WordTrace tailWord_1627271 prefixEnd_1627271 278524059374202676142941 := by
  unfold tailWord_1627271
  simp only [CollatzResearch.WordTrace]
  refine ⟨59351449287682557605905667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39567632858455038403937111 59351449287682557605905667)
  ·
    refine ⟨89027173931523836408858501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59351449287682557605905667 89027173931523836408858501)
    ·
      refine ⟨16692595112160719326660969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89027173931523836408858501 16692595112160719326660969)
      ·
        refine ⟨12519446334120539494995727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16692595112160719326660969 12519446334120539494995727)
        ·
          refine ⟨18779169501180809242493591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12519446334120539494995727 18779169501180809242493591)
          ·
            refine ⟨28168754251771213863740387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18779169501180809242493591 28168754251771213863740387)
            ·
              refine ⟨42253131377656820795610581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28168754251771213863740387 42253131377656820795610581)
              ·
                refine ⟨990307766663831737397123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42253131377656820795610581 990307766663831737397123)
                ·
                  refine ⟨1485461649995747606095685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990307766663831737397123 1485461649995747606095685)
                  ·
                    refine ⟨278524059374202676142941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485461649995747606095685 278524059374202676142941)
                    ·
                      rfl

theorem cell23_1627271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_1627271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627271 prefixEnd_1627271 := by exact prefixLift 1627271
  have htrace : WordTrace (prefixWord ++ tailWord_1627271) baseStart_1627271 baseEnd_1627271 := by
    simpa [prefixWord, tailWord_1627271, baseEnd_1627271] using wordTrace_append hprefix tailTrace_1627271
  have hstable : (prefixWord ++ tailWord_1627271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627271).length < 2 ^ (prefixWord ++ tailWord_1627271).sum := by decide
  have hdescent : baseEnd_1627271 < baseStart_1627271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627288 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 1, 4]
def baseStart_1627288 : Nat := 118140960795 + 1627288 * 2 ^ 59
def prefixEnd_1627288 : Nat := 4983230072969 + 3 ^ 40 * 1627288 * 2
def baseEnd_1627288 : Nat := 278526969097911487305415

theorem tailTrace_1627288 : CollatzResearch.WordTrace tailWord_1627288 prefixEnd_1627288 278526969097911487305415 := by
  unfold tailWord_1627288
  simp only [CollatzResearch.WordTrace]
  refine ⟨29676034664310484754637259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39568046219080646339516345 29676034664310484754637259)
  ·
    refine ⟨44514051996465727131955889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29676034664310484754637259 44514051996465727131955889)
    ·
      refine ⟨33385538997349295348966917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44514051996465727131955889 33385538997349295348966917)
      ·
        refine ⟨6259788562002992877931297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33385538997349295348966917 6259788562002992877931297)
        ·
          refine ⟨4694841421502244658448473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259788562002992877931297 4694841421502244658448473)
          ·
            refine ⟨3521131066126683493836355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4694841421502244658448473 3521131066126683493836355)
            ·
              refine ⟨5281696599190025240754533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521131066126683493836355 5281696599190025240754533)
              ·
                refine ⟨990318112348129732641475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5281696599190025240754533 990318112348129732641475)
                ·
                  refine ⟨1485477168522194598962213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990318112348129732641475 1485477168522194598962213)
                  ·
                    refine ⟨278526969097911487305415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485477168522194598962213 278526969097911487305415)
                    ·
                      rfl

theorem cell23_1627288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_1627288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627288 prefixEnd_1627288 := by exact prefixLift 1627288
  have htrace : WordTrace (prefixWord ++ tailWord_1627288) baseStart_1627288 baseEnd_1627288 := by
    simpa [prefixWord, tailWord_1627288, baseEnd_1627288] using wordTrace_append hprefix tailTrace_1627288
  have hstable : (prefixWord ++ tailWord_1627288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627288).length < 2 ^ (prefixWord ++ tailWord_1627288).sum := by decide
  have hdescent : baseEnd_1627288 < baseStart_1627288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627314 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_1627314 : Nat := 118140960795 + 1627314 * 2 ^ 59
def prefixEnd_1627314 : Nat := 4983230072969 + 3 ^ 40 * 1627314 * 2
def baseEnd_1627314 : Nat := 278531419263583786730375

theorem tailTrace_1627314 : CollatzResearch.WordTrace tailWord_1627314 prefixEnd_1627314 278531419263583786730375 := by
  unfold tailWord_1627314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838254406631693987430249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39568678417684517299813997 14838254406631693987430249)
  ·
    refine ⟨11128690804973770490572687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14838254406631693987430249 11128690804973770490572687)
    ·
      refine ⟨16693036207460655735859031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11128690804973770490572687 16693036207460655735859031)
      ·
        refine ⟨25039554311190983603788547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16693036207460655735859031 25039554311190983603788547)
        ·
          refine ⟨37559331466786475405682821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25039554311190983603788547 37559331466786475405682821)
          ·
            refine ⟨7042374650022464138565529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37559331466786475405682821 7042374650022464138565529)
            ·
              refine ⟨5281780987516848103924147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7042374650022464138565529 5281780987516848103924147)
              ·
                refine ⟨7922671481275272155886221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281780987516848103924147 7922671481275272155886221)
                ·
                  refine ⟨2971001805478227058457333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7922671481275272155886221 2971001805478227058457333)
                  ·
                    refine ⟨278531419263583786730375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2971001805478227058457333 278531419263583786730375)
                    ·
                      rfl

theorem cell23_1627314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_1627314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627314 prefixEnd_1627314 := by exact prefixLift 1627314
  have htrace : WordTrace (prefixWord ++ tailWord_1627314) baseStart_1627314 baseEnd_1627314 := by
    simpa [prefixWord, tailWord_1627314, baseEnd_1627314] using wordTrace_append hprefix tailTrace_1627314
  have hstable : (prefixWord ++ tailWord_1627314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627314).length < 2 ^ (prefixWord ++ tailWord_1627314).sum := by decide
  have hdescent : baseEnd_1627314 < baseStart_1627314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627321 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 1, 5, 2]
def baseStart_1627321 : Nat := 118140960795 + 1627321 * 2 ^ 59
def prefixEnd_1627321 : Nat := 4983230072969 + 3 ^ 40 * 1627321 * 2
def baseEnd_1627321 : Nat := 835597852155332832803593

theorem tailTrace_1627321 : CollatzResearch.WordTrace tailWord_1627321 prefixEnd_1627321 835597852155332832803593 := by
  unfold tailWord_1627321
  simp only [CollatzResearch.WordTrace]
  refine ⟨59353272937501416145225817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39568848625000944096817211 59353272937501416145225817)
  ·
    refine ⟨44514954703126062108919363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59353272937501416145225817 44514954703126062108919363)
    ·
      refine ⟨66772432054689093163379045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44514954703126062108919363 66772432054689093163379045)
      ·
        refine ⟨12519831010254204968133571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66772432054689093163379045 12519831010254204968133571)
        ·
          refine ⟨18779746515381307452200357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12519831010254204968133571 18779746515381307452200357)
          ·
            refine ⟨3521202471633995147287567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18779746515381307452200357 3521202471633995147287567)
            ·
              refine ⟨5281803707450992720931351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521202471633995147287567 5281803707450992720931351)
              ·
                refine ⟨7922705561176489081397027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281803707450992720931351 7922705561176489081397027)
                ·
                  refine ⟨11884058341764733622095541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7922705561176489081397027 11884058341764733622095541)
                  ·
                    refine ⟨1114130469540443777071457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11884058341764733622095541 1114130469540443777071457)
                    ·
                      refine ⟨835597852155332832803593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114130469540443777071457 835597852155332832803593)
                      ·
                        rfl

theorem cell23_1627321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_1627321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627321 prefixEnd_1627321 := by exact prefixLift 1627321
  have htrace : WordTrace (prefixWord ++ tailWord_1627321) baseStart_1627321 baseEnd_1627321 := by
    simpa [prefixWord, tailWord_1627321, baseEnd_1627321] using wordTrace_append hprefix tailTrace_1627321
  have hstable : (prefixWord ++ tailWord_1627321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627321).length < 2 ^ (prefixWord ++ tailWord_1627321).sum := by decide
  have hdescent : baseEnd_1627321 < baseStart_1627321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627347 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_1627347 : Nat := 118140960795 + 1627347 * 2 ^ 59
def prefixEnd_1627347 : Nat := 4983230072969 + 3 ^ 40 * 1627347 * 2
def baseEnd_1627347 : Nat := 835611202652349731078473

theorem tailTrace_1627347 : CollatzResearch.WordTrace tailWord_1627347 prefixEnd_1627347 835611202652349731078473 := by
  unfold tailWord_1627347
  simp only [CollatzResearch.WordTrace]
  refine ⟨59354221235407222585672295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39569480823604815057114863 59354221235407222585672295)
  ·
    refine ⟨89031331853110833878508443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59354221235407222585672295 89031331853110833878508443)
    ·
      refine ⟨133546997779666250817762665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89031331853110833878508443 133546997779666250817762665)
      ·
        refine ⟨100160248334749688113321999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133546997779666250817762665 100160248334749688113321999)
        ·
          refine ⟨150240372502124532169982999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100160248334749688113321999 150240372502124532169982999)
          ·
            refine ⟨225360558753186798254974499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150240372502124532169982999 225360558753186798254974499)
            ·
              refine ⟨338040838129780197382461749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225360558753186798254974499 338040838129780197382461749)
              ·
                refine ⟨31691328574666893504605789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338040838129780197382461749 31691328574666893504605789)
                ·
                  refine ⟨11884248215500085064227171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31691328574666893504605789 11884248215500085064227171)
                  ·
                    refine ⟨17826372323250127596340757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11884248215500085064227171 17826372323250127596340757)
                    ·
                      refine ⟨835611202652349731078473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17826372323250127596340757 835611202652349731078473)
                      ·
                        rfl

theorem cell23_1627347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_1627347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627347 prefixEnd_1627347 := by exact prefixLift 1627347
  have htrace : WordTrace (prefixWord ++ tailWord_1627347) baseStart_1627347 baseEnd_1627347 := by
    simpa [prefixWord, tailWord_1627347, baseEnd_1627347] using wordTrace_append hprefix tailTrace_1627347
  have hstable : (prefixWord ++ tailWord_1627347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627347).length < 2 ^ (prefixWord ++ tailWord_1627347).sum := by decide
  have hdescent : baseEnd_1627347 < baseStart_1627347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627361 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 1, 6]
def baseStart_1627361 : Nat := 118140960795 + 1627361 * 2 ^ 59
def prefixEnd_1627361 : Nat := 4983230072969 + 3 ^ 40 * 1627361 * 2
def baseEnd_1627361 : Nat := 278539463793837558767803

theorem tailTrace_1627361 : CollatzResearch.WordTrace tailWord_1627361 prefixEnd_1627361 278539463793837558767803 := by
  unfold tailWord_1627361
  simp only [CollatzResearch.WordTrace]
  refine ⟨59354731857356502976681937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39569821238237668651121291 59354731857356502976681937)
  ·
    refine ⟨44516048893017377232511453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59354731857356502976681937 44516048893017377232511453)
    ·
      refine ⟨16693518334881516462191795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44516048893017377232511453 16693518334881516462191795)
      ·
        refine ⟨25040277502322274693287693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16693518334881516462191795 25040277502322274693287693)
        ·
          refine ⟨9390104063370853009982885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25040277502322274693287693 9390104063370853009982885)
          ·
            refine ⟨1760644511882034939371791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9390104063370853009982885 1760644511882034939371791)
            ·
              refine ⟨2640966767823052409057687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760644511882034939371791 2640966767823052409057687)
              ·
                refine ⟨3961450151734578613586531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640966767823052409057687 3961450151734578613586531)
                ·
                  refine ⟨5942175227601867920379797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961450151734578613586531 5942175227601867920379797)
                  ·
                    refine ⟨278539463793837558767803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5942175227601867920379797 278539463793837558767803)
                    ·
                      rfl

theorem cell23_1627361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_1627361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627361 prefixEnd_1627361 := by exact prefixLift 1627361
  have htrace : WordTrace (prefixWord ++ tailWord_1627361) baseStart_1627361 baseEnd_1627361 := by
    simpa [prefixWord, tailWord_1627361, baseEnd_1627361] using wordTrace_append hprefix tailTrace_1627361
  have hstable : (prefixWord ++ tailWord_1627361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627361).length < 2 ^ (prefixWord ++ tailWord_1627361).sum := by decide
  have hdescent : baseEnd_1627361 < baseStart_1627361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627368 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1627368 : Nat := 118140960795 + 1627368 * 2 ^ 59
def prefixEnd_1627368 : Nat := 4983230072969 + 3 ^ 40 * 1627368 * 2
def baseEnd_1627368 : Nat := 835621985746094148915877

theorem tailTrace_1627368 : CollatzResearch.WordTrace tailWord_1627368 prefixEnd_1627368 835621985746094148915877 := by
  unfold tailWord_1627368
  simp only [CollatzResearch.WordTrace]
  refine ⟨29677493584165571586093379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39569991445554095448124505 29677493584165571586093379)
  ·
    refine ⟨44516240376248357379140069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29677493584165571586093379 44516240376248357379140069)
    ·
      refine ⟨8346795070546567008588763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44516240376248357379140069 8346795070546567008588763)
      ·
        refine ⟨12520192605819850512883145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8346795070546567008588763 12520192605819850512883145)
        ·
          refine ⟨9390144454364887884662359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12520192605819850512883145 9390144454364887884662359)
          ·
            refine ⟨14085216681547331826993539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9390144454364887884662359 14085216681547331826993539)
            ·
              refine ⟨21127825022320997740490309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14085216681547331826993539 21127825022320997740490309)
              ·
                refine ⟨3961467191685187076341933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21127825022320997740490309 3961467191685187076341933)
                ·
                  refine ⟨1485550196881945153628225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3961467191685187076341933 1485550196881945153628225)
                  ·
                    refine ⟨1114162647661458865221169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1485550196881945153628225 1114162647661458865221169)
                    ·
                      refine ⟨835621985746094148915877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114162647661458865221169 835621985746094148915877)
                      ·
                        rfl

theorem cell23_1627368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1627368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627368 prefixEnd_1627368 := by exact prefixLift 1627368
  have htrace : WordTrace (prefixWord ++ tailWord_1627368) baseStart_1627368 baseEnd_1627368 := by
    simpa [prefixWord, tailWord_1627368, baseEnd_1627368] using wordTrace_append hprefix tailTrace_1627368
  have hstable : (prefixWord ++ tailWord_1627368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627368).length < 2 ^ (prefixWord ++ tailWord_1627368).sum := by decide
  have hdescent : baseEnd_1627368 < baseStart_1627368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627371 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 3]
def baseStart_1627371 : Nat := 118140960795 + 1627371 * 2 ^ 59
def prefixEnd_1627371 : Nat := 4983230072969 + 3 ^ 40 * 1627371 * 2
def baseEnd_1627371 : Nat := 835623526188057637178363

theorem tailTrace_1627371 : CollatzResearch.WordTrace tailWord_1627371 prefixEnd_1627371 835623526188057637178363 := by
  unfold tailWord_1627371
  simp only [CollatzResearch.WordTrace]
  refine ⟨59355096587320274684545967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39570064391546849789697311 59355096587320274684545967)
  ·
    refine ⟨89032644880980412026818951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59355096587320274684545967 89032644880980412026818951)
    ·
      refine ⟨133548967321470618040228427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89032644880980412026818951 133548967321470618040228427)
      ·
        refine ⟨200323450982205927060342641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133548967321470618040228427 200323450982205927060342641)
        ·
          refine ⟨150242588236654445295256981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200323450982205927060342641 150242588236654445295256981)
          ·
            refine ⟨7042621323593177123215171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150242588236654445295256981 7042621323593177123215171)
            ·
              refine ⟨10563931985389765684822757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042621323593177123215171 10563931985389765684822757)
              ·
                refine ⟨1980737247260581065904267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10563931985389765684822757 1980737247260581065904267)
                ·
                  refine ⟨2971105870890871598856401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980737247260581065904267 2971105870890871598856401)
                  ·
                    refine ⟨2228329403168153699142301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2971105870890871598856401 2228329403168153699142301)
                    ·
                      refine ⟨835623526188057637178363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2228329403168153699142301 835623526188057637178363)
                      ·
                        rfl

theorem cell23_1627371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 3].length) (baseStart_1627371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627371 prefixEnd_1627371 := by exact prefixLift 1627371
  have htrace : WordTrace (prefixWord ++ tailWord_1627371) baseStart_1627371 baseEnd_1627371 := by
    simpa [prefixWord, tailWord_1627371, baseEnd_1627371] using wordTrace_append hprefix tailTrace_1627371
  have hstable : (prefixWord ++ tailWord_1627371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627371).length < 2 ^ (prefixWord ++ tailWord_1627371).sum := by decide
  have hdescent : baseEnd_1627371 < baseStart_1627371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627401 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 3]
def baseStart_1627401 : Nat := 118140960795 + 1627401 * 2 ^ 59
def prefixEnd_1627401 : Nat := 4983230072969 + 3 ^ 40 * 1627401 * 2
def baseEnd_1627401 : Nat := 835638930607692519803225

theorem tailTrace_1627401 : CollatzResearch.WordTrace tailWord_1627401 prefixEnd_1627401 835638930607692519803225 := by
  unfold tailWord_1627401
  simp only [CollatzResearch.WordTrace]
  refine ⟨59356190777211589808138057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39570793851474393205425371 59356190777211589808138057)
  ·
    refine ⟨44517143082908692356103543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59356190777211589808138057 44517143082908692356103543)
    ·
      refine ⟨66775714624363038534155315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44517143082908692356103543 66775714624363038534155315)
      ·
        refine ⟨100163571936544557801232973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66775714624363038534155315 100163571936544557801232973)
        ·
          refine ⟨37561339476204209175462365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100163571936544557801232973 37561339476204209175462365)
          ·
            refine ⟨14085502303576578440798387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37561339476204209175462365 14085502303576578440798387)
            ·
              refine ⟨21128253455364867661197581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14085502303576578440798387 21128253455364867661197581)
              ·
                refine ⟨7923095045761825372949093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21128253455364867661197581 7923095045761825372949093)
                ·
                  refine ⟨1485580321080342257427955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7923095045761825372949093 1485580321080342257427955)
                  ·
                    refine ⟨2228370481620513386141933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485580321080342257427955 2228370481620513386141933)
                    ·
                      refine ⟨835638930607692519803225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2228370481620513386141933 835638930607692519803225)
                      ·
                        rfl

theorem cell23_1627401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_1627401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627401 prefixEnd_1627401 := by exact prefixLift 1627401
  have htrace : WordTrace (prefixWord ++ tailWord_1627401) baseStart_1627401 baseEnd_1627401 := by
    simpa [prefixWord, tailWord_1627401, baseEnd_1627401] using wordTrace_append hprefix tailTrace_1627401
  have hstable : (prefixWord ++ tailWord_1627401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627401).length < 2 ^ (prefixWord ++ tailWord_1627401).sum := by decide
  have hdescent : baseEnd_1627401 < baseStart_1627401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627428 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_1627428 : Nat := 118140960795 + 1627428 * 2 ^ 59
def prefixEnd_1627428 : Nat := 4983230072969 + 3 ^ 40 * 1627428 * 2
def baseEnd_1627428 : Nat := 835652794585363914165601

theorem tailTrace_1627428 : CollatzResearch.WordTrace tailWord_1627428 prefixEnd_1627428 835652794585363914165601 := by
  unfold tailWord_1627428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29678587774056886709685469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39571450365409182279580625 29678587774056886709685469)
  ·
    refine ⟨11129470415271332516132051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29678587774056886709685469 11129470415271332516132051)
    ·
      refine ⟨16694205622906998774198077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129470415271332516132051 16694205622906998774198077)
      ·
        refine ⟨6260327108590124540324279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16694205622906998774198077 6260327108590124540324279)
        ·
          refine ⟨9390490662885186810486419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6260327108590124540324279 9390490662885186810486419)
          ·
            refine ⟨14085735994327780215729629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9390490662885186810486419 14085735994327780215729629)
            ·
              refine ⟨5282150997872917580898611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14085735994327780215729629 5282150997872917580898611)
              ·
                refine ⟨7923226496809376371347917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282150997872917580898611 7923226496809376371347917)
                ·
                  refine ⟨2971209936303516139255469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7923226496809376371347917 2971209936303516139255469)
                  ·
                    refine ⟨1114203726113818552220801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971209936303516139255469 1114203726113818552220801)
                    ·
                      refine ⟨835652794585363914165601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114203726113818552220801 835652794585363914165601)
                      ·
                        rfl

theorem cell23_1627428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_1627428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627428 prefixEnd_1627428 := by exact prefixLift 1627428
  have htrace : WordTrace (prefixWord ++ tailWord_1627428) baseStart_1627428 baseEnd_1627428 := by
    simpa [prefixWord, tailWord_1627428, baseEnd_1627428] using wordTrace_append hprefix tailTrace_1627428
  have hstable : (prefixWord ++ tailWord_1627428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627428).length < 2 ^ (prefixWord ++ tailWord_1627428).sum := by decide
  have hdescent : baseEnd_1627428 < baseStart_1627428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627453 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1627453 : Nat := 118140960795 + 1627453 * 2 ^ 59
def prefixEnd_1627453 : Nat := 4983230072969 + 3 ^ 40 * 1627453 * 2
def baseEnd_1627453 : Nat := 835665631601726316352987

theorem tailTrace_1627453 : CollatzResearch.WordTrace tailWord_1627453 prefixEnd_1627453 835665631601726316352987 := by
  unfold tailWord_1627453
  simp only [CollatzResearch.WordTrace]
  refine ⟨59358087373023202689031013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39572058248682135126020675 59358087373023202689031013)
  ·
    refine ⟨11129641382441850504193315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59358087373023202689031013 11129641382441850504193315)
    ·
      refine ⟨16694462073662775756289973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129641382441850504193315 16694462073662775756289973)
      ·
        refine ⟨1565105819405885227152185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16694462073662775756289973 1565105819405885227152185)
        ·
          refine ⟨1173829364554413920364139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565105819405885227152185 1173829364554413920364139)
          ·
            refine ⟨1760744046831620880546209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173829364554413920364139 1760744046831620880546209)
            ·
              refine ⟨1320558035123715660409657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760744046831620880546209 1320558035123715660409657)
              ·
                refine ⟨990418526342786745307243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320558035123715660409657 990418526342786745307243)
                ·
                  refine ⟨1485627789514180117960865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990418526342786745307243 1485627789514180117960865)
                  ·
                    refine ⟨1114220842135635088470649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1485627789514180117960865 1114220842135635088470649)
                    ·
                      refine ⟨835665631601726316352987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114220842135635088470649 835665631601726316352987)
                      ·
                        rfl

theorem cell23_1627453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1627453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627453 prefixEnd_1627453 := by exact prefixLift 1627453
  have htrace : WordTrace (prefixWord ++ tailWord_1627453) baseStart_1627453 baseEnd_1627453 := by
    simpa [prefixWord, tailWord_1627453, baseEnd_1627453] using wordTrace_append hprefix tailTrace_1627453
  have hstable : (prefixWord ++ tailWord_1627453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627453).length < 2 ^ (prefixWord ++ tailWord_1627453).sum := by decide
  have hdescent : baseEnd_1627453 < baseStart_1627453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627464 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 7]
def baseStart_1627464 : Nat := 118140960795 + 1627464 * 2 ^ 59
def prefixEnd_1627464 : Nat := 4983230072969 + 3 ^ 40 * 1627464 * 2
def baseEnd_1627464 : Nat := 92852364432102863701715

theorem tailTrace_1627464 : CollatzResearch.WordTrace tailWord_1627464 prefixEnd_1627464 92852364432102863701715 := by
  unfold tailWord_1627464
  simp only [CollatzResearch.WordTrace]
  refine ⟨29679244287991675783840723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39572325717322234378454297 29679244287991675783840723)
  ·
    refine ⟨44518866431987513675761085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29679244287991675783840723 44518866431987513675761085)
    ·
      refine ⟨16694574911995317628410407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44518866431987513675761085 16694574911995317628410407)
      ·
        refine ⟨25041862367992976442615611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16694574911995317628410407 25041862367992976442615611)
        ·
          refine ⟨37562793551989464663923417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25041862367992976442615611 37562793551989464663923417)
          ·
            refine ⟨28172095163992098497942563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37562793551989464663923417 28172095163992098497942563)
            ·
              refine ⟨42258142745988147746913845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28172095163992098497942563 42258142745988147746913845)
              ·
                refine ⟨3961700882436388851273173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42258142745988147746913845 3961700882436388851273173)
                ·
                  refine ⟨92852364432102863701715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3961700882436388851273173 92852364432102863701715)
                  ·
                    rfl

theorem cell23_1627464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_1627464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627464 prefixEnd_1627464 := by exact prefixLift 1627464
  have htrace : WordTrace (prefixWord ++ tailWord_1627464) baseStart_1627464 baseEnd_1627464 := by
    simpa [prefixWord, tailWord_1627464, baseEnd_1627464] using wordTrace_append hprefix tailTrace_1627464
  have hstable : (prefixWord ++ tailWord_1627464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627464).length < 2 ^ (prefixWord ++ tailWord_1627464).sum := by decide
  have hdescent : baseEnd_1627464 < baseStart_1627464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627509 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1627509 : Nat := 118140960795 + 1627509 * 2 ^ 59
def prefixEnd_1627509 : Nat := 4983230072969 + 3 ^ 40 * 1627509 * 2
def baseEnd_1627509 : Nat := 835694386518378097252729

theorem tailTrace_1627509 : CollatzResearch.WordTrace tailWord_1627509 prefixEnd_1627509 835694386518378097252729 := by
  unfold tailWord_1627509
  simp only [CollatzResearch.WordTrace]
  refine ⟨59360129860820324253069581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39573419907213549502046387 59360129860820324253069581)
  ·
    refine ⟨22260048697807621594901093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59360129860820324253069581 22260048697807621594901093)
    ·
      refine ⟨4173759130838929049043955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22260048697807621594901093 4173759130838929049043955)
      ·
        refine ⟨6260638696258393573565933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4173759130838929049043955 6260638696258393573565933)
        ·
          refine ⟨2347739511096897590087225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6260638696258393573565933 2347739511096897590087225)
          ·
            refine ⟨1760804633322673192565419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2347739511096897590087225 1760804633322673192565419)
            ·
              refine ⟨2641206949984009788848129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760804633322673192565419 2641206949984009788848129)
              ·
                refine ⟨1980905212488007341636097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641206949984009788848129 1980905212488007341636097)
                ·
                  refine ⟨1485678909366005506227073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1980905212488007341636097 1485678909366005506227073)
                  ·
                    refine ⟨1114259182024504129670305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1485678909366005506227073 1114259182024504129670305)
                    ·
                      refine ⟨835694386518378097252729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114259182024504129670305 835694386518378097252729)
                      ·
                        rfl

theorem cell23_1627509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1627509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627509 prefixEnd_1627509 := by exact prefixLift 1627509
  have htrace : WordTrace (prefixWord ++ tailWord_1627509) baseStart_1627509 baseEnd_1627509 := by
    simpa [prefixWord, tailWord_1627509, baseEnd_1627509] using wordTrace_append hprefix tailTrace_1627509
  have hstable : (prefixWord ++ tailWord_1627509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627509).length < 2 ^ (prefixWord ++ tailWord_1627509).sum := by decide
  have hdescent : baseEnd_1627509 < baseStart_1627509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627565 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1627565 : Nat := 118140960795 + 1627565 * 2 ^ 59
def prefixEnd_1627565 : Nat := 4983230072969 + 3 ^ 40 * 1627565 * 2
def baseEnd_1627565 : Nat := 835723141435029878152471

theorem tailTrace_1627565 : CollatzResearch.WordTrace tailWord_1627565 prefixEnd_1627565 835723141435029878152471 := by
  unfold tailWord_1627565
  simp only [CollatzResearch.WordTrace]
  refine ⟨59362172348617445817108149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39574781565744963878072099 59362172348617445817108149)
  ·
    refine ⟨5565203657682885545353889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59362172348617445817108149 5565203657682885545353889)
    ·
      refine ⟨4173902743262164159015417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5565203657682885545353889 4173902743262164159015417)
      ·
        refine ⟨3130427057446623119261563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173902743262164159015417 3130427057446623119261563)
        ·
          refine ⟨4695640586169934678892345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130427057446623119261563 4695640586169934678892345)
          ·
            refine ⟨3521730439627451009169259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4695640586169934678892345 3521730439627451009169259)
            ·
              refine ⟨5282595659441176513753889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521730439627451009169259 5282595659441176513753889)
              ·
                refine ⟨3961946744580882385315417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5282595659441176513753889 3961946744580882385315417)
                ·
                  refine ⟨2971460058435661788986563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961946744580882385315417 2971460058435661788986563)
                  ·
                    refine ⟨4457190087653492683479845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2971460058435661788986563 4457190087653492683479845)
                    ·
                      refine ⟨835723141435029878152471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4457190087653492683479845 835723141435029878152471)
                      ·
                        rfl

theorem cell23_1627565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1627565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627565 prefixEnd_1627565 := by exact prefixLift 1627565
  have htrace : WordTrace (prefixWord ++ tailWord_1627565) baseStart_1627565 baseEnd_1627565 := by
    simpa [prefixWord, tailWord_1627565, baseEnd_1627565] using wordTrace_append hprefix tailTrace_1627565
  have hstable : (prefixWord ++ tailWord_1627565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627565).length < 2 ^ (prefixWord ++ tailWord_1627565).sum := by decide
  have hdescent : baseEnd_1627565 < baseStart_1627565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627608 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 1, 5, 2]
def baseStart_1627608 : Nat := 118140960795 + 1627608 * 2 ^ 59
def prefixEnd_1627608 : Nat := 4983230072969 + 3 ^ 40 * 1627608 * 2
def baseEnd_1627608 : Nat := 835745221103173209914773

theorem tailTrace_1627608 : CollatzResearch.WordTrace tailWord_1627608 prefixEnd_1627608 835745221103173209914773 := by
  unfold tailWord_1627608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29681870343730832080461739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39575827124974442773948985 29681870343730832080461739)
  ·
    refine ⟨44522805515596248120692609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29681870343730832080461739 44522805515596248120692609)
    ·
      refine ⟨33392104136697186090519457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44522805515596248120692609 33392104136697186090519457)
      ·
        refine ⟨25044078102522889567889593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33392104136697186090519457 25044078102522889567889593)
        ·
          refine ⟨18783058576892167175917195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25044078102522889567889593 18783058576892167175917195)
          ·
            refine ⟨28174587865338250763875793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18783058576892167175917195 28174587865338250763875793)
            ·
              refine ⟨21130940899003688072906845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28174587865338250763875793 21130940899003688072906845)
              ·
                refine ⟨7924102837126383027340067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21130940899003688072906845 7924102837126383027340067)
                ·
                  refine ⟨11886154255689574541010101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7924102837126383027340067 11886154255689574541010101)
                  ·
                    refine ⟨1114326961470897613219697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11886154255689574541010101 1114326961470897613219697)
                    ·
                      refine ⟨835745221103173209914773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114326961470897613219697 835745221103173209914773)
                      ·
                        rfl

theorem cell23_1627608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_1627608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627608 prefixEnd_1627608 := by exact prefixLift 1627608
  have htrace : WordTrace (prefixWord ++ tailWord_1627608) baseStart_1627608 baseEnd_1627608 := by
    simpa [prefixWord, tailWord_1627608, baseEnd_1627608] using wordTrace_append hprefix tailTrace_1627608
  have hstable : (prefixWord ++ tailWord_1627608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627608).length < 2 ^ (prefixWord ++ tailWord_1627608).sum := by decide
  have hdescent : baseEnd_1627608 < baseStart_1627608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627626 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1627626 : Nat := 118140960795 + 1627626 * 2 ^ 59
def prefixEnd_1627626 : Nat := 4983230072969 + 3 ^ 40 * 1627626 * 2
def baseEnd_1627626 : Nat := 278584821251651379829897

theorem tailTrace_1627626 : CollatzResearch.WordTrace tailWord_1627626 prefixEnd_1627626 278584821251651379829897 := by
  unfold tailWord_1627626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841099300349113308769683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39576264800930968823385821 14841099300349113308769683)
  ·
    refine ⟨22261648950523669963154525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841099300349113308769683 22261648950523669963154525)
    ·
      refine ⟨8348118356446376236182947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22261648950523669963154525 8348118356446376236182947)
      ·
        refine ⟨12522177534669564354274421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348118356446376236182947 12522177534669564354274421)
        ·
          refine ⟨1173954143875271658213227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12522177534669564354274421 1173954143875271658213227)
          ·
            refine ⟨1760931215812907487319841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173954143875271658213227 1760931215812907487319841)
            ·
              refine ⟨1320698411859680615489881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760931215812907487319841 1320698411859680615489881)
              ·
                refine ⟨990523808894760461617411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320698411859680615489881 990523808894760461617411)
                ·
                  refine ⟨1485785713342140692426117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990523808894760461617411 1485785713342140692426117)
                  ·
                    refine ⟨278584821251651379829897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485785713342140692426117 278584821251651379829897)
                    ·
                      rfl

theorem cell23_1627626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1627626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627626 prefixEnd_1627626 := by exact prefixLift 1627626
  have htrace : WordTrace (prefixWord ++ tailWord_1627626) baseStart_1627626 baseEnd_1627626 := by
    simpa [prefixWord, tailWord_1627626, baseEnd_1627626] using wordTrace_append hprefix tailTrace_1627626
  have hstable : (prefixWord ++ tailWord_1627626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627626).length < 2 ^ (prefixWord ++ tailWord_1627626).sum := by decide
  have hdescent : baseEnd_1627626 < baseStart_1627626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627632 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 1, 1, 3]
def baseStart_1627632 : Nat := 118140960795 + 1627632 * 2 ^ 59
def prefixEnd_1627632 : Nat := 4983230072969 + 3 ^ 40 * 1627632 * 2
def baseEnd_1627632 : Nat := 835757544638881116014663

theorem tailTrace_1627632 : CollatzResearch.WordTrace tailWord_1627632 prefixEnd_1627632 835757544638881116014663 := by
  unfold tailWord_1627632
  simp only [CollatzResearch.WordTrace]
  refine ⟨29682308019687358129898575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39576410692916477506531433 29682308019687358129898575)
  ·
    refine ⟨44523462029531037194847863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29682308019687358129898575 44523462029531037194847863)
    ·
      refine ⟨66785193044296555792271795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44523462029531037194847863 66785193044296555792271795)
      ·
        refine ⟨100177789566444833688407693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66785193044296555792271795 100177789566444833688407693)
        ·
          refine ⟨37566671087416812633152885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100177789566444833688407693 37566671087416812633152885)
          ·
            refine ⟨3521875414445326184358083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37566671087416812633152885 3521875414445326184358083)
            ·
              refine ⟨5282813121667989276537125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521875414445326184358083 5282813121667989276537125)
              ·
                refine ⟨990527460312747989350711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5282813121667989276537125 990527460312747989350711)
                ·
                  refine ⟨1485791190469121984026067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990527460312747989350711 1485791190469121984026067)
                  ·
                    refine ⟨2228686785703682976039101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485791190469121984026067 2228686785703682976039101)
                    ·
                      refine ⟨835757544638881116014663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2228686785703682976039101 835757544638881116014663)
                      ·
                        rfl

theorem cell23_1627632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 1, 3].length) (baseStart_1627632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627632 prefixEnd_1627632 := by exact prefixLift 1627632
  have htrace : WordTrace (prefixWord ++ tailWord_1627632) baseStart_1627632 baseEnd_1627632 := by
    simpa [prefixWord, tailWord_1627632, baseEnd_1627632] using wordTrace_append hprefix tailTrace_1627632
  have hstable : (prefixWord ++ tailWord_1627632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627632).length < 2 ^ (prefixWord ++ tailWord_1627632).sum := by decide
  have hdescent : baseEnd_1627632 < baseStart_1627632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627641 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1627641 : Nat := 118140960795 + 1627641 * 2 ^ 59
def prefixEnd_1627641 : Nat := 4983230072969 + 3 ^ 40 * 1627641 * 2
def baseEnd_1627641 : Nat := 835762165964771580802121

theorem tailTrace_1627641 : CollatzResearch.WordTrace tailWord_1627641 prefixEnd_1627641 835762165964771580802121 := by
  unfold tailWord_1627641
  simp only [CollatzResearch.WordTrace]
  refine ⟨59364944296342110796874777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39576629530894740531249851 59364944296342110796874777)
  ·
    refine ⟨44523708222256583097656083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59364944296342110796874777 44523708222256583097656083)
    ·
      refine ⟨66785562333384874646484125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44523708222256583097656083 66785562333384874646484125)
      ·
        refine ⟨25044585875019327992431547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66785562333384874646484125 25044585875019327992431547)
        ·
          refine ⟨37566878812528991988647321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25044585875019327992431547 37566878812528991988647321)
          ·
            refine ⟨28175159109396743991485491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37566878812528991988647321 28175159109396743991485491)
            ·
              refine ⟨42262738664095115987228237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28175159109396743991485491 42262738664095115987228237)
              ·
                refine ⟨15848526999035668495210589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42262738664095115987228237 15848526999035668495210589)
                ·
                  refine ⟨5943197624638375685703971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15848526999035668495210589 5943197624638375685703971)
                  ·
                    refine ⟨8914796436957563528555957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5943197624638375685703971 8914796436957563528555957)
                    ·
                      refine ⟨835762165964771580802121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8914796436957563528555957 835762165964771580802121)
                      ·
                        rfl

theorem cell23_1627641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1627641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627641 prefixEnd_1627641 := by exact prefixLift 1627641
  have htrace : WordTrace (prefixWord ++ tailWord_1627641) baseStart_1627641 baseEnd_1627641 := by
    simpa [prefixWord, tailWord_1627641, baseEnd_1627641] using wordTrace_append hprefix tailTrace_1627641
  have hstable : (prefixWord ++ tailWord_1627641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627641).length < 2 ^ (prefixWord ++ tailWord_1627641).sum := by decide
  have hdescent : baseEnd_1627641 < baseStart_1627641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627659 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 2, 3, 2]
def baseStart_1627659 : Nat := 118140960795 + 1627659 * 2 ^ 59
def prefixEnd_1627659 : Nat := 4983230072969 + 3 ^ 40 * 1627659 * 2
def baseEnd_1627659 : Nat := 835771408616552510377039

theorem tailTrace_1627659 : CollatzResearch.WordTrace tailWord_1627659 prefixEnd_1627659 835771408616552510377039 := by
  unfold tailWord_1627659
  simp only [CollatzResearch.WordTrace]
  refine ⟨59365600810276899871030031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39577067206851266580686687 59365600810276899871030031)
  ·
    refine ⟨89048401215415349806545047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59365600810276899871030031 89048401215415349806545047)
    ·
      refine ⟨133572601823123024709817571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89048401215415349806545047 133572601823123024709817571)
      ·
        refine ⟨200358902734684537064726357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133572601823123024709817571 200358902734684537064726357)
        ·
          refine ⟨1173977945711042209363631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 200358902734684537064726357 1173977945711042209363631)
          ·
            refine ⟨1760966918566563314045447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173977945711042209363631 1760966918566563314045447)
            ·
              refine ⟨2641450377849844971068171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760966918566563314045447 2641450377849844971068171)
              ·
                refine ⟨3962175566774767456602257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641450377849844971068171 3962175566774767456602257)
                ·
                  refine ⟨2971631675081075592451693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3962175566774767456602257 2971631675081075592451693)
                  ·
                    refine ⟨1114361878155403347169385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971631675081075592451693 1114361878155403347169385)
                    ·
                      refine ⟨835771408616552510377039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114361878155403347169385 835771408616552510377039)
                      ·
                        rfl

theorem cell23_1627659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 3, 2].length) (baseStart_1627659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627659 prefixEnd_1627659 := by exact prefixLift 1627659
  have htrace : WordTrace (prefixWord ++ tailWord_1627659) baseStart_1627659 baseEnd_1627659 := by
    simpa [prefixWord, tailWord_1627659, baseEnd_1627659] using wordTrace_append hprefix tailTrace_1627659
  have hstable : (prefixWord ++ tailWord_1627659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627659).length < 2 ^ (prefixWord ++ tailWord_1627659).sum := by decide
  have hdescent : baseEnd_1627659 < baseStart_1627659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627705 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1627705 : Nat := 118140960795 + 1627705 * 2 ^ 59
def prefixEnd_1627705 : Nat := 4983230072969 + 3 ^ 40 * 1627705 * 2
def baseEnd_1627705 : Nat := 835795028726659330401827

theorem tailTrace_1627705 : CollatzResearch.WordTrace tailWord_1627705 prefixEnd_1627705 835795028726659330401827 := by
  unfold tailWord_1627705
  simp only [CollatzResearch.WordTrace]
  refine ⟨59367278568110249727204569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39578185712073499818136379 59367278568110249727204569)
  ·
    refine ⟨44525458926082687295403427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59367278568110249727204569 44525458926082687295403427)
    ·
      refine ⟨66788188389124030943105141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44525458926082687295403427 66788188389124030943105141)
      ·
        refine ⟨6261392661480377900916107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66788188389124030943105141 6261392661480377900916107)
        ·
          refine ⟨9392088992220566851374161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261392661480377900916107 9392088992220566851374161)
          ·
            refine ⟨7044066744165425138530621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9392088992220566851374161 7044066744165425138530621)
            ·
              refine ⟨2641525029062034426948983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7044066744165425138530621 2641525029062034426948983)
              ·
                refine ⟨3962287543593051640423475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641525029062034426948983 3962287543593051640423475)
                ·
                  refine ⟨5943431315389577460635213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962287543593051640423475 5943431315389577460635213)
                  ·
                    refine ⟨2228786743271091547738205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5943431315389577460635213 2228786743271091547738205)
                    ·
                      refine ⟨835795028726659330401827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2228786743271091547738205 835795028726659330401827)
                      ·
                        rfl

theorem cell23_1627705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1627705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627705 prefixEnd_1627705 := by exact prefixLift 1627705
  have htrace : WordTrace (prefixWord ++ tailWord_1627705) baseStart_1627705 baseEnd_1627705 := by
    simpa [prefixWord, tailWord_1627705, baseEnd_1627705] using wordTrace_append hprefix tailTrace_1627705
  have hstable : (prefixWord ++ tailWord_1627705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627705).length < 2 ^ (prefixWord ++ tailWord_1627705).sum := by decide
  have hdescent : baseEnd_1627705 < baseStart_1627705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627721 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_1627721 : Nat := 118140960795 + 1627721 * 2 ^ 59
def prefixEnd_1627721 : Nat := 4983230072969 + 3 ^ 40 * 1627721 * 2
def baseEnd_1627721 : Nat := 278601081472377089267251

theorem tailTrace_1627721 : CollatzResearch.WordTrace tailWord_1627721 prefixEnd_1627721 278601081472377089267251 := by
  unfold tailWord_1627721
  simp only [CollatzResearch.WordTrace]
  refine ⟨59367862136052284459787017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39578574757368189639858011 59367862136052284459787017)
  ·
    refine ⟨44525896602039213344840263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59367862136052284459787017 44525896602039213344840263)
    ·
      refine ⟨66788844903058820017260395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44525896602039213344840263 66788844903058820017260395)
      ·
        refine ⟨100183267354588230025890593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66788844903058820017260395 100183267354588230025890593)
        ·
          refine ⟨75137450515941172519417945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100183267354588230025890593 75137450515941172519417945)
          ·
            refine ⟨56353087886955879389563459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75137450515941172519417945 56353087886955879389563459)
            ·
              refine ⟨84529631830433819084345189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56353087886955879389563459 84529631830433819084345189)
              ·
                refine ⟨15849305968206341078314723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84529631830433819084345189 15849305968206341078314723)
                ·
                  refine ⟨23773958952309511617472085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15849305968206341078314723 23773958952309511617472085)
                  ·
                    refine ⟨278601081472377089267251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23773958952309511617472085 278601081472377089267251)
                    ·
                      rfl

theorem cell23_1627721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_1627721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627721 prefixEnd_1627721 := by exact prefixLift 1627721
  have htrace : WordTrace (prefixWord ++ tailWord_1627721) baseStart_1627721 baseEnd_1627721 := by
    simpa [prefixWord, tailWord_1627721, baseEnd_1627721] using wordTrace_append hprefix tailTrace_1627721
  have hstable : (prefixWord ++ tailWord_1627721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627721).length < 2 ^ (prefixWord ++ tailWord_1627721).sum := by decide
  have hdescent : baseEnd_1627721 < baseStart_1627721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627732 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_1627732 : Nat := 118140960795 + 1627732 * 2 ^ 59
def prefixEnd_1627732 : Nat := 4983230072969 + 3 ^ 40 * 1627732 * 2
def baseEnd_1627732 : Nat := 835808892704330724764203

theorem tailTrace_1627732 : CollatzResearch.WordTrace tailWord_1627732 prefixEnd_1627732 835808892704330724764203 := by
  unfold tailWord_1627732
  simp only [CollatzResearch.WordTrace]
  refine ⟨29684131669506216669218725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39578842226008288892291633 29684131669506216669218725)
  ·
    refine ⟨5565774688032415625478511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29684131669506216669218725 5565774688032415625478511)
    ·
      refine ⟨8348662032048623438217767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565774688032415625478511 8348662032048623438217767)
      ·
        refine ⟨12522993048072935157326651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348662032048623438217767 12522993048072935157326651)
        ·
          refine ⟨18784489572109402735989977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12522993048072935157326651 18784489572109402735989977)
          ·
            refine ⟨14088367179082052051992483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18784489572109402735989977 14088367179082052051992483)
            ·
              refine ⟨21132550768623078077988725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14088367179082052051992483 21132550768623078077988725)
              ·
                refine ⟨1981176634558413569811443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21132550768623078077988725 1981176634558413569811443)
                ·
                  refine ⟨2971764951837620354717165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981176634558413569811443 2971764951837620354717165)
                  ·
                    refine ⟨1114411856939107633018937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971764951837620354717165 1114411856939107633018937)
                    ·
                      refine ⟨835808892704330724764203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114411856939107633018937 835808892704330724764203)
                      ·
                        rfl

theorem cell23_1627732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_1627732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627732 prefixEnd_1627732 := by exact prefixLift 1627732
  have htrace : WordTrace (prefixWord ++ tailWord_1627732) baseStart_1627732 baseEnd_1627732 := by
    simpa [prefixWord, tailWord_1627732, baseEnd_1627732] using wordTrace_append hprefix tailTrace_1627732
  have hstable : (prefixWord ++ tailWord_1627732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627732).length < 2 ^ (prefixWord ++ tailWord_1627732).sum := by decide
  have hdescent : baseEnd_1627732 < baseStart_1627732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627765 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1627765 : Nat := 118140960795 + 1627765 * 2 ^ 59
def prefixEnd_1627765 : Nat := 4983230072969 + 3 ^ 40 * 1627765 * 2
def baseEnd_1627765 : Nat := 835825837565929095651551

theorem tailTrace_1627765 : CollatzResearch.WordTrace tailWord_1627765 prefixEnd_1627765 835825837565929095651551 := by
  unfold tailWord_1627765
  simp only [CollatzResearch.WordTrace]
  refine ⟨59369466947892879974388749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39579644631928586649592499 59369466947892879974388749)
  ·
    refine ⟨22263550105459829990395781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59369466947892879974388749 22263550105459829990395781)
    ·
      refine ⟨4174415644773718123199209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22263550105459829990395781 4174415644773718123199209)
      ·
        refine ⟨3130811733580288592399407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4174415644773718123199209 3130811733580288592399407)
        ·
          refine ⟨4696217600370432888599111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130811733580288592399407 4696217600370432888599111)
          ·
            refine ⟨7044326400555649332898667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696217600370432888599111 7044326400555649332898667)
            ·
              refine ⟨10566489600833473999348001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7044326400555649332898667 10566489600833473999348001)
              ·
                refine ⟨7924867200625105499511001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10566489600833473999348001 7924867200625105499511001)
                ·
                  refine ⟨5943650400468829124633251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7924867200625105499511001 5943650400468829124633251)
                  ·
                    refine ⟨8915475600703243686949877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5943650400468829124633251 8915475600703243686949877)
                    ·
                      refine ⟨835825837565929095651551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8915475600703243686949877 835825837565929095651551)
                      ·
                        rfl

theorem cell23_1627765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1627765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627765 prefixEnd_1627765 := by exact prefixLift 1627765
  have htrace : WordTrace (prefixWord ++ tailWord_1627765) baseStart_1627765 baseEnd_1627765 := by
    simpa [prefixWord, tailWord_1627765, baseEnd_1627765] using wordTrace_append hprefix tailTrace_1627765
  have hstable : (prefixWord ++ tailWord_1627765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627765).length < 2 ^ (prefixWord ++ tailWord_1627765).sum := by decide
  have hdescent : baseEnd_1627765 < baseStart_1627765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627766 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1627766 : Nat := 118140960795 + 1627766 * 2 ^ 59
def prefixEnd_1627766 : Nat := 4983230072969 + 3 ^ 40 * 1627766 * 2
def baseEnd_1627766 : Nat := 835826351046583591739047

theorem tailTrace_1627766 : CollatzResearch.WordTrace tailWord_1627766 prefixEnd_1627766 835826351046583591739047 := by
  unfold tailWord_1627766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710593963805578571573447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39579668947259504763450101 3710593963805578571573447)
  ·
    refine ⟨5565890945708367857360171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3710593963805578571573447 5565890945708367857360171)
    ·
      refine ⟨8348836418562551786040257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565890945708367857360171 8348836418562551786040257)
      ·
        refine ⟨6261627313921913839530193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8348836418562551786040257 6261627313921913839530193)
        ·
          refine ⟨4696220485441435379647645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6261627313921913839530193 4696220485441435379647645)
          ·
            refine ⟨1761082682040538267367867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4696220485441435379647645 1761082682040538267367867)
            ·
              refine ⟨2641624023060807401051801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761082682040538267367867 2641624023060807401051801)
              ·
                refine ⟨1981218017295605550788851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641624023060807401051801 1981218017295605550788851)
                ·
                  refine ⟨2971827025943408326183277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981218017295605550788851 2971827025943408326183277)
                  ·
                    refine ⟨1114435134728778122318729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971827025943408326183277 1114435134728778122318729)
                    ·
                      refine ⟨835826351046583591739047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114435134728778122318729 835826351046583591739047)
                      ·
                        rfl

theorem cell23_1627766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1627766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627766 prefixEnd_1627766 := by exact prefixLift 1627766
  have htrace : WordTrace (prefixWord ++ tailWord_1627766) baseStart_1627766 baseEnd_1627766 := by
    simpa [prefixWord, tailWord_1627766, baseEnd_1627766] using wordTrace_append hprefix tailTrace_1627766
  have hstable : (prefixWord ++ tailWord_1627766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627766).length < 2 ^ (prefixWord ++ tailWord_1627766).sum := by decide
  have hdescent : baseEnd_1627766 < baseStart_1627766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627848 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1627848 : Nat := 118140960795 + 1627848 * 2 ^ 59
def prefixEnd_1627848 : Nat := 4983230072969 + 3 ^ 40 * 1627848 * 2
def baseEnd_1627848 : Nat := 835868456460252270913669

theorem tailTrace_1627848 : CollatzResearch.WordTrace tailWord_1627848 prefixEnd_1627848 835868456460252270913669 := by
  unfold tailWord_1627848
  simp only [CollatzResearch.WordTrace]
  refine ⟨29686247103296092574830099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39581662804394790099773465 29686247103296092574830099)
  ·
    refine ⟨44529370654944138862245149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29686247103296092574830099 44529370654944138862245149)
    ·
      refine ⟨16698513995604052073341931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44529370654944138862245149 16698513995604052073341931)
      ·
        refine ⟨25047770993406078110012897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16698513995604052073341931 25047770993406078110012897)
        ·
          refine ⟨18785828245054558582509673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25047770993406078110012897 18785828245054558582509673)
          ·
            refine ⟨14089371183790918936882255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18785828245054558582509673 14089371183790918936882255)
            ·
              refine ⟨21134056775686378405323383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14089371183790918936882255 21134056775686378405323383)
              ·
                refine ⟨31701085163529567607985075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21134056775686378405323383 31701085163529567607985075)
                ·
                  refine ⟨47551627745294351411977613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31701085163529567607985075 47551627745294351411977613)
                  ·
                    refine ⟨17831860404485381779491605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47551627745294351411977613 17831860404485381779491605)
                    ·
                      refine ⟨835868456460252270913669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17831860404485381779491605 835868456460252270913669)
                      ·
                        rfl

theorem cell23_1627848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1627848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627848 prefixEnd_1627848 := by exact prefixLift 1627848
  have htrace : WordTrace (prefixWord ++ tailWord_1627848) baseStart_1627848 baseEnd_1627848 := by
    simpa [prefixWord, tailWord_1627848, baseEnd_1627848] using wordTrace_append hprefix tailTrace_1627848
  have hstable : (prefixWord ++ tailWord_1627848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627848).length < 2 ^ (prefixWord ++ tailWord_1627848).sum := by decide
  have hdescent : baseEnd_1627848 < baseStart_1627848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627855 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_1627855 : Nat := 118140960795 + 1627855 * 2 ^ 59
def prefixEnd_1627855 : Nat := 4983230072969 + 3 ^ 40 * 1627855 * 2
def baseEnd_1627855 : Nat := 835872050824833743526137

theorem tailTrace_1627855 : CollatzResearch.WordTrace tailWord_1627855 prefixEnd_1627855 835872050824833743526137 := by
  unfold tailWord_1627855
  simp only [CollatzResearch.WordTrace]
  refine ⟨59372749517566825345165019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39581833011711216896776679 59372749517566825345165019)
  ·
    refine ⟨89059124276350238017747529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59372749517566825345165019 89059124276350238017747529)
    ·
      refine ⟨66794343207262678513310647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89059124276350238017747529 66794343207262678513310647)
      ·
        refine ⟨100191514810894017769965971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66794343207262678513310647 100191514810894017769965971)
        ·
          refine ⟨150287272216341026654948957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100191514810894017769965971 150287272216341026654948957)
          ·
            refine ⟨56357727081127884995605859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150287272216341026654948957 56357727081127884995605859)
            ·
              refine ⟨84536590621691827493408789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56357727081127884995605859 84536590621691827493408789)
              ·
                refine ⟨3962652685391804413753537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84536590621691827493408789 3962652685391804413753537)
                ·
                  refine ⟨2971989514043853310315153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3962652685391804413753537 2971989514043853310315153)
                  ·
                    refine ⟨2228992135532889982736365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2971989514043853310315153 2228992135532889982736365)
                    ·
                      refine ⟨835872050824833743526137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2228992135532889982736365 835872050824833743526137)
                      ·
                        rfl

theorem cell23_1627855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_1627855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627855 prefixEnd_1627855 := by exact prefixLift 1627855
  have htrace : WordTrace (prefixWord ++ tailWord_1627855) baseStart_1627855 baseEnd_1627855 := by
    simpa [prefixWord, tailWord_1627855, baseEnd_1627855] using wordTrace_append hprefix tailTrace_1627855
  have hstable : (prefixWord ++ tailWord_1627855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627855).length < 2 ^ (prefixWord ++ tailWord_1627855).sum := by decide
  have hdescent : baseEnd_1627855 < baseStart_1627855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627935 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 1, 6]
def baseStart_1627935 : Nat := 118140960795 + 1627935 * 2 ^ 59
def prefixEnd_1627935 : Nat := 4983230072969 + 3 ^ 40 * 1627935 * 2
def baseEnd_1627935 : Nat := 278637709759064476841923

theorem tailTrace_1627935 : CollatzResearch.WordTrace tailWord_1627935 prefixEnd_1627935 278637709759064476841923 := by
  unfold tailWord_1627935
  simp only [CollatzResearch.WordTrace]
  refine ⟨59375667357276999008077259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39583778238184666005384839 59375667357276999008077259)
  ·
    refine ⟨89063501035915498512115889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59375667357276999008077259 89063501035915498512115889)
    ·
      refine ⟨66797625776936623884086917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89063501035915498512115889 66797625776936623884086917)
      ·
        refine ⟨12524554833175616978266297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66797625776936623884086917 12524554833175616978266297)
        ·
          refine ⟨9393416124881712733699723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12524554833175616978266297 9393416124881712733699723)
          ·
            refine ⟨14090124187322569100549585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393416124881712733699723 14090124187322569100549585)
            ·
              refine ⟨10567593140491926825412189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14090124187322569100549585 10567593140491926825412189)
              ·
                refine ⟨3962847427684472559529571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10567593140491926825412189 3962847427684472559529571)
                ·
                  refine ⟨5944271141526708839294357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962847427684472559529571 5944271141526708839294357)
                  ·
                    refine ⟨278637709759064476841923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5944271141526708839294357 278637709759064476841923)
                    ·
                      rfl

theorem cell23_1627935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_1627935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627935 prefixEnd_1627935 := by exact prefixLift 1627935
  have htrace : WordTrace (prefixWord ++ tailWord_1627935) baseStart_1627935 baseEnd_1627935 := by
    simpa [prefixWord, tailWord_1627935, baseEnd_1627935] using wordTrace_append hprefix tailTrace_1627935
  have hstable : (prefixWord ++ tailWord_1627935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627935).length < 2 ^ (prefixWord ++ tailWord_1627935).sum := by decide
  have hdescent : baseEnd_1627935 < baseStart_1627935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627956 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1627956 : Nat := 118140960795 + 1627956 * 2 ^ 59
def prefixEnd_1627956 : Nat := 4983230072969 + 3 ^ 40 * 1627956 * 2
def baseEnd_1627956 : Nat := 278641304123645949454391

theorem tailTrace_1627956 : CollatzResearch.WordTrace tailWord_1627956 prefixEnd_1627956 278641304123645949454391 := by
  unfold tailWord_1627956
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688216645100459797295861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39584288860133946396394481 29688216645100459797295861)
  ·
    refine ⟨2783270310478168105996487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29688216645100459797295861 2783270310478168105996487)
    ·
      refine ⟨4174905465717252158994731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783270310478168105996487 4174905465717252158994731)
      ·
        refine ⟨6262358198575878238492097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174905465717252158994731 6262358198575878238492097)
        ·
          refine ⟨4696768648931908678869073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262358198575878238492097 4696768648931908678869073)
          ·
            refine ⟨3522576486698931509151805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4696768648931908678869073 3522576486698931509151805)
            ·
              refine ⟨1320966182512099315931927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3522576486698931509151805 1320966182512099315931927)
              ·
                refine ⟨1981449273768148973897891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320966182512099315931927 1981449273768148973897891)
                ·
                  refine ⟨2972173910652223460846837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981449273768148973897891 2972173910652223460846837)
                  ·
                    refine ⟨278641304123645949454391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2972173910652223460846837 278641304123645949454391)
                    ·
                      rfl

theorem cell23_1627956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1627956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627956 prefixEnd_1627956 := by exact prefixLift 1627956
  have htrace : WordTrace (prefixWord ++ tailWord_1627956) baseStart_1627956 baseEnd_1627956 := by
    simpa [prefixWord, tailWord_1627956, baseEnd_1627956] using wordTrace_append hprefix tailTrace_1627956
  have hstable : (prefixWord ++ tailWord_1627956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627956).length < 2 ^ (prefixWord ++ tailWord_1627956).sum := by decide
  have hdescent : baseEnd_1627956 < baseStart_1627956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627962 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_1627962 : Nat := 118140960795 + 1627962 * 2 ^ 59
def prefixEnd_1627962 : Nat := 4983230072969 + 3 ^ 40 * 1627962 * 2
def baseEnd_1627962 : Nat := 835926993254864824888145

theorem tailTrace_1627962 : CollatzResearch.WordTrace tailWord_1627962 prefixEnd_1627962 835926993254864824888145 := by
  unfold tailWord_1627962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844163032044795654827535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39584434752119455079540093 14844163032044795654827535)
  ·
    refine ⟨22266244548067193482241303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14844163032044795654827535 22266244548067193482241303)
    ·
      refine ⟨33399366822100790223361955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22266244548067193482241303 33399366822100790223361955)
      ·
        refine ⟨50099050233151185335042933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33399366822100790223361955 50099050233151185335042933)
        ·
          refine ⟨4696785959357923625160275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50099050233151185335042933 4696785959357923625160275)
          ·
            refine ⟨7045178939036885437740413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696785959357923625160275 7045178939036885437740413)
            ·
              refine ⟨2641942102138832039152655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7045178939036885437740413 2641942102138832039152655)
              ·
                refine ⟨3962913153208248058728983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641942102138832039152655 3962913153208248058728983)
                ·
                  refine ⟨5944369729812372088093475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962913153208248058728983 5944369729812372088093475)
                  ·
                    refine ⟨8916554594718558132140213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5944369729812372088093475 8916554594718558132140213)
                    ·
                      refine ⟨835926993254864824888145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8916554594718558132140213 835926993254864824888145)
                      ·
                        rfl

theorem cell23_1627962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_1627962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627962 prefixEnd_1627962 := by exact prefixLift 1627962
  have htrace : WordTrace (prefixWord ++ tailWord_1627962) baseStart_1627962 baseEnd_1627962 := by
    simpa [prefixWord, tailWord_1627962, baseEnd_1627962] using wordTrace_append hprefix tailTrace_1627962
  have hstable : (prefixWord ++ tailWord_1627962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627962).length < 2 ^ (prefixWord ++ tailWord_1627962).sum := by decide
  have hdescent : baseEnd_1627962 < baseStart_1627962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627965 : List Nat := [1, 4, 1, 4, 1, 12]
def baseStart_1627965 : Nat := 118140960795 + 1627965 * 2 ^ 59
def prefixEnd_1627965 : Nat := 4983230072969 + 3 ^ 40 * 1627965 * 2
def baseEnd_1627965 : Nat := 3440035118093943675517

theorem tailTrace_1627965 : CollatzResearch.WordTrace tailWord_1627965 prefixEnd_1627965 3440035118093943675517 := by
  unfold tailWord_1627965
  simp only [CollatzResearch.WordTrace]
  refine ⟨59376761547168314131669349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39584507698112209421112899 59376761547168314131669349)
  ·
    refine ⟨11133142790094058899688003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59376761547168314131669349 11133142790094058899688003)
    ·
      refine ⟨16699714185141088349532005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11133142790094058899688003 16699714185141088349532005)
      ·
        refine ⟨3131196409713954065537251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16699714185141088349532005 3131196409713954065537251)
        ·
          refine ⟨4696794614570931098305877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131196409713954065537251 4696794614570931098305877)
          ·
            refine ⟨3440035118093943675517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4696794614570931098305877 3440035118093943675517)
            ·
              rfl

theorem cell23_1627965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 12].length) (baseStart_1627965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627965 prefixEnd_1627965 := by exact prefixLift 1627965
  have htrace : WordTrace (prefixWord ++ tailWord_1627965) baseStart_1627965 baseEnd_1627965 := by
    simpa [prefixWord, tailWord_1627965, baseEnd_1627965] using wordTrace_append hprefix tailTrace_1627965
  have hstable : (prefixWord ++ tailWord_1627965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627965).length < 2 ^ (prefixWord ++ tailWord_1627965).sum := by decide
  have hdescent : baseEnd_1627965 < baseStart_1627965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627992 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1627992 : Nat := 118140960795 + 1627992 * 2 ^ 59
def prefixEnd_1627992 : Nat := 4983230072969 + 3 ^ 40 * 1627992 * 2
def baseEnd_1627992 : Nat := 835942397674499707513007

theorem tailTrace_1627992 : CollatzResearch.WordTrace tailWord_1627992 prefixEnd_1627992 835942397674499707513007 := by
  unfold tailWord_1627992
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688873159035248871451115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39585164212046998495268153 29688873159035248871451115)
  ·
    refine ⟨44533309738552873307176673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29688873159035248871451115 44533309738552873307176673)
    ·
      refine ⟨33399982303914654980382505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44533309738552873307176673 33399982303914654980382505)
      ·
        refine ⟨25049986727935991235286879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33399982303914654980382505 25049986727935991235286879)
        ·
          refine ⟨37574980091903986852930319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25049986727935991235286879 37574980091903986852930319)
          ·
            refine ⟨56362470137855980279395479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37574980091903986852930319 56362470137855980279395479)
            ·
              refine ⟨84543705206783970419093219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56362470137855980279395479 84543705206783970419093219)
              ·
                refine ⟨126815557810175955628639829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84543705206783970419093219 126815557810175955628639829)
                ·
                  refine ⟨1486119818087999480023123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 126815557810175955628639829 1486119818087999480023123)
                  ·
                    refine ⟨2229179727131999220034685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1486119818087999480023123 2229179727131999220034685)
                    ·
                      refine ⟨835942397674499707513007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2229179727131999220034685 835942397674499707513007)
                      ·
                        rfl

theorem cell23_1627992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1627992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1627992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1627992 prefixEnd_1627992 := by exact prefixLift 1627992
  have htrace : WordTrace (prefixWord ++ tailWord_1627992) baseStart_1627992 baseEnd_1627992 := by
    simpa [prefixWord, tailWord_1627992, baseEnd_1627992] using wordTrace_append hprefix tailTrace_1627992
  have hstable : (prefixWord ++ tailWord_1627992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627992).length < 2 ^ (prefixWord ++ tailWord_1627992).sum := by decide
  have hdescent : baseEnd_1627992 < baseStart_1627992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628005 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1628005 : Nat := 118140960795 + 1628005 * 2 ^ 59
def prefixEnd_1628005 : Nat := 4983230072969 + 3 ^ 40 * 1628005 * 2
def baseEnd_1628005 : Nat := 835949072923008156650447

theorem tailTrace_1628005 : CollatzResearch.WordTrace tailWord_1628005 prefixEnd_1628005 835949072923008156650447 := by
  unfold tailWord_1628005
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378220467023400963125469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39585480311348933975416979 59378220467023400963125469)
  ·
    refine ⟨22266832675133775361172051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59378220467023400963125469 22266832675133775361172051)
    ·
      refine ⟨33400249012700663041758077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22266832675133775361172051 33400249012700663041758077)
      ·
        refine ⟨12525093379762748640659279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33400249012700663041758077 12525093379762748640659279)
        ·
          refine ⟨18787640069644122960988919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12525093379762748640659279 18787640069644122960988919)
          ·
            refine ⟨28181460104466184441483379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18787640069644122960988919 28181460104466184441483379)
            ·
              refine ⟨42272190156699276662225069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28181460104466184441483379 42272190156699276662225069)
              ·
                refine ⟨15852071308762228748334401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42272190156699276662225069 15852071308762228748334401)
                ·
                  refine ⟨11889053481571671561250801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15852071308762228748334401 11889053481571671561250801)
                  ·
                    refine ⟨8916790111178753670938101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11889053481571671561250801 8916790111178753670938101)
                    ·
                      refine ⟨835949072923008156650447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8916790111178753670938101 835949072923008156650447)
                      ·
                        rfl

theorem cell23_1628005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1628005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628005 prefixEnd_1628005 := by exact prefixLift 1628005
  have htrace : WordTrace (prefixWord ++ tailWord_1628005) baseStart_1628005 baseEnd_1628005 := by
    simpa [prefixWord, tailWord_1628005, baseEnd_1628005] using wordTrace_append hprefix tailTrace_1628005
  have hstable : (prefixWord ++ tailWord_1628005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628005).length < 2 ^ (prefixWord ++ tailWord_1628005).sum := by decide
  have hdescent : baseEnd_1628005 < baseStart_1628005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628010 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1628010 : Nat := 118140960795 + 1628010 * 2 ^ 59
def prefixEnd_1628010 : Nat := 4983230072969 + 3 ^ 40 * 1628010 * 2
def baseEnd_1628010 : Nat := 835951640326280637087925

theorem tailTrace_1628010 : CollatzResearch.WordTrace tailWord_1628010 prefixEnd_1628010 835951640326280637087925 := by
  unfold tailWord_1628010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844600708001321704264371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39585601888003524544704989 14844600708001321704264371)
  ·
    refine ⟨22266901062001982556396557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14844600708001321704264371 22266901062001982556396557)
    ·
      refine ⟨8350087898250743458648709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22266901062001982556396557 8350087898250743458648709)
      ·
        refine ⟨1565641480922014398496633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8350087898250743458648709 1565641480922014398496633)
        ·
          refine ⟨1174231110691510798872475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565641480922014398496633 1174231110691510798872475)
          ·
            refine ⟨1761346666037266198308713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174231110691510798872475 1761346666037266198308713)
            ·
              refine ⟨1321009999527949648731535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761346666037266198308713 1321009999527949648731535)
              ·
                refine ⟨1981514999291924473097303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321009999527949648731535 1981514999291924473097303)
                ·
                  refine ⟨2972272498937886709645955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981514999291924473097303 2972272498937886709645955)
                  ·
                    refine ⟨4458408748406830064468933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2972272498937886709645955 4458408748406830064468933)
                    ·
                      refine ⟨835951640326280637087925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4458408748406830064468933 835951640326280637087925)
                      ·
                        rfl

theorem cell23_1628010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1628010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628010 prefixEnd_1628010 := by exact prefixLift 1628010
  have htrace : WordTrace (prefixWord ++ tailWord_1628010) baseStart_1628010 baseEnd_1628010 := by
    simpa [prefixWord, tailWord_1628010, baseEnd_1628010] using wordTrace_append hprefix tailTrace_1628010
  have hstable : (prefixWord ++ tailWord_1628010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628010).length < 2 ^ (prefixWord ++ tailWord_1628010).sum := by decide
  have hdescent : baseEnd_1628010 < baseStart_1628010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628025 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_1628025 : Nat := 118140960795 + 1628025 * 2 ^ 59
def prefixEnd_1628025 : Nat := 4983230072969 + 3 ^ 40 * 1628025 * 2
def baseEnd_1628025 : Nat := 278653114178699359466785

theorem tailTrace_1628025 : CollatzResearch.WordTrace tailWord_1628025 prefixEnd_1628025 278653114178699359466785 := by
  unfold tailWord_1628025
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378949926950944378853529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39585966617967296252569019 59378949926950944378853529)
  ·
    refine ⟨44534212445213208284140147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59378949926950944378853529 44534212445213208284140147)
    ·
      refine ⟨66801318667819812426210221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44534212445213208284140147 66801318667819812426210221)
      ·
        refine ⟨25050494500432429659828833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66801318667819812426210221 25050494500432429659828833)
        ·
          refine ⟨18787870875324322244871625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25050494500432429659828833 18787870875324322244871625)
          ·
            refine ⟨14090903156493241683653719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18787870875324322244871625 14090903156493241683653719)
            ·
              refine ⟨21136354734739862525480579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14090903156493241683653719 21136354734739862525480579)
              ·
                refine ⟨31704532102109793788220869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21136354734739862525480579 31704532102109793788220869)
                ·
                  refine ⟨5944599769145586335291413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31704532102109793788220869 5944599769145586335291413)
                  ·
                    refine ⟨278653114178699359466785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5944599769145586335291413 278653114178699359466785)
                    ·
                      rfl

theorem cell23_1628025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_1628025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628025 prefixEnd_1628025 := by exact prefixLift 1628025
  have htrace : WordTrace (prefixWord ++ tailWord_1628025) baseStart_1628025 baseEnd_1628025 := by
    simpa [prefixWord, tailWord_1628025, baseEnd_1628025] using wordTrace_append hprefix tailTrace_1628025
  have hstable : (prefixWord ++ tailWord_1628025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628025).length < 2 ^ (prefixWord ++ tailWord_1628025).sum := by decide
  have hdescent : baseEnd_1628025 < baseStart_1628025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628049 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 1, 4, 2]
def baseStart_1628049 : Nat := 118140960795 + 1628049 * 2 ^ 59
def prefixEnd_1628049 : Nat := 4983230072969 + 3 ^ 40 * 1628049 * 2
def baseEnd_1628049 : Nat := 835971666071805984500245

theorem tailTrace_1628049 : CollatzResearch.WordTrace tailWord_1628049 prefixEnd_1628049 835971666071805984500245 := by
  unfold tailWord_1628049
  simp only [CollatzResearch.WordTrace]
  refine ⟨59379825278863996477727201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39586550185909330985151467 59379825278863996477727201)
  ·
    refine ⟨44534868959147997358295401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59379825278863996477727201 44534868959147997358295401)
    ·
      refine ⟨33401151719360998018721551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44534868959147997358295401 33401151719360998018721551)
      ·
        refine ⟨50101727579041497028082327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33401151719360998018721551 50101727579041497028082327)
        ·
          refine ⟨75152591368562245542123491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50101727579041497028082327 75152591368562245542123491)
          ·
            refine ⟨112728887052843368313185237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75152591368562245542123491 112728887052843368313185237)
            ·
              refine ⟨2642083290301016444840279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112728887052843368313185237 2642083290301016444840279)
              ·
                refine ⟨3963124935451524667260419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642083290301016444840279 3963124935451524667260419)
                ·
                  refine ⟨5944687403177287000890629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963124935451524667260419 5944687403177287000890629)
                  ·
                    refine ⟨1114628888095741312666993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5944687403177287000890629 1114628888095741312666993)
                    ·
                      refine ⟨835971666071805984500245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114628888095741312666993 835971666071805984500245)
                      ·
                        rfl

theorem cell23_1628049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_1628049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628049 prefixEnd_1628049 := by exact prefixLift 1628049
  have htrace : WordTrace (prefixWord ++ tailWord_1628049) baseStart_1628049 baseEnd_1628049 := by
    simpa [prefixWord, tailWord_1628049, baseEnd_1628049] using wordTrace_append hprefix tailTrace_1628049
  have hstable : (prefixWord ++ tailWord_1628049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628049).length < 2 ^ (prefixWord ++ tailWord_1628049).sum := by decide
  have hdescent : baseEnd_1628049 < baseStart_1628049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628082 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1628082 : Nat := 118140960795 + 1628082 * 2 ^ 59
def prefixEnd_1628082 : Nat := 4983230072969 + 3 ^ 40 * 1628082 * 2
def baseEnd_1628082 : Nat := 835988610933404355387593

theorem tailTrace_1628082 : CollatzResearch.WordTrace tailWord_1628082 prefixEnd_1628082 835988610933404355387593 := by
  unfold tailWord_1628082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845257221936110778419625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39587352591829628742452333 14845257221936110778419625)
  ·
    refine ⟨11133942916452083083814719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14845257221936110778419625 11133942916452083083814719)
    ·
      refine ⟨16700914374678124625722079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11133942916452083083814719 16700914374678124625722079)
      ·
        refine ⟨25051371562017186938583119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16700914374678124625722079 25051371562017186938583119)
        ·
          refine ⟨37577057343025780407874679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25051371562017186938583119 37577057343025780407874679)
          ·
            refine ⟨56365586014538670611812019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37577057343025780407874679 56365586014538670611812019)
            ·
              refine ⟨84548379021808005917718029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56365586014538670611812019 84548379021808005917718029)
              ·
                refine ⟨31705642133178002219144261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84548379021808005917718029 31705642133178002219144261)
                ·
                  refine ⟨5944807899970875416089549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31705642133178002219144261 5944807899970875416089549)
                  ·
                    refine ⟨2229302962489078281033581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5944807899970875416089549 2229302962489078281033581)
                    ·
                      refine ⟨835988610933404355387593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2229302962489078281033581 835988610933404355387593)
                      ·
                        rfl

theorem cell23_1628082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1628082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628082 prefixEnd_1628082 := by exact prefixLift 1628082
  have htrace : WordTrace (prefixWord ++ tailWord_1628082) baseStart_1628082 baseEnd_1628082 := by
    simpa [prefixWord, tailWord_1628082, baseEnd_1628082] using wordTrace_append hprefix tailTrace_1628082
  have hstable : (prefixWord ++ tailWord_1628082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628082).length < 2 ^ (prefixWord ++ tailWord_1628082).sum := by decide
  have hdescent : baseEnd_1628082 < baseStart_1628082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628229 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 8, 2]
def baseStart_1628229 : Nat := 118140960795 + 1628229 * 2 ^ 59
def prefixEnd_1628229 : Nat := 4983230072969 + 3 ^ 40 * 1628229 * 2
def baseEnd_1628229 : Nat := 836064092589615280249417

theorem tailTrace_1628229 : CollatzResearch.WordTrace tailWord_1628229 prefixEnd_1628229 836064092589615280249417 := by
  unfold tailWord_1628229
  simp only [CollatzResearch.WordTrace]
  refine ⟨59386390418211887219279741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39590926945474591479519827 59386390418211887219279741)
  ·
    refine ⟨22269896406829457707229903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59386390418211887219279741 22269896406829457707229903)
    ·
      refine ⟨33404844610244186560844855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22269896406829457707229903 33404844610244186560844855)
      ·
        refine ⟨50107266915366279841267283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33404844610244186560844855 50107266915366279841267283)
        ·
          refine ⟨75160900373049419761900925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50107266915366279841267283 75160900373049419761900925)
          ·
            refine ⟨28185337639893532410712847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75160900373049419761900925 28185337639893532410712847)
            ·
              refine ⟨42278006459840298616069271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28185337639893532410712847 42278006459840298616069271)
              ·
                refine ⟨63417009689760447924103907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42278006459840298616069271 63417009689760447924103907)
                ·
                  refine ⟨95125514534640671886155861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63417009689760447924103907 95125514534640671886155861)
                  ·
                    refine ⟨1114752123452820373665889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95125514534640671886155861 1114752123452820373665889)
                    ·
                      refine ⟨836064092589615280249417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114752123452820373665889 836064092589615280249417)
                      ·
                        rfl

theorem cell23_1628229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_1628229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628229 prefixEnd_1628229 := by exact prefixLift 1628229
  have htrace : WordTrace (prefixWord ++ tailWord_1628229) baseStart_1628229 baseEnd_1628229 := by
    simpa [prefixWord, tailWord_1628229, baseEnd_1628229] using wordTrace_append hprefix tailTrace_1628229
  have hstable : (prefixWord ++ tailWord_1628229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628229).length < 2 ^ (prefixWord ++ tailWord_1628229).sum := by decide
  have hdescent : baseEnd_1628229 < baseStart_1628229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628249 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_1628249 : Nat := 118140960795 + 1628249 * 2 ^ 59
def prefixEnd_1628249 : Nat := 4983230072969 + 3 ^ 40 * 1628249 * 2
def baseEnd_1628249 : Nat := 836074362202705201999325

theorem tailTrace_1628249 : CollatzResearch.WordTrace tailWord_1628249 prefixEnd_1628249 836074362202705201999325 := by
  unfold tailWord_1628249
  simp only [CollatzResearch.WordTrace]
  refine ⟨59387119878139430635007801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39591413252092953756671867 59387119878139430635007801)
  ·
    refine ⟨44540339908604572976255851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59387119878139430635007801 44540339908604572976255851)
    ·
      refine ⟨66810509862906859464383777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44540339908604572976255851 66810509862906859464383777)
      ·
        refine ⟨50107882397180144598287833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66810509862906859464383777 50107882397180144598287833)
        ·
          refine ⟨37580911797885108448715875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50107882397180144598287833 37580911797885108448715875)
          ·
            refine ⟨56371367696827662673073813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37580911797885108448715875 56371367696827662673073813)
            ·
              refine ⟨2642407860788796687800335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56371367696827662673073813 2642407860788796687800335)
              ·
                refine ⟨3963611791183195031700503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642407860788796687800335 3963611791183195031700503)
                ·
                  refine ⟨5945417686774792547550755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963611791183195031700503 5945417686774792547550755)
                  ·
                    refine ⟨8918126530162188821326133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5945417686774792547550755 8918126530162188821326133)
                    ·
                      refine ⟨836074362202705201999325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8918126530162188821326133 836074362202705201999325)
                      ·
                        rfl

theorem cell23_1628249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_1628249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628249 prefixEnd_1628249 := by exact prefixLift 1628249
  have htrace : WordTrace (prefixWord ++ tailWord_1628249) baseStart_1628249 baseEnd_1628249 := by
    simpa [prefixWord, tailWord_1628249, baseEnd_1628249] using wordTrace_append hprefix tailTrace_1628249
  have hstable : (prefixWord ++ tailWord_1628249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628249).length < 2 ^ (prefixWord ++ tailWord_1628249).sum := by decide
  have hdescent : baseEnd_1628249 < baseStart_1628249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628269 : List Nat := [1, 5, 1, 1, 2, 1, 4, 8]
def baseStart_1628269 : Nat := 118140960795 + 1628269 * 2 ^ 59
def prefixEnd_1628269 : Nat := 4983230072969 + 3 ^ 40 * 1628269 * 2
def baseEnd_1628269 : Nat := 30966097474659078657379

theorem tailTrace_1628269 : CollatzResearch.WordTrace tailWord_1628269 prefixEnd_1628269 30966097474659078657379 := by
  unfold tailWord_1628269
  simp only [CollatzResearch.WordTrace]
  refine ⟨59387849338066974050735861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39591899558711316033823907 59387849338066974050735861)
  ·
    refine ⟨5567610875443778817256487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59387849338066974050735861 5567610875443778817256487)
    ·
      refine ⟨8351416313165668225884731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5567610875443778817256487 8351416313165668225884731)
      ·
        refine ⟨12527124469748502338827097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8351416313165668225884731 12527124469748502338827097)
        ·
          refine ⟨9395343352311376754120323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12527124469748502338827097 9395343352311376754120323)
          ·
            refine ⟨14093015028467065131180485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9395343352311376754120323 14093015028467065131180485)
            ·
              refine ⟨2642440317837574712096341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14093015028467065131180485 2642440317837574712096341)
              ·
                refine ⟨30966097474659078657379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2642440317837574712096341 30966097474659078657379)
                ·
                  rfl

theorem cell23_1628269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 8].length) (baseStart_1628269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628269 prefixEnd_1628269 := by exact prefixLift 1628269
  have htrace : WordTrace (prefixWord ++ tailWord_1628269) baseStart_1628269 baseEnd_1628269 := by
    simpa [prefixWord, tailWord_1628269, baseEnd_1628269] using wordTrace_append hprefix tailTrace_1628269
  have hstable : (prefixWord ++ tailWord_1628269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628269).length < 2 ^ (prefixWord ++ tailWord_1628269).sum := by decide
  have hdescent : baseEnd_1628269 < baseStart_1628269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628296 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1628296 : Nat := 118140960795 + 1628296 * 2 ^ 59
def prefixEnd_1628296 : Nat := 4983230072969 + 3 ^ 40 * 1628296 * 2
def baseEnd_1628296 : Nat := 836098495793466518111609

theorem tailTrace_1628296 : CollatzResearch.WordTrace tailWord_1628296 prefixEnd_1628296 836098495793466518111609 := by
  unfold tailWord_1628296
  simp only [CollatzResearch.WordTrace]
  refine ⟨29694417054484578830984371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39592556072646105107979161 29694417054484578830984371)
  ·
    refine ⟨44541625581726868246476557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29694417054484578830984371 44541625581726868246476557)
    ·
      refine ⟨16703109593147575592428709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44541625581726868246476557 16703109593147575592428709)
      ·
        refine ⟨3131833048715170423580383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16703109593147575592428709 3131833048715170423580383)
        ·
          refine ⟨4697749573072755635370575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131833048715170423580383 4697749573072755635370575)
          ·
            refine ⟨7046624359609133453055863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697749573072755635370575 7046624359609133453055863)
            ·
              refine ⟨10569936539413700179583795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046624359609133453055863 10569936539413700179583795)
              ·
                refine ⟨15854904809120550269375693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569936539413700179583795 15854904809120550269375693)
                ·
                  refine ⟨5945589303420206351015885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15854904809120550269375693 5945589303420206351015885)
                  ·
                    refine ⟨2229595988782577381630957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5945589303420206351015885 2229595988782577381630957)
                    ·
                      refine ⟨836098495793466518111609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2229595988782577381630957 836098495793466518111609)
                      ·
                        rfl

theorem cell23_1628296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1628296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628296 prefixEnd_1628296 := by exact prefixLift 1628296
  have htrace : WordTrace (prefixWord ++ tailWord_1628296) baseStart_1628296 baseEnd_1628296 := by
    simpa [prefixWord, tailWord_1628296, baseEnd_1628296] using wordTrace_append hprefix tailTrace_1628296
  have hstable : (prefixWord ++ tailWord_1628296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628296).length < 2 ^ (prefixWord ++ tailWord_1628296).sum := by decide
  have hdescent : baseEnd_1628296 < baseStart_1628296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628330 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1628330 : Nat := 118140960795 + 1628330 * 2 ^ 59
def prefixEnd_1628330 : Nat := 4983230072969 + 3 ^ 40 * 1628330 * 2
def baseEnd_1628330 : Nat := 836115954135719385086453

theorem tailTrace_1628330 : CollatzResearch.WordTrace tailWord_1628330 prefixEnd_1628330 836115954135719385086453 := by
  unfold tailWord_1628330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14847518547711495367176611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39593382793897320979137629 14847518547711495367176611)
  ·
    refine ⟨22271277821567243050764917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14847518547711495367176611 22271277821567243050764917)
    ·
      refine ⟨2087932295771929036009211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22271277821567243050764917 2087932295771929036009211)
      ·
        refine ⟨3131898443657893554013817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087932295771929036009211 3131898443657893554013817)
        ·
          refine ⟨2348923832743420165510363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3131898443657893554013817 2348923832743420165510363)
          ·
            refine ⟨3523385749115130248265545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348923832743420165510363 3523385749115130248265545)
            ·
              refine ⟨2642539311836347686199159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3523385749115130248265545 2642539311836347686199159)
              ·
                refine ⟨3963808967754521529298739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642539311836347686199159 3963808967754521529298739)
                ·
                  refine ⟨5945713451631782293948109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963808967754521529298739 5945713451631782293948109)
                  ·
                    refine ⟨2229642544361918360230541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5945713451631782293948109 2229642544361918360230541)
                    ·
                      refine ⟨836115954135719385086453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2229642544361918360230541 836115954135719385086453)
                      ·
                        rfl

theorem cell23_1628330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1628330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628330 prefixEnd_1628330 := by exact prefixLift 1628330
  have htrace : WordTrace (prefixWord ++ tailWord_1628330) baseStart_1628330 baseEnd_1628330 := by
    simpa [prefixWord, tailWord_1628330, baseEnd_1628330] using wordTrace_append hprefix tailTrace_1628330
  have hstable : (prefixWord ++ tailWord_1628330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628330).length < 2 ^ (prefixWord ++ tailWord_1628330).sum := by decide
  have hdescent : baseEnd_1628330 < baseStart_1628330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628339 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 3]
def baseStart_1628339 : Nat := 118140960795 + 1628339 * 2 ^ 59
def prefixEnd_1628339 : Nat := 4983230072969 + 3 ^ 40 * 1628339 * 2
def baseEnd_1628339 : Nat := 836120575461609849873911

theorem tailTrace_1628339 : CollatzResearch.WordTrace tailWord_1628339 prefixEnd_1628339 836120575461609849873911 := by
  unfold tailWord_1628339
  simp only [CollatzResearch.WordTrace]
  refine ⟨59390402447813376005784071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39593601631875584003856047 59390402447813376005784071)
  ·
    refine ⟨89085603671720064008676107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59390402447813376005784071 89085603671720064008676107)
    ·
      refine ⟨133628405507580096013014161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89085603671720064008676107 133628405507580096013014161)
      ·
        refine ⟨100221304130685072009760621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133628405507580096013014161 100221304130685072009760621)
        ·
          refine ⟨37582989049006902003660233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100221304130685072009760621 37582989049006902003660233)
          ·
            refine ⟨28187241786755176502745175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37582989049006902003660233 28187241786755176502745175)
            ·
              refine ⟨42280862680132764754117763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28187241786755176502745175 42280862680132764754117763)
              ·
                refine ⟨63421294020199147131176645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42280862680132764754117763 63421294020199147131176645)
                ·
                  refine ⟨11891492628787340087095621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63421294020199147131176645 11891492628787340087095621)
                  ·
                    refine ⟨2229654867897626266330429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11891492628787340087095621 2229654867897626266330429)
                    ·
                      refine ⟨836120575461609849873911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2229654867897626266330429 836120575461609849873911)
                      ·
                        rfl

theorem cell23_1628339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_1628339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628339 prefixEnd_1628339 := by exact prefixLift 1628339
  have htrace : WordTrace (prefixWord ++ tailWord_1628339) baseStart_1628339 baseEnd_1628339 := by
    simpa [prefixWord, tailWord_1628339, baseEnd_1628339] using wordTrace_append hprefix tailTrace_1628339
  have hstable : (prefixWord ++ tailWord_1628339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628339).length < 2 ^ (prefixWord ++ tailWord_1628339).sum := by decide
  have hdescent : baseEnd_1628339 < baseStart_1628339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628349 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1628349 : Nat := 118140960795 + 1628349 * 2 ^ 59
def prefixEnd_1628349 : Nat := 4983230072969 + 3 ^ 40 * 1628349 * 2
def baseEnd_1628349 : Nat := 836125710268154810748865

theorem tailTrace_1628349 : CollatzResearch.WordTrace tailWord_1628349 prefixEnd_1628349 836125710268154810748865 := by
  unfold tailWord_1628349
  simp only [CollatzResearch.WordTrace]
  refine ⟨59390767177777147713648101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39593844785184765142432067 59390767177777147713648101)
  ·
    refine ⟨11135768845833215196309019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59390767177777147713648101 11135768845833215196309019)
    ·
      refine ⟨16703653268749822794463529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11135768845833215196309019 16703653268749822794463529)
      ·
        refine ⟨12527739951562367095847647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16703653268749822794463529 12527739951562367095847647)
        ·
          refine ⟨18791609927343550643771471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12527739951562367095847647 18791609927343550643771471)
          ·
            refine ⟨28187414891015325965657207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18791609927343550643771471 28187414891015325965657207)
            ·
              refine ⟨42281122336522988948485811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28187414891015325965657207 42281122336522988948485811)
              ·
                refine ⟨63421683504784483422728717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42281122336522988948485811 63421683504784483422728717)
                ·
                  refine ⟨23783131314294181283523269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63421683504784483422728717 23783131314294181283523269)
                  ·
                    refine ⟨4459337121430158990660613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23783131314294181283523269 4459337121430158990660613)
                    ·
                      refine ⟨836125710268154810748865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4459337121430158990660613 836125710268154810748865)
                      ·
                        rfl

theorem cell23_1628349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1628349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628349 prefixEnd_1628349 := by exact prefixLift 1628349
  have htrace : WordTrace (prefixWord ++ tailWord_1628349) baseStart_1628349 baseEnd_1628349 := by
    simpa [prefixWord, tailWord_1628349, baseEnd_1628349] using wordTrace_append hprefix tailTrace_1628349
  have hstable : (prefixWord ++ tailWord_1628349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628349).length < 2 ^ (prefixWord ++ tailWord_1628349).sum := by decide
  have hdescent : baseEnd_1628349 < baseStart_1628349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628364 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1628364 : Nat := 118140960795 + 1628364 * 2 ^ 59
def prefixEnd_1628364 : Nat := 4983230072969 + 3 ^ 40 * 1628364 * 2
def baseEnd_1628364 : Nat := 836133412477972252061297

theorem tailTrace_1628364 : CollatzResearch.WordTrace tailWord_1628364 prefixEnd_1628364 836133412477972252061297 := by
  unfold tailWord_1628364
  simp only [CollatzResearch.WordTrace]
  refine ⟨29695657136361402637722073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39594209515148536850296097 29695657136361402637722073)
  ·
    refine ⟨22271742852271051978291555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29695657136361402637722073 22271742852271051978291555)
    ·
      refine ⟨33407614278406577967437333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22271742852271051978291555 33407614278406577967437333)
      ·
        refine ⟨1565981919300308342223625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33407614278406577967437333 1565981919300308342223625)
        ·
          refine ⟨1174486439475231256667719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565981919300308342223625 1174486439475231256667719)
          ·
            refine ⟨1761729659212846885001579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174486439475231256667719 1761729659212846885001579)
            ·
              refine ⟨2642594488819270327502369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761729659212846885001579 2642594488819270327502369)
              ·
                refine ⟨1981945866614452745626777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642594488819270327502369 1981945866614452745626777)
                ·
                  refine ⟨1486459399960839559220083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1981945866614452745626777 1486459399960839559220083)
                  ·
                    refine ⟨2229689099941259338830125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1486459399960839559220083 2229689099941259338830125)
                    ·
                      refine ⟨836133412477972252061297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2229689099941259338830125 836133412477972252061297)
                      ·
                        rfl

theorem cell23_1628364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1628364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628364 prefixEnd_1628364 := by exact prefixLift 1628364
  have htrace : WordTrace (prefixWord ++ tailWord_1628364) baseStart_1628364 baseEnd_1628364 := by
    simpa [prefixWord, tailWord_1628364, baseEnd_1628364] using wordTrace_append hprefix tailTrace_1628364
  have hstable : (prefixWord ++ tailWord_1628364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628364).length < 2 ^ (prefixWord ++ tailWord_1628364).sum := by decide
  have hdescent : baseEnd_1628364 < baseStart_1628364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628366 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1628366 : Nat := 118140960795 + 1628366 * 2 ^ 59
def prefixEnd_1628366 : Nat := 4983230072969 + 3 ^ 40 * 1628366 * 2
def baseEnd_1628366 : Nat := 836134439439281244236287

theorem tailTrace_1628366 : CollatzResearch.WordTrace tailWord_1628366 prefixEnd_1628366 836134439439281244236287 := by
  unfold tailWord_1628366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423923402339444952127119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39594258145810373078011301 7423923402339444952127119)
  ·
    refine ⟨11135885103509167428190679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7423923402339444952127119 11135885103509167428190679)
    ·
      refine ⟨16703827655263751142286019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11135885103509167428190679 16703827655263751142286019)
      ·
        refine ⟨25055741482895626713429029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16703827655263751142286019 25055741482895626713429029)
        ·
          refine ⟨4697951528042930008767943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25055741482895626713429029 4697951528042930008767943)
          ·
            refine ⟨7046927292064395013151915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697951528042930008767943 7046927292064395013151915)
            ·
              refine ⟨10570390938096592519727873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046927292064395013151915 10570390938096592519727873)
              ·
                refine ⟨7927793203572444389795905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10570390938096592519727873 7927793203572444389795905)
                ·
                  refine ⟨5945844902679333292346929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927793203572444389795905 5945844902679333292346929)
                  ·
                    refine ⟨4459383677009499969260197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5945844902679333292346929 4459383677009499969260197)
                    ·
                      refine ⟨836134439439281244236287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4459383677009499969260197 836134439439281244236287)
                      ·
                        rfl

theorem cell23_1628366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1628366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628366 prefixEnd_1628366 := by exact prefixLift 1628366
  have htrace : WordTrace (prefixWord ++ tailWord_1628366) baseStart_1628366 baseEnd_1628366 := by
    simpa [prefixWord, tailWord_1628366, baseEnd_1628366] using wordTrace_append hprefix tailTrace_1628366
  have hstable : (prefixWord ++ tailWord_1628366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628366).length < 2 ^ (prefixWord ++ tailWord_1628366).sum := by decide
  have hdescent : baseEnd_1628366 < baseStart_1628366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628370 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1628370 : Nat := 118140960795 + 1628370 * 2 ^ 59
def prefixEnd_1628370 : Nat := 4983230072969 + 3 ^ 40 * 1628370 * 2
def baseEnd_1628370 : Nat := 836136493361899228586269

theorem tailTrace_1628370 : CollatzResearch.WordTrace tailWord_1628370 prefixEnd_1628370 836136493361899228586269 := by
  unfold tailWord_1628370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14847883277675267075040641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39594355407134045533441709 14847883277675267075040641)
  ·
    refine ⟨11135912458256450306280481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14847883277675267075040641 11135912458256450306280481)
    ·
      refine ⟨8351934343692337729710361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11135912458256450306280481 8351934343692337729710361)
      ·
        refine ⟨6263950757769253297282771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8351934343692337729710361 6263950757769253297282771)
        ·
          refine ⟨9395926136653879945924157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263950757769253297282771 9395926136653879945924157)
          ·
            refine ⟨3523472301245204979721559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9395926136653879945924157 3523472301245204979721559)
            ·
              refine ⟨5285208451867807469582339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523472301245204979721559 5285208451867807469582339)
              ·
                refine ⟨7927812677801711204373509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285208451867807469582339 7927812677801711204373509)
                ·
                  refine ⟨1486464877087820850820033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7927812677801711204373509 1486464877087820850820033)
                  ·
                    refine ⟨1114848657815865638115025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1486464877087820850820033 1114848657815865638115025)
                    ·
                      refine ⟨836136493361899228586269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114848657815865638115025 836136493361899228586269)
                      ·
                        rfl

theorem cell23_1628370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1628370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628370 prefixEnd_1628370 := by exact prefixLift 1628370
  have htrace : WordTrace (prefixWord ++ tailWord_1628370) baseStart_1628370 baseEnd_1628370 := by
    simpa [prefixWord, tailWord_1628370, baseEnd_1628370] using wordTrace_append hprefix tailTrace_1628370
  have hstable : (prefixWord ++ tailWord_1628370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628370).length < 2 ^ (prefixWord ++ tailWord_1628370).sum := by decide
  have hdescent : baseEnd_1628370 < baseStart_1628370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628376 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 7]
def baseStart_1628376 : Nat := 118140960795 + 1628376 * 2 ^ 59
def prefixEnd_1628376 : Nat := 4983230072969 + 3 ^ 40 * 1628376 * 2
def baseEnd_1628376 : Nat := 92904397138425133901249

theorem tailTrace_1628376 : CollatzResearch.WordTrace tailWord_1628376 prefixEnd_1628376 92904397138425133901249 := by
  unfold tailWord_1628376
  simp only [CollatzResearch.WordTrace]
  refine ⟨29695875974339665662440491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39594501299119554216587321 29695875974339665662440491)
  ·
    refine ⟨44543813961509498493660737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29695875974339665662440491 44543813961509498493660737)
    ·
      refine ⟨33407860471132123870245553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44543813961509498493660737 33407860471132123870245553)
      ·
        refine ⟨25055895353349092902684165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33407860471132123870245553 25055895353349092902684165)
        ·
          refine ⟨4697980378752954919253281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25055895353349092902684165 4697980378752954919253281)
          ·
            refine ⟨3523485284064716189439961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4697980378752954919253281 3523485284064716189439961)
            ·
              refine ⟨2642613963048537142079971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3523485284064716189439961 2642613963048537142079971)
              ·
                refine ⟨3963920944572805713119957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642613963048537142079971 3963920944572805713119957)
                ·
                  refine ⟨92904397138425133901249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3963920944572805713119957 92904397138425133901249)
                  ·
                    rfl

theorem cell23_1628376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 7].length) (baseStart_1628376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628376 prefixEnd_1628376 := by exact prefixLift 1628376
  have htrace : WordTrace (prefixWord ++ tailWord_1628376) baseStart_1628376 baseEnd_1628376 := by
    simpa [prefixWord, tailWord_1628376, baseEnd_1628376] using wordTrace_append hprefix tailTrace_1628376
  have hstable : (prefixWord ++ tailWord_1628376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628376).length < 2 ^ (prefixWord ++ tailWord_1628376).sum := by decide
  have hdescent : baseEnd_1628376 < baseStart_1628376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628387 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1628387 : Nat := 118140960795 + 1628387 * 2 ^ 59
def prefixEnd_1628387 : Nat := 4983230072969 + 3 ^ 40 * 1628387 * 2
def baseEnd_1628387 : Nat := 836145222533025662073691

theorem tailTrace_1628387 : CollatzResearch.WordTrace tailWord_1628387 prefixEnd_1628387 836145222533025662073691 := by
  unfold tailWord_1628387
  simp only [CollatzResearch.WordTrace]
  refine ⟨59392153151639480203531415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39594768767759653469020943 59392153151639480203531415)
  ·
    refine ⟨89088229727459220305297123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59392153151639480203531415 89088229727459220305297123)
    ·
      refine ⟨133632344591188830457945685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89088229727459220305297123 133632344591188830457945685)
      ·
        refine ⟨1566004038177994106929051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 133632344591188830457945685 1566004038177994106929051)
        ·
          refine ⟨2349006057266991160393577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566004038177994106929051 2349006057266991160393577)
          ·
            refine ⟨1761754542950243370295183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2349006057266991160393577 1761754542950243370295183)
            ·
              refine ⟨2642631814425365055442775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761754542950243370295183 2642631814425365055442775)
              ·
                refine ⟨3963947721638047583164163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642631814425365055442775 3963947721638047583164163)
                ·
                  refine ⟨5945921582457071374746245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963947721638047583164163 5945921582457071374746245)
                  ·
                    refine ⟨1114860296710700882764921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945921582457071374746245 1114860296710700882764921)
                    ·
                      refine ⟨836145222533025662073691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114860296710700882764921 836145222533025662073691)
                      ·
                        rfl

theorem cell23_1628387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1628387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628387 prefixEnd_1628387 := by exact prefixLift 1628387
  have htrace : WordTrace (prefixWord ++ tailWord_1628387) baseStart_1628387 baseEnd_1628387 := by
    simpa [prefixWord, tailWord_1628387, baseEnd_1628387] using wordTrace_append hprefix tailTrace_1628387
  have hstable : (prefixWord ++ tailWord_1628387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628387).length < 2 ^ (prefixWord ++ tailWord_1628387).sum := by decide
  have hdescent : baseEnd_1628387 < baseStart_1628387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628406 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1628406 : Nat := 118140960795 + 1628406 * 2 ^ 59
def prefixEnd_1628406 : Nat := 4983230072969 + 3 ^ 40 * 1628406 * 2
def baseEnd_1628406 : Nat := 278718326221820362578701

theorem tailTrace_1628406 : CollatzResearch.WordTrace tailWord_1628406 prefixEnd_1628406 278718326221820362578701 := by
  unfold tailWord_1628406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712052883660665403029567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39595230759047097632315381 3712052883660665403029567)
  ·
    refine ⟨5568079325490998104544351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712052883660665403029567 5568079325490998104544351)
    ·
      refine ⟨8352118988236497156816527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568079325490998104544351 8352118988236497156816527)
      ·
        refine ⟨12528178482354745735224791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352118988236497156816527 12528178482354745735224791)
        ·
          refine ⟨18792267723532118602837187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528178482354745735224791 18792267723532118602837187)
          ·
            refine ⟨28188401585298177904255781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18792267723532118602837187 28188401585298177904255781)
            ·
              refine ⟨5285325297243408357047959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28188401585298177904255781 5285325297243408357047959)
              ·
                refine ⟨7927987945865112535571939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285325297243408357047959 7927987945865112535571939)
                ·
                  refine ⟨11891981918797668803357909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7927987945865112535571939 11891981918797668803357909)
                  ·
                    refine ⟨278718326221820362578701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11891981918797668803357909 278718326221820362578701)
                    ·
                      rfl

theorem cell23_1628406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1628406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628406 prefixEnd_1628406 := by exact prefixLift 1628406
  have htrace : WordTrace (prefixWord ++ tailWord_1628406) baseStart_1628406 baseEnd_1628406 := by
    simpa [prefixWord, tailWord_1628406, baseEnd_1628406] using wordTrace_append hprefix tailTrace_1628406
  have hstable : (prefixWord ++ tailWord_1628406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628406).length < 2 ^ (prefixWord ++ tailWord_1628406).sum := by decide
  have hdescent : baseEnd_1628406 < baseStart_1628406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628426 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1628426 : Nat := 118140960795 + 1628426 * 2 ^ 59
def prefixEnd_1628426 : Nat := 4983230072969 + 3 ^ 40 * 1628426 * 2
def baseEnd_1628426 : Nat := 836165248278551009486011

theorem tailTrace_1628426 : CollatzResearch.WordTrace tailWord_1628426 prefixEnd_1628426 836165248278551009486011 := by
  unfold tailWord_1628426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848393899624547466050283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39595717065665459909467421 14848393899624547466050283)
  ·
    refine ⟨22272590849436821199075425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14848393899624547466050283 22272590849436821199075425)
    ·
      refine ⟨16704443137077615899306569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22272590849436821199075425 16704443137077615899306569)
      ·
        refine ⟨12528332352808211924479927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16704443137077615899306569 12528332352808211924479927)
        ·
          refine ⟨18792498529212317886719891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528332352808211924479927 18792498529212317886719891)
          ·
            refine ⟨28188747793818476830079837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18792498529212317886719891 28188747793818476830079837)
            ·
              refine ⟨10570780422681928811279939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28188747793818476830079837 10570780422681928811279939)
              ·
                refine ⟨15856170634022893216919909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10570780422681928811279939 15856170634022893216919909)
                ·
                  refine ⟨2973031993879292478172483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15856170634022893216919909 2973031993879292478172483)
                  ·
                    refine ⟨4459547990818938717258725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2973031993879292478172483 4459547990818938717258725)
                    ·
                      refine ⟨836165248278551009486011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4459547990818938717258725 836165248278551009486011)
                      ·
                        rfl

theorem cell23_1628426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1628426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628426 prefixEnd_1628426 := by exact prefixLift 1628426
  have htrace : WordTrace (prefixWord ++ tailWord_1628426) baseStart_1628426 baseEnd_1628426 := by
    simpa [prefixWord, tailWord_1628426, baseEnd_1628426] using wordTrace_append hprefix tailTrace_1628426
  have hstable : (prefixWord ++ tailWord_1628426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628426).length < 2 ^ (prefixWord ++ tailWord_1628426).sum := by decide
  have hdescent : baseEnd_1628426 < baseStart_1628426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628496 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_1628496 : Nat := 118140960795 + 1628496 * 2 ^ 59
def prefixEnd_1628496 : Nat := 4983230072969 + 3 ^ 40 * 1628496 * 2
def baseEnd_1628496 : Nat := 278733730641455245203563

theorem tailTrace_1628496 : CollatzResearch.WordTrace tailWord_1628496 prefixEnd_1628496 278733730641455245203563 := by
  unfold tailWord_1628496
  simp only [CollatzResearch.WordTrace]
  refine ⟨29698064354122295909624671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39597419138829727879499561 29698064354122295909624671)
  ·
    refine ⟨44547096531183443864437007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29698064354122295909624671 44547096531183443864437007)
    ·
      refine ⟨66820644796775165796655511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44547096531183443864437007 66820644796775165796655511)
      ·
        refine ⟨100230967195162748694983267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66820644796775165796655511 100230967195162748694983267)
        ·
          refine ⟨150346450792744123042474901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100230967195162748694983267 150346450792744123042474901)
          ·
            refine ⟨7047489880909880767616011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150346450792744123042474901 7047489880909880767616011)
            ·
              refine ⟨10571234821364821151424017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7047489880909880767616011 10571234821364821151424017)
              ·
                refine ⟨7928426116023615863568013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10571234821364821151424017 7928426116023615863568013)
                ·
                  refine ⟨2973159793508855948838005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7928426116023615863568013 2973159793508855948838005)
                  ·
                    refine ⟨278733730641455245203563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2973159793508855948838005 278733730641455245203563)
                    ·
                      rfl

theorem cell23_1628496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_1628496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628496 prefixEnd_1628496 := by exact prefixLift 1628496
  have htrace : WordTrace (prefixWord ++ tailWord_1628496) baseStart_1628496 baseEnd_1628496 := by
    simpa [prefixWord, tailWord_1628496, baseEnd_1628496] using wordTrace_append hprefix tailTrace_1628496
  have hstable : (prefixWord ++ tailWord_1628496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628496).length < 2 ^ (prefixWord ++ tailWord_1628496).sum := by decide
  have hdescent : baseEnd_1628496 < baseStart_1628496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628503 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 1, 5, 2]
def baseStart_1628503 : Nat := 118140960795 + 1628503 * 2 ^ 59
def prefixEnd_1628503 : Nat := 4983230072969 + 3 ^ 40 * 1628503 * 2
def baseEnd_1628503 : Nat := 836204786288947208223157

theorem tailTrace_1628503 : CollatzResearch.WordTrace tailWord_1628503 prefixEnd_1628503 836204786288947208223157 := by
  unfold tailWord_1628503
  simp only [CollatzResearch.WordTrace]
  refine ⟨59396384019219232014754163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39597589346146154676502775 59396384019219232014754163)
  ·
    refine ⟨89094576028828848022131245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59396384019219232014754163 89094576028828848022131245)
    ·
      refine ⟨33410466010810818008299217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89094576028828848022131245 33410466010810818008299217)
      ·
        refine ⟨25057849508108113506224413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33410466010810818008299217 25057849508108113506224413)
        ·
          refine ⟨9396693565540542564834155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25057849508108113506224413 9396693565540542564834155)
          ·
            refine ⟨14095040348310813847251233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396693565540542564834155 14095040348310813847251233)
            ·
              refine ⟨10571280261233110385438425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14095040348310813847251233 10571280261233110385438425)
              ·
                refine ⟨7928460195924832789078819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10571280261233110385438425 7928460195924832789078819)
                ·
                  refine ⟨11892690293887249183618229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7928460195924832789078819 11892690293887249183618229)
                  ·
                    refine ⟨1114939715051929610964209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11892690293887249183618229 1114939715051929610964209)
                    ·
                      refine ⟨836204786288947208223157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114939715051929610964209 836204786288947208223157)
                      ·
                        rfl

theorem cell23_1628503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_1628503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628503 prefixEnd_1628503 := by exact prefixLift 1628503
  have htrace : WordTrace (prefixWord ++ tailWord_1628503) baseStart_1628503 baseEnd_1628503 := by
    simpa [prefixWord, tailWord_1628503, baseEnd_1628503] using wordTrace_append hprefix tailTrace_1628503
  have hstable : (prefixWord ++ tailWord_1628503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628503).length < 2 ^ (prefixWord ++ tailWord_1628503).sum := by decide
  have hdescent : baseEnd_1628503 < baseStart_1628503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628520 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1628520 : Nat := 118140960795 + 1628520 * 2 ^ 59
def prefixEnd_1628520 : Nat := 4983230072969 + 3 ^ 40 * 1628520 * 2
def baseEnd_1628520 : Nat := 836213515460073641710579

theorem tailTrace_1628520 : CollatzResearch.WordTrace tailWord_1628520 prefixEnd_1628520 836213515460073641710579 := by
  unfold tailWord_1628520
  simp only [CollatzResearch.WordTrace]
  refine ⟨29698502030078821959061507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39598002706771762612082009 29698502030078821959061507)
  ·
    refine ⟨44547753045118232938592261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29698502030078821959061507 44547753045118232938592261)
    ·
      refine ⟨8352703695959668675986049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44547753045118232938592261 8352703695959668675986049)
      ·
        refine ⟨6264527771969751506989537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8352703695959668675986049 6264527771969751506989537)
        ·
          refine ⟨4698395828977313630242153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264527771969751506989537 4698395828977313630242153)
          ·
            refine ⟨3523796871732985222681615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698395828977313630242153 3523796871732985222681615)
            ·
              refine ⟨5285695307599477834022423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523796871732985222681615 5285695307599477834022423)
              ·
                refine ⟨7928542961399216751033635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285695307599477834022423 7928542961399216751033635)
                ·
                  refine ⟨11892814442098825126550453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7928542961399216751033635 11892814442098825126550453)
                  ·
                    refine ⟨1114951353946764855614105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11892814442098825126550453 1114951353946764855614105)
                    ·
                      refine ⟨836213515460073641710579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1114951353946764855614105 836213515460073641710579)
                      ·
                        rfl

theorem cell23_1628520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1628520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628520 prefixEnd_1628520 := by exact prefixLift 1628520
  have htrace : WordTrace (prefixWord ++ tailWord_1628520) baseStart_1628520 baseEnd_1628520 := by
    simpa [prefixWord, tailWord_1628520, baseEnd_1628520] using wordTrace_append hprefix tailTrace_1628520
  have hstable : (prefixWord ++ tailWord_1628520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628520).length < 2 ^ (prefixWord ++ tailWord_1628520).sum := by decide
  have hdescent : baseEnd_1628520 < baseStart_1628520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628530 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_1628530 : Nat := 118140960795 + 1628530 * 2 ^ 59
def prefixEnd_1628530 : Nat := 4983230072969 + 3 ^ 40 * 1628530 * 2
def baseEnd_1628530 : Nat := 278739550088872867528511

theorem tailTrace_1628530 : CollatzResearch.WordTrace tailWord_1628530 prefixEnd_1628530 278739550088872867528511 := by
  unfold tailWord_1628530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14849342197530353906496761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39598245860080943750658029 14849342197530353906496761)
  ·
    refine ⟨11137006648147765429872571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14849342197530353906496761 11137006648147765429872571)
    ·
      refine ⟨16705509972221648144808857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11137006648147765429872571 16705509972221648144808857)
      ·
        refine ⟨12529132479166236108606643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16705509972221648144808857 12529132479166236108606643)
        ·
          refine ⟨18793698718749354162909965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12529132479166236108606643 18793698718749354162909965)
          ·
            refine ⟨7047637019531007811091237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18793698718749354162909965 7047637019531007811091237)
            ·
              refine ⟨1321431941162063964579607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7047637019531007811091237 1321431941162063964579607)
              ·
                refine ⟨1982147911743095946869411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321431941162063964579607 1982147911743095946869411)
                ·
                  refine ⟨2973221867614643920304117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982147911743095946869411 2973221867614643920304117)
                  ·
                    refine ⟨278739550088872867528511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2973221867614643920304117 278739550088872867528511)
                    ·
                      rfl

theorem cell23_1628530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_1628530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628530 prefixEnd_1628530 := by exact prefixLift 1628530
  have htrace : WordTrace (prefixWord ++ tailWord_1628530) baseStart_1628530 baseEnd_1628530 := by
    simpa [prefixWord, tailWord_1628530, baseEnd_1628530] using wordTrace_append hprefix tailTrace_1628530
  have hstable : (prefixWord ++ tailWord_1628530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628530).length < 2 ^ (prefixWord ++ tailWord_1628530).sum := by decide
  have hdescent : baseEnd_1628530 < baseStart_1628530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628534 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_1628534 : Nat := 118140960795 + 1628534 * 2 ^ 59
def prefixEnd_1628534 : Nat := 4983230072969 + 3 ^ 40 * 1628534 * 2
def baseEnd_1628534 : Nat := 92913411576581842992835

theorem tailTrace_1628534 : CollatzResearch.WordTrace tailWord_1628534 prefixEnd_1628534 92913411576581842992835 := by
  unfold tailWord_1628534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712344667631682769320791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39598343121404616206088437 3712344667631682769320791)
  ·
    refine ⟨5568517001447524153981187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712344667631682769320791 5568517001447524153981187)
    ·
      refine ⟨8352775502171286230971781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568517001447524153981187 8352775502171286230971781)
      ·
        refine ⟨1566145406657116168307209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8352775502171286230971781 1566145406657116168307209)
        ·
          refine ⟨1174609054992837126230407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566145406657116168307209 1174609054992837126230407)
          ·
            refine ⟨1761913582489255689345611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174609054992837126230407 1761913582489255689345611)
            ·
              refine ⟨2642870373733883534018417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761913582489255689345611 2642870373733883534018417)
              ·
                refine ⟨1982152780300412650513813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642870373733883534018417 1982152780300412650513813)
                ·
                  refine ⟨92913411576581842992835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1982152780300412650513813 92913411576581842992835)
                  ·
                    rfl

theorem cell23_1628534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_1628534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628534 prefixEnd_1628534 := by exact prefixLift 1628534
  have htrace : WordTrace (prefixWord ++ tailWord_1628534) baseStart_1628534 baseEnd_1628534 := by
    simpa [prefixWord, tailWord_1628534, baseEnd_1628534] using wordTrace_append hprefix tailTrace_1628534
  have hstable : (prefixWord ++ tailWord_1628534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628534).length < 2 ^ (prefixWord ++ tailWord_1628534).sum := by decide
  have hdescent : baseEnd_1628534 < baseStart_1628534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628553 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_1628553 : Nat := 118140960795 + 1628553 * 2 ^ 59
def prefixEnd_1628553 : Nat := 4983230072969 + 3 ^ 40 * 1628553 * 2
def baseEnd_1628553 : Nat := 836230460321672012597927

theorem tailTrace_1628553 : CollatzResearch.WordTrace tailWord_1628553 prefixEnd_1628553 836230460321672012597927 := by
  unfold tailWord_1628553
  simp only [CollatzResearch.WordTrace]
  refine ⟨59398207669038090554074313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39598805112692060369382875 59398207669038090554074313)
  ·
    refine ⟨44548655751778567915555735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59398207669038090554074313 44548655751778567915555735)
    ·
      refine ⟨66822983627667851873333603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44548655751778567915555735 66822983627667851873333603)
      ·
        refine ⟨100234475441501777810000405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66822983627667851873333603 100234475441501777810000405)
        ·
          refine ⟨4698491036320395834843769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100234475441501777810000405 4698491036320395834843769)
          ·
            refine ⟨3523868277240296876132827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698491036320395834843769 3523868277240296876132827)
            ·
              refine ⟨5285802415860445314199241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523868277240296876132827 5285802415860445314199241)
              ·
                refine ⟨3964351811895333985649431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285802415860445314199241 3964351811895333985649431)
                ·
                  refine ⟨5946527717843000978474147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964351811895333985649431 5946527717843000978474147)
                  ·
                    refine ⟨8919791576764501467711221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5946527717843000978474147 8919791576764501467711221)
                    ·
                      refine ⟨836230460321672012597927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8919791576764501467711221 836230460321672012597927)
                      ·
                        rfl

theorem cell23_1628553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_1628553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628553 prefixEnd_1628553 := by exact prefixLift 1628553
  have htrace : WordTrace (prefixWord ++ tailWord_1628553) baseStart_1628553 baseEnd_1628553 := by
    simpa [prefixWord, tailWord_1628553, baseEnd_1628553] using wordTrace_append hprefix tailTrace_1628553
  have hstable : (prefixWord ++ tailWord_1628553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628553).length < 2 ^ (prefixWord ++ tailWord_1628553).sum := by decide
  have hdescent : baseEnd_1628553 < baseStart_1628553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628570 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1628570 : Nat := 118140960795 + 1628570 * 2 ^ 59
def prefixEnd_1628570 : Nat := 4983230072969 + 3 ^ 40 * 1628570 * 2
def baseEnd_1628570 : Nat := 836239189492798446085349

theorem tailTrace_1628570 : CollatzResearch.WordTrace tailWord_1628570 prefixEnd_1628570 836239189492798446085349 := by
  unfold tailWord_1628570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14849706927494125614360791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39599218473317668304962109 14849706927494125614360791)
  ·
    refine ⟨22274560391241188421541187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14849706927494125614360791 22274560391241188421541187)
    ·
      refine ⟨33411840586861782632311781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22274560391241188421541187 33411840586861782632311781)
      ·
        refine ⟨6264720110036584243558459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33411840586861782632311781 6264720110036584243558459)
        ·
          refine ⟨9397080165054876365337689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264720110036584243558459 9397080165054876365337689)
          ·
            refine ⟨7047810123791157274003267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9397080165054876365337689 7047810123791157274003267)
            ·
              refine ⟨10571715185686735911004901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7047810123791157274003267 10571715185686735911004901)
              ·
                refine ⟨1982196597316262983313419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10571715185686735911004901 1982196597316262983313419)
                ·
                  refine ⟨2973294895974394474970129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982196597316262983313419 2973294895974394474970129)
                  ·
                    refine ⟨2229971171980795856227597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973294895974394474970129 2229971171980795856227597)
                    ·
                      refine ⟨836239189492798446085349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2229971171980795856227597 836239189492798446085349)
                      ·
                        rfl

theorem cell23_1628570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1628570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628570 prefixEnd_1628570 := by exact prefixLift 1628570
  have htrace : WordTrace (prefixWord ++ tailWord_1628570) baseStart_1628570 baseEnd_1628570 := by
    simpa [prefixWord, tailWord_1628570, baseEnd_1628570] using wordTrace_append hprefix tailTrace_1628570
  have hstable : (prefixWord ++ tailWord_1628570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628570).length < 2 ^ (prefixWord ++ tailWord_1628570).sum := by decide
  have hdescent : baseEnd_1628570 < baseStart_1628570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628573 : List Nat := [1, 4, 2, 1, 4, 1, 1, 9]
def baseStart_1628573 : Nat := 118140960795 + 1628573 * 2 ^ 59
def prefixEnd_1628573 : Nat := 4983230072969 + 3 ^ 40 * 1628573 * 2
def baseEnd_1628573 : Nat := 30971878886472664235105

theorem tailTrace_1628573 : CollatzResearch.WordTrace tailWord_1628573 prefixEnd_1628573 30971878886472664235105 := by
  unfold tailWord_1628573
  simp only [CollatzResearch.WordTrace]
  refine ⟨59398937128965633969802373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39599291419310422646534915 59398937128965633969802373)
  ·
    refine ⟨11137300711681056369337945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59398937128965633969802373 11137300711681056369337945)
    ·
      refine ⟨8352975533760792277003459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11137300711681056369337945 8352975533760792277003459)
      ·
        refine ⟨12529463300641188415505189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352975533760792277003459 12529463300641188415505189)
        ·
          refine ⟨2349274368870222827907223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12529463300641188415505189 2349274368870222827907223)
          ·
            refine ⟨3523911553305334241860835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349274368870222827907223 3523911553305334241860835)
            ·
              refine ⟨5285867329958001362791253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523911553305334241860835 5285867329958001362791253)
              ·
                refine ⟨30971878886472664235105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5285867329958001362791253 30971878886472664235105)
                ·
                  rfl

theorem cell23_1628573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 9].length) (baseStart_1628573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628573 prefixEnd_1628573 := by exact prefixLift 1628573
  have htrace : WordTrace (prefixWord ++ tailWord_1628573) baseStart_1628573 baseEnd_1628573 := by
    simpa [prefixWord, tailWord_1628573, baseEnd_1628573] using wordTrace_append hprefix tailTrace_1628573
  have hstable : (prefixWord ++ tailWord_1628573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628573).length < 2 ^ (prefixWord ++ tailWord_1628573).sum := by decide
  have hdescent : baseEnd_1628573 < baseStart_1628573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628600 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_1628600 : Nat := 118140960795 + 1628600 * 2 ^ 59
def prefixEnd_1628600 : Nat := 4983230072969 + 3 ^ 40 * 1628600 * 2
def baseEnd_1628600 : Nat := 836254593912433328710211

theorem tailTrace_1628600 : CollatzResearch.WordTrace tailWord_1628600 prefixEnd_1628600 836254593912433328710211 := by
  unfold tailWord_1628600
  simp only [CollatzResearch.WordTrace]
  refine ⟨29699960949933908790517627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39599947933245211720690169 29699960949933908790517627)
  ·
    refine ⟨44549941424900863185776441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29699960949933908790517627 44549941424900863185776441)
    ·
      refine ⟨33412456068675647389332331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44549941424900863185776441 33412456068675647389332331)
      ·
        refine ⟨50118684103013471083998497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33412456068675647389332331 50118684103013471083998497)
        ·
          refine ⟨37589013077260103312998873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50118684103013471083998497 37589013077260103312998873)
          ·
            refine ⟨28191759807945077484749155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37589013077260103312998873 28191759807945077484749155)
            ·
              refine ⟨42287639711917616227123733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28191759807945077484749155 42287639711917616227123733)
              ·
                refine ⟨1982233111496138260646425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42287639711917616227123733 1982233111496138260646425)
                ·
                  refine ⟨1486674833622103695484819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982233111496138260646425 1486674833622103695484819)
                  ·
                    refine ⟨2230012250433155543227229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1486674833622103695484819 2230012250433155543227229)
                    ·
                      refine ⟨836254593912433328710211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230012250433155543227229 836254593912433328710211)
                      ·
                        rfl

theorem cell23_1628600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_1628600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628600 prefixEnd_1628600 := by exact prefixLift 1628600
  have htrace : WordTrace (prefixWord ++ tailWord_1628600) baseStart_1628600 baseEnd_1628600 := by
    simpa [prefixWord, tailWord_1628600, baseEnd_1628600] using wordTrace_append hprefix tailTrace_1628600
  have hstable : (prefixWord ++ tailWord_1628600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628600).length < 2 ^ (prefixWord ++ tailWord_1628600).sum := by decide
  have hdescent : baseEnd_1628600 < baseStart_1628600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628601 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 1, 2, 2]
def baseStart_1628601 : Nat := 118140960795 + 1628601 * 2 ^ 59
def prefixEnd_1628601 : Nat := 4983230072969 + 3 ^ 40 * 1628601 * 2
def baseEnd_1628601 : Nat := 836255107393087824797707

theorem tailTrace_1628601 : CollatzResearch.WordTrace tailWord_1628601 prefixEnd_1628601 836255107393087824797707 := by
  unfold tailWord_1628601
  simp only [CollatzResearch.WordTrace]
  refine ⟨59399958372864194751821657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39599972248576129834547771 59399958372864194751821657)
  ·
    refine ⟨44549968779648146063866243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59399958372864194751821657 44549968779648146063866243)
    ·
      refine ⟨66824953169472219095799365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44549968779648146063866243 66824953169472219095799365)
      ·
        refine ⟨12529678719276041080462381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66824953169472219095799365 12529678719276041080462381)
        ·
          refine ⟨4698629519728515405173393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12529678719276041080462381 4698629519728515405173393)
          ·
            refine ⟨3523972139796386553880045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698629519728515405173393 3523972139796386553880045)
            ·
              refine ⟨1321489552423644957705017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3523972139796386553880045 1321489552423644957705017)
              ·
                refine ⟨991117164317733718278763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321489552423644957705017 991117164317733718278763)
                ·
                  refine ⟨1486675746476600577418145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991117164317733718278763 1486675746476600577418145)
                  ·
                    refine ⟨1115006809857450433063609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1486675746476600577418145 1115006809857450433063609)
                    ·
                      refine ⟨836255107393087824797707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115006809857450433063609 836255107393087824797707)
                      ·
                        rfl

theorem cell23_1628601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_1628601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628601 prefixEnd_1628601 := by exact prefixLift 1628601
  have htrace : WordTrace (prefixWord ++ tailWord_1628601) baseStart_1628601 baseEnd_1628601 := by
    simpa [prefixWord, tailWord_1628601, baseEnd_1628601] using wordTrace_append hprefix tailTrace_1628601
  have hstable : (prefixWord ++ tailWord_1628601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628601).length < 2 ^ (prefixWord ++ tailWord_1628601).sum := by decide
  have hdescent : baseEnd_1628601 < baseStart_1628601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628617 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 2, 1, 3]
def baseStart_1628617 : Nat := 118140960795 + 1628617 * 2 ^ 59
def prefixEnd_1628617 : Nat := 4983230072969 + 3 ^ 40 * 1628617 * 2
def baseEnd_1628617 : Nat := 836263323083559762197633

theorem tailTrace_1628617 : CollatzResearch.WordTrace tailWord_1628617 prefixEnd_1628617 836263323083559762197633 := by
  unfold tailWord_1628617
  simp only [CollatzResearch.WordTrace]
  refine ⟨59400541940806229484404105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39600361293870819656269403 59400541940806229484404105)
  ·
    refine ⟨44550406455604672113303079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59400541940806229484404105 44550406455604672113303079)
    ·
      refine ⟨66825609683407008169954619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44550406455604672113303079 66825609683407008169954619)
      ·
        refine ⟨100238414525110512254931929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66825609683407008169954619 100238414525110512254931929)
        ·
          refine ⟨75178810893832884191198947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100238414525110512254931929 75178810893832884191198947)
          ·
            refine ⟨112768216340749326286798421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75178810893832884191198947 112768216340749326286798421)
            ·
              refine ⟨1321502535243156167423419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 112768216340749326286798421 1321502535243156167423419)
              ·
                refine ⟨1982253802864734251135129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321502535243156167423419 1982253802864734251135129)
                ·
                  refine ⟨1486690352148550688351347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982253802864734251135129 1486690352148550688351347)
                  ·
                    refine ⟨2230035528222826032527021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1486690352148550688351347 2230035528222826032527021)
                    ·
                      refine ⟨836263323083559762197633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230035528222826032527021 836263323083559762197633)
                      ·
                        rfl

theorem cell23_1628617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 1, 3].length) (baseStart_1628617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628617 prefixEnd_1628617 := by exact prefixLift 1628617
  have htrace : WordTrace (prefixWord ++ tailWord_1628617) baseStart_1628617 baseEnd_1628617 := by
    simpa [prefixWord, tailWord_1628617, baseEnd_1628617] using wordTrace_append hprefix tailTrace_1628617
  have hstable : (prefixWord ++ tailWord_1628617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628617).length < 2 ^ (prefixWord ++ tailWord_1628617).sum := by decide
  have hdescent : baseEnd_1628617 < baseStart_1628617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628640 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 1, 4, 2]
def baseStart_1628640 : Nat := 118140960795 + 1628640 * 2 ^ 59
def prefixEnd_1628640 : Nat := 4983230072969 + 3 ^ 40 * 1628640 * 2
def baseEnd_1628640 : Nat := 836275133138613172210027

theorem tailTrace_1628640 : CollatzResearch.WordTrace tailWord_1628640 prefixEnd_1628640 836275133138613172210027 := by
  unfold tailWord_1628640
  simp only [CollatzResearch.WordTrace]
  refine ⟨29700690409861452206245687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39600920546481936274994249 29700690409861452206245687)
  ·
    refine ⟨44551035614792178309368531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29700690409861452206245687 44551035614792178309368531)
    ·
      refine ⟨66826553422188267464052797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44551035614792178309368531 66826553422188267464052797)
      ·
        refine ⟨25059957533320600299019799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66826553422188267464052797 25059957533320600299019799)
        ·
          refine ⟨37589936299980900448529699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25059957533320600299019799 37589936299980900448529699)
          ·
            refine ⟨56384904449971350672794549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37589936299980900448529699 56384904449971350672794549)
            ·
              refine ⟨5286084792184814125574489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56384904449971350672794549 5286084792184814125574489)
              ·
                refine ⟨3964563594138610594180867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5286084792184814125574489 3964563594138610594180867)
                ·
                  refine ⟨5946845391207915891271301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964563594138610594180867 5946845391207915891271301)
                  ·
                    refine ⟨1115033510851484229613369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946845391207915891271301 1115033510851484229613369)
                    ·
                      refine ⟨836275133138613172210027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115033510851484229613369 836275133138613172210027)
                      ·
                        rfl

theorem cell23_1628640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_1628640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628640 prefixEnd_1628640 := by exact prefixLift 1628640
  have htrace : WordTrace (prefixWord ++ tailWord_1628640) baseStart_1628640 baseEnd_1628640 := by
    simpa [prefixWord, tailWord_1628640, baseEnd_1628640] using wordTrace_append hprefix tailTrace_1628640
  have hstable : (prefixWord ++ tailWord_1628640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628640).length < 2 ^ (prefixWord ++ tailWord_1628640).sum := by decide
  have hdescent : baseEnd_1628640 < baseStart_1628640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628693 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1628693 : Nat := 118140960795 + 1628693 * 2 ^ 59
def prefixEnd_1628693 : Nat := 4983230072969 + 3 ^ 40 * 1628693 * 2
def baseEnd_1628693 : Nat := 278767449204433821615761

theorem tailTrace_1628693 : CollatzResearch.WordTrace tailWord_1628693 prefixEnd_1628693 278767449204433821615761 := by
  unfold tailWord_1628693
  simp only [CollatzResearch.WordTrace]
  refine ⟨59403313888530894464170733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39602209259020596309447155 59403313888530894464170733)
  ·
    refine ⟨22276242708199085424064025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59403313888530894464170733 22276242708199085424064025)
    ·
      refine ⟨16707182031149314068048019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22276242708199085424064025 16707182031149314068048019)
      ·
        refine ⟨25060773046723971102072029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707182031149314068048019 25060773046723971102072029)
        ·
          refine ⟨9397789892521489163277011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25060773046723971102072029 9397789892521489163277011)
          ·
            refine ⟨14096684838782233744915517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9397789892521489163277011 14096684838782233744915517)
            ·
              refine ⟨5286256814543337654343319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14096684838782233744915517 5286256814543337654343319)
              ·
                refine ⟨7929385221815006481514979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286256814543337654343319 7929385221815006481514979)
                ·
                  refine ⟨11894077832722509722272469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7929385221815006481514979 11894077832722509722272469)
                  ·
                    refine ⟨278767449204433821615761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11894077832722509722272469 278767449204433821615761)
                    ·
                      rfl

theorem cell23_1628693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1628693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628693 prefixEnd_1628693 := by exact prefixLift 1628693
  have htrace : WordTrace (prefixWord ++ tailWord_1628693) baseStart_1628693 baseEnd_1628693 := by
    simpa [prefixWord, tailWord_1628693, baseEnd_1628693] using wordTrace_append hprefix tailTrace_1628693
  have hstable : (prefixWord ++ tailWord_1628693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628693).length < 2 ^ (prefixWord ++ tailWord_1628693).sum := by decide
  have hdescent : baseEnd_1628693 < baseStart_1628693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628708 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1628708 : Nat := 118140960795 + 1628708 * 2 ^ 59
def prefixEnd_1628708 : Nat := 4983230072969 + 3 ^ 40 * 1628708 * 2
def baseEnd_1628708 : Nat := 836310049823118906159715

theorem tailTrace_1628708 : CollatzResearch.WordTrace tailWord_1628708 prefixEnd_1628708 836310049823118906159715 := by
  unfold tailWord_1628708
  simp only [CollatzResearch.WordTrace]
  refine ⟨29701930491738276012983389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39602573988984368017311185 29701930491738276012983389)
  ·
    refine ⟨11138223934401853504868771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29701930491738276012983389 11138223934401853504868771)
    ·
      refine ⟨16707335901602780257303157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11138223934401853504868771 16707335901602780257303157)
      ·
        refine ⟨1566312740775260649122171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16707335901602780257303157 1566312740775260649122171)
        ·
          refine ⟨2349469111162890973683257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566312740775260649122171 2349469111162890973683257)
          ·
            refine ⟨1762101833372168230262443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2349469111162890973683257 1762101833372168230262443)
            ·
              refine ⟨2643152750058252345393665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762101833372168230262443 2643152750058252345393665)
              ·
                refine ⟨1982364562543689259045249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643152750058252345393665 1982364562543689259045249)
                ·
                  refine ⟨1486773421907766944283937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982364562543689259045249 1486773421907766944283937)
                  ·
                    refine ⟨1115080066430825208212953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1486773421907766944283937 1115080066430825208212953)
                    ·
                      refine ⟨836310049823118906159715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115080066430825208212953 836310049823118906159715)
                      ·
                        rfl

theorem cell23_1628708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1628708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628708 prefixEnd_1628708 := by exact prefixLift 1628708
  have htrace : WordTrace (prefixWord ++ tailWord_1628708) baseStart_1628708 baseEnd_1628708 := by
    simpa [prefixWord, tailWord_1628708, baseEnd_1628708] using wordTrace_append hprefix tailTrace_1628708
  have hstable : (prefixWord ++ tailWord_1628708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628708).length < 2 ^ (prefixWord ++ tailWord_1628708).sum := by decide
  have hdescent : baseEnd_1628708 < baseStart_1628708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628750 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1628750 : Nat := 118140960795 + 1628750 * 2 ^ 59
def prefixEnd_1628750 : Nat := 4983230072969 + 3 ^ 40 * 1628750 * 2
def baseEnd_1628750 : Nat := 836331616010607741834521

theorem tailTrace_1628750 : CollatzResearch.WordTrace tailWord_1628750 prefixEnd_1628750 836331616010607741834521 := by
  unfold tailWord_1628750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425674106165549149874463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39603595232882928799330469 7425674106165549149874463)
  ·
    refine ⟨11138511159248323724811695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7425674106165549149874463 11138511159248323724811695)
    ·
      refine ⟨16707766738872485587217543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11138511159248323724811695 16707766738872485587217543)
      ·
        refine ⟨25061650108308728380826315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707766738872485587217543 25061650108308728380826315)
        ·
          refine ⟨37592475162463092571239473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061650108308728380826315 37592475162463092571239473)
          ·
            refine ⟨28194356371847319428429605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37592475162463092571239473 28194356371847319428429605)
            ·
              refine ⟨5286441819721372392830551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28194356371847319428429605 5286441819721372392830551)
              ·
                refine ⟨7929662729582058589245827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286441819721372392830551 7929662729582058589245827)
                ·
                  refine ⟨11894494094373087883868741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7929662729582058589245827 11894494094373087883868741)
                  ·
                    refine ⟨2230217642694953978225389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11894494094373087883868741 2230217642694953978225389)
                    ·
                      refine ⟨836331616010607741834521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230217642694953978225389 836331616010607741834521)
                      ·
                        rfl

theorem cell23_1628750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1628750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628750 prefixEnd_1628750 := by exact prefixLift 1628750
  have htrace : WordTrace (prefixWord ++ tailWord_1628750) baseStart_1628750 baseEnd_1628750 := by
    simpa [prefixWord, tailWord_1628750, baseEnd_1628750] using wordTrace_append hprefix tailTrace_1628750
  have hstable : (prefixWord ++ tailWord_1628750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628750).length < 2 ^ (prefixWord ++ tailWord_1628750).sum := by decide
  have hdescent : baseEnd_1628750 < baseStart_1628750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628753 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 8]
def baseStart_1628753 : Nat := 118140960795 + 1628753 * 2 ^ 59
def prefixEnd_1628753 : Nat := 4983230072969 + 3 ^ 40 * 1628753 * 2
def baseEnd_1628753 : Nat := 92925906272507914455223

theorem tailTrace_1628753 : CollatzResearch.WordTrace tailWord_1628753 prefixEnd_1628753 92925906272507914455223 := by
  unfold tailWord_1628753
  simp only [CollatzResearch.WordTrace]
  refine ⟨59405502268313524711354913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39603668178875683140903275 59405502268313524711354913)
  ·
    refine ⟨44554126701235143533516185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59405502268313524711354913 44554126701235143533516185)
    ·
      refine ⟨33415595025926357650137139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44554126701235143533516185 33415595025926357650137139)
      ·
        refine ⟨50123392538889536475205709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33415595025926357650137139 50123392538889536475205709)
        ·
          refine ⟨18796272202083576178202141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50123392538889536475205709 18796272202083576178202141)
          ·
            refine ⟨7048602075781341066825803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18796272202083576178202141 7048602075781341066825803)
            ·
              refine ⟨10572903113672011600238705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048602075781341066825803 10572903113672011600238705)
              ·
                refine ⟨7929677335254008700179029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10572903113672011600238705 7929677335254008700179029)
                ·
                  refine ⟨92925906272507914455223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7929677335254008700179029 92925906272507914455223)
                  ·
                    rfl

theorem cell23_1628753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_1628753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628753 prefixEnd_1628753 := by exact prefixLift 1628753
  have htrace : WordTrace (prefixWord ++ tailWord_1628753) baseStart_1628753 baseEnd_1628753 := by
    simpa [prefixWord, tailWord_1628753, baseEnd_1628753] using wordTrace_append hprefix tailTrace_1628753
  have hstable : (prefixWord ++ tailWord_1628753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628753).length < 2 ^ (prefixWord ++ tailWord_1628753).sum := by decide
  have hdescent : baseEnd_1628753 < baseStart_1628753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628800 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_1628800 : Nat := 118140960795 + 1628800 * 2 ^ 59
def prefixEnd_1628800 : Nat := 4983230072969 + 3 ^ 40 * 1628800 * 2
def baseEnd_1628800 : Nat := 278785763347777515403097

theorem tailTrace_1628800 : CollatzResearch.WordTrace tailWord_1628800 prefixEnd_1628800 278785763347777515403097 := by
  unfold tailWord_1628800
  simp only [CollatzResearch.WordTrace]
  refine ⟨29703608249571625869157927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39604810999428834492210569 29703608249571625869157927)
  ·
    refine ⟨44555412374357438803736891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29703608249571625869157927 44555412374357438803736891)
    ·
      refine ⟨66833118561536158205605337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44555412374357438803736891 66833118561536158205605337)
      ·
        refine ⟨50124838921152118654204003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66833118561536158205605337 50124838921152118654204003)
        ·
          refine ⟨75187258381728177981306005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50124838921152118654204003 75187258381728177981306005)
          ·
            refine ⟨3524402736643508342873719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75187258381728177981306005 3524402736643508342873719)
            ·
              refine ⟨5286604104965262514310579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524402736643508342873719 5286604104965262514310579)
              ·
                refine ⟨7929906157447893771465869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286604104965262514310579 7929906157447893771465869)
                ·
                  refine ⟨2973714809042960164299701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7929906157447893771465869 2973714809042960164299701)
                  ·
                    refine ⟨278785763347777515403097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2973714809042960164299701 278785763347777515403097)
                    ·
                      rfl

theorem cell23_1628800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_1628800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628800 prefixEnd_1628800 := by exact prefixLift 1628800
  have htrace : WordTrace (prefixWord ++ tailWord_1628800) baseStart_1628800 baseEnd_1628800 := by
    simpa [prefixWord, tailWord_1628800, baseEnd_1628800] using wordTrace_append hprefix tailTrace_1628800
  have hstable : (prefixWord ++ tailWord_1628800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628800).length < 2 ^ (prefixWord ++ tailWord_1628800).sum := by decide
  have hdescent : baseEnd_1628800 < baseStart_1628800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628847 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 2, 4]
def baseStart_1628847 : Nat := 118140960795 + 1628847 * 2 ^ 59
def prefixEnd_1628847 : Nat := 4983230072969 + 3 ^ 40 * 1628847 * 2
def baseEnd_1628847 : Nat := 278793807878031287440525

theorem tailTrace_1628847 : CollatzResearch.WordTrace tailWord_1628847 prefixEnd_1628847 278793807878031287440525 := by
  unfold tailWord_1628847
  simp only [CollatzResearch.WordTrace]
  refine ⟨59408930729972978765276795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39605953819981985843517863 59408930729972978765276795)
  ·
    refine ⟨89113396094959468147915193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59408930729972978765276795 89113396094959468147915193)
    ·
      refine ⟨66835047071219601110936395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89113396094959468147915193 66835047071219601110936395)
      ·
        refine ⟨100252570606829401666404593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66835047071219601110936395 100252570606829401666404593)
        ·
          refine ⟨75189427955122051249803445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100252570606829401666404593 75189427955122051249803445)
          ·
            refine ⟨7049008870792692304669073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75189427955122051249803445 7049008870792692304669073)
            ·
              refine ⟨5286756653094519228501805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7049008870792692304669073 5286756653094519228501805)
              ·
                refine ⟨1982533744910444710688177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5286756653094519228501805 1982533744910444710688177)
                ·
                  refine ⟨1486900308682833533016133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982533744910444710688177 1486900308682833533016133)
                  ·
                    refine ⟨278793807878031287440525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1486900308682833533016133 278793807878031287440525)
                    ·
                      rfl

theorem cell23_1628847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_1628847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628847 prefixEnd_1628847 := by exact prefixLift 1628847
  have htrace : WordTrace (prefixWord ++ tailWord_1628847) baseStart_1628847 baseEnd_1628847 := by
    simpa [prefixWord, tailWord_1628847, baseEnd_1628847] using wordTrace_append hprefix tailTrace_1628847
  have hstable : (prefixWord ++ tailWord_1628847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628847).length < 2 ^ (prefixWord ++ tailWord_1628847).sum := by decide
  have hdescent : baseEnd_1628847 < baseStart_1628847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628857 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1628857 : Nat := 118140960795 + 1628857 * 2 ^ 59
def prefixEnd_1628857 : Nat := 4983230072969 + 3 ^ 40 * 1628857 * 2
def baseEnd_1628857 : Nat := 836386558440638823196529

theorem tailTrace_1628857 : CollatzResearch.WordTrace tailWord_1628857 prefixEnd_1628857 836386558440638823196529 := by
  unfold tailWord_1628857
  simp only [CollatzResearch.WordTrace]
  refine ⟨59409295459936750473140825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39606196973291166982093883 59409295459936750473140825)
  ·
    refine ⟨44556971594952562854855619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59409295459936750473140825 44556971594952562854855619)
    ·
      refine ⟨66835457392428844282283429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44556971594952562854855619 66835457392428844282283429)
      ·
        refine ⟨12531648261080408302928143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66835457392428844282283429 12531648261080408302928143)
        ·
          refine ⟨18797472391620612454392215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12531648261080408302928143 18797472391620612454392215)
          ·
            refine ⟨28196208587430918681588323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18797472391620612454392215 28196208587430918681588323)
            ·
              refine ⟨42294312881146378022382485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28196208587430918681588323 42294312881146378022382485)
              ·
                refine ⟨1982545916303736469799179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42294312881146378022382485 1982545916303736469799179)
                ·
                  refine ⟨2973818874455604704698769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982545916303736469799179 2973818874455604704698769)
                  ·
                    refine ⟨2230364155841703528524077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973818874455604704698769 2230364155841703528524077)
                    ·
                      refine ⟨836386558440638823196529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230364155841703528524077 836386558440638823196529)
                      ·
                        rfl

theorem cell23_1628857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1628857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628857 prefixEnd_1628857 := by exact prefixLift 1628857
  have htrace : WordTrace (prefixWord ++ tailWord_1628857) baseStart_1628857 baseEnd_1628857 := by
    simpa [prefixWord, tailWord_1628857, baseEnd_1628857] using wordTrace_append hprefix tailTrace_1628857
  have hstable : (prefixWord ++ tailWord_1628857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628857).length < 2 ^ (prefixWord ++ tailWord_1628857).sum := by decide
  have hdescent : baseEnd_1628857 < baseStart_1628857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628865 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1628865 : Nat := 118140960795 + 1628865 * 2 ^ 59
def prefixEnd_1628865 : Nat := 4983230072969 + 3 ^ 40 * 1628865 * 2
def baseEnd_1628865 : Nat := 836390666285874791896493

theorem tailTrace_1628865 : CollatzResearch.WordTrace tailWord_1628865 prefixEnd_1628865 836390666285874791896493 := by
  unfold tailWord_1628865
  simp only [CollatzResearch.WordTrace]
  refine ⟨59409587243907767839432049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39606391495938511892954699 59409587243907767839432049)
  ·
    refine ⟨44557190432930825879574037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59409587243907767839432049 44557190432930825879574037)
    ·
      refine ⟨2088618301543632463105033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44557190432930825879574037 2088618301543632463105033)
      ·
        refine ⟨1566463726157724347328775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2088618301543632463105033 1566463726157724347328775)
        ·
          refine ⟨2349695589236586520993163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566463726157724347328775 2349695589236586520993163)
          ·
            refine ⟨3524543383854879781489745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349695589236586520993163 3524543383854879781489745)
            ·
              refine ⟨2643407537891159836117309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524543383854879781489745 2643407537891159836117309)
              ·
                refine ⟨991277826709184938543991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2643407537891159836117309 991277826709184938543991)
                ·
                  refine ⟨1486916740063777407815987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991277826709184938543991 1486916740063777407815987)
                  ·
                    refine ⟨2230375110095666111723981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1486916740063777407815987 2230375110095666111723981)
                    ·
                      refine ⟨836390666285874791896493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230375110095666111723981 836390666285874791896493)
                      ·
                        rfl

theorem cell23_1628865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1628865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628865 prefixEnd_1628865 := by exact prefixLift 1628865
  have htrace : WordTrace (prefixWord ++ tailWord_1628865) baseStart_1628865 baseEnd_1628865 := by
    simpa [prefixWord, tailWord_1628865, baseEnd_1628865] using wordTrace_append hprefix tailTrace_1628865
  have hstable : (prefixWord ++ tailWord_1628865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628865).length < 2 ^ (prefixWord ++ tailWord_1628865).sum := by decide
  have hdescent : baseEnd_1628865 < baseStart_1628865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628874 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_1628874 : Nat := 118140960795 + 1628874 * 2 ^ 59
def prefixEnd_1628874 : Nat := 4983230072969 + 3 ^ 40 * 1628874 * 2
def baseEnd_1628874 : Nat := 836395287611765256683951

theorem tailTrace_1628874 : CollatzResearch.WordTrace tailWord_1628874 prefixEnd_1628874 836395287611765256683951 := by
  unfold tailWord_1628874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14852478875218790594127419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39606610333916774917673117 14852478875218790594127419)
  ·
    refine ⟨22278718312828185891191129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14852478875218790594127419 22278718312828185891191129)
    ·
      refine ⟨16709038734621139418393347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22278718312828185891191129 16709038734621139418393347)
      ·
        refine ⟨25063558101931709127590021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16709038734621139418393347 25063558101931709127590021)
        ·
          refine ⟨4699417144112195461423129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25063558101931709127590021 4699417144112195461423129)
          ·
            refine ⟨3524562858084146596067347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4699417144112195461423129 3524562858084146596067347)
            ·
              refine ⟨5286844287126219894101021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524562858084146596067347 5286844287126219894101021)
              ·
                refine ⟨1982566607672332460287883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5286844287126219894101021 1982566607672332460287883)
                ·
                  refine ⟨2973849911508498690431825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982566607672332460287883 2973849911508498690431825)
                  ·
                    refine ⟨2230387433631374017823869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2973849911508498690431825 2230387433631374017823869)
                    ·
                      refine ⟨836395287611765256683951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230387433631374017823869 836395287611765256683951)
                      ·
                        rfl

theorem cell23_1628874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_1628874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628874 prefixEnd_1628874 := by exact prefixLift 1628874
  have htrace : WordTrace (prefixWord ++ tailWord_1628874) baseStart_1628874 baseEnd_1628874 := by
    simpa [prefixWord, tailWord_1628874, baseEnd_1628874] using wordTrace_append hprefix tailTrace_1628874
  have hstable : (prefixWord ++ tailWord_1628874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628874).length < 2 ^ (prefixWord ++ tailWord_1628874).sum := by decide
  have hdescent : baseEnd_1628874 < baseStart_1628874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628927 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 3, 4, 2]
def baseStart_1628927 : Nat := 118140960795 + 1628927 * 2 ^ 59
def prefixEnd_1628927 : Nat := 4983230072969 + 3 ^ 40 * 1628927 * 2
def baseEnd_1628927 : Nat := 836422502086453549321207

theorem tailTrace_1628927 : CollatzResearch.WordTrace tailWord_1628927 prefixEnd_1628927 836422502086453549321207 := by
  unfold tailWord_1628927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59411848569683152428189035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39607899046455434952126023 59411848569683152428189035)
  ·
    refine ⟨89117772854524728642283553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59411848569683152428189035 89117772854524728642283553)
    ·
      refine ⟨66838329640893546481712665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89117772854524728642283553 66838329640893546481712665)
      ·
        refine ⟨50128747230670159861284499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66838329640893546481712665 50128747230670159861284499)
        ·
          refine ⟨75193120846005239791926749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50128747230670159861284499 75193120846005239791926749)
          ·
            refine ⟨28197420317251964921972531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75193120846005239791926749 28197420317251964921972531)
            ·
              refine ⟨42296130475877947382958797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28197420317251964921972531 42296130475877947382958797)
              ·
                refine ⟨15861048928454230268609549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42296130475877947382958797 15861048928454230268609549)
                ·
                  refine ⟨5947893348170336350728581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15861048928454230268609549 5947893348170336350728581)
                  ·
                    refine ⟨1115230002781938065761609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5947893348170336350728581 1115230002781938065761609)
                    ·
                      refine ⟨836422502086453549321207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115230002781938065761609 836422502086453549321207)
                      ·
                        rfl

theorem cell23_1628927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_1628927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628927 prefixEnd_1628927 := by exact prefixLift 1628927
  have htrace : WordTrace (prefixWord ++ tailWord_1628927) baseStart_1628927 baseEnd_1628927 := by
    simpa [prefixWord, tailWord_1628927, baseEnd_1628927] using wordTrace_append hprefix tailTrace_1628927
  have hstable : (prefixWord ++ tailWord_1628927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628927).length < 2 ^ (prefixWord ++ tailWord_1628927).sum := by decide
  have hdescent : baseEnd_1628927 < baseStart_1628927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628961 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1628961 : Nat := 118140960795 + 1628961 * 2 ^ 59
def prefixEnd_1628961 : Nat := 4983230072969 + 3 ^ 40 * 1628961 * 2
def baseEnd_1628961 : Nat := 836439960428706416296051

theorem tailTrace_1628961 : CollatzResearch.WordTrace tailWord_1628961 prefixEnd_1628961 836439960428706416296051 := by
  unfold tailWord_1628961
  simp only [CollatzResearch.WordTrace]
  refine ⟨59413088651559976234926737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39608725767706650823284491 59413088651559976234926737)
  ·
    refine ⟨44559816488669982176195053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59413088651559976234926737 44559816488669982176195053)
    ·
      refine ⟨16709931183251243316073145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44559816488669982176195053 16709931183251243316073145)
      ·
        refine ⟨12532448387438432487054859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16709931183251243316073145 12532448387438432487054859)
        ·
          refine ⟨18798672581157648730582289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12532448387438432487054859 18798672581157648730582289)
          ·
            refine ⟨14099004435868236547936717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18798672581157648730582289 14099004435868236547936717)
            ·
              refine ⟨5287126663450588705476269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14099004435868236547936717 5287126663450588705476269)
              ·
                refine ⟨1982672498793970764553601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5287126663450588705476269 1982672498793970764553601)
                ·
                  refine ⟨1487004374095478073415201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982672498793970764553601 1487004374095478073415201)
                  ·
                    refine ⟨1115253280571608555061401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487004374095478073415201 1115253280571608555061401)
                    ·
                      refine ⟨836439960428706416296051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115253280571608555061401 836439960428706416296051)
                      ·
                        rfl

theorem cell23_1628961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1628961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1628961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1628961 prefixEnd_1628961 := by exact prefixLift 1628961
  have htrace : WordTrace (prefixWord ++ tailWord_1628961) baseStart_1628961 baseEnd_1628961 := by
    simpa [prefixWord, tailWord_1628961, baseEnd_1628961] using wordTrace_append hprefix tailTrace_1628961
  have hstable : (prefixWord ++ tailWord_1628961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628961).length < 2 ^ (prefixWord ++ tailWord_1628961).sum := by decide
  have hdescent : baseEnd_1628961 < baseStart_1628961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629001 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 5]
def baseStart_1629001 : Nat := 118140960795 + 1629001 * 2 ^ 59
def prefixEnd_1629001 : Nat := 4983230072969 + 3 ^ 40 * 1629001 * 2
def baseEnd_1629001 : Nat := 92940055517209584421763

theorem tailTrace_1629001 : CollatzResearch.WordTrace tailWord_1629001 prefixEnd_1629001 92940055517209584421763 := by
  unfold tailWord_1629001
  simp only [CollatzResearch.WordTrace]
  refine ⟨59414547571415063066382857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39609698380943375377588571 59414547571415063066382857)
  ·
    refine ⟨44560910678561297299787143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59414547571415063066382857 44560910678561297299787143)
    ·
      refine ⟨66841366017841945949680715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44560910678561297299787143 66841366017841945949680715)
      ·
        refine ⟨100262049026762918924521073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66841366017841945949680715 100262049026762918924521073)
        ·
          refine ⟨75196536770072189193390805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100262049026762918924521073 75196536770072189193390805)
          ·
            refine ⟨1762418830548566934220097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75196536770072189193390805 1762418830548566934220097)
            ·
              refine ⟨1321814122911425200665073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762418830548566934220097 1321814122911425200665073)
              ·
                refine ⟨991360592183568900498805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321814122911425200665073 991360592183568900498805)
                ·
                  refine ⟨92940055517209584421763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 991360592183568900498805 92940055517209584421763)
                  ·
                    rfl

theorem cell23_1629001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 5].length) (baseStart_1629001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629001 prefixEnd_1629001 := by exact prefixLift 1629001
  have htrace : WordTrace (prefixWord ++ tailWord_1629001) baseStart_1629001 baseEnd_1629001 := by
    simpa [prefixWord, tailWord_1629001, baseEnd_1629001] using wordTrace_append hprefix tailTrace_1629001
  have hstable : (prefixWord ++ tailWord_1629001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629001).length < 2 ^ (prefixWord ++ tailWord_1629001).sum := by decide
  have hdescent : baseEnd_1629001 < baseStart_1629001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629004 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 2, 5, 2]
def baseStart_1629004 : Nat := 118140960795 + 1629004 * 2 ^ 59
def prefixEnd_1629004 : Nat := 4983230072969 + 3 ^ 40 * 1629004 * 2
def baseEnd_1629004 : Nat := 836462040096849748058353

theorem tailTrace_1629004 : CollatzResearch.WordTrace tailWord_1629004 prefixEnd_1629004 836462040096849748058353 := by
  unfold tailWord_1629004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29707328495202097289371033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39609771326936129719161377 29707328495202097289371033)
  ·
    refine ⟨22280496371401572967028275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29707328495202097289371033 22280496371401572967028275)
    ·
      refine ⟨33420744557102359450542413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22280496371401572967028275 33420744557102359450542413)
      ·
        refine ⟨12532779208913384793953405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33420744557102359450542413 12532779208913384793953405)
        ·
          refine ⟨4699792203342519297732527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12532779208913384793953405 4699792203342519297732527)
          ·
            refine ⟨7049688305013778946598791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699792203342519297732527 7049688305013778946598791)
            ·
              refine ⟨10574532457520668419898187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049688305013778946598791 10574532457520668419898187)
              ·
                refine ⟨15861798686281002629847281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574532457520668419898187 15861798686281002629847281)
                ·
                  refine ⟨11896349014710751972385461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15861798686281002629847281 11896349014710751972385461)
                  ·
                    refine ⟨1115282720129132997411137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11896349014710751972385461 1115282720129132997411137)
                    ·
                      refine ⟨836462040096849748058353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115282720129132997411137 836462040096849748058353)
                      ·
                        rfl

theorem cell23_1629004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_1629004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629004 prefixEnd_1629004 := by exact prefixLift 1629004
  have htrace : WordTrace (prefixWord ++ tailWord_1629004) baseStart_1629004 baseEnd_1629004 := by
    simpa [prefixWord, tailWord_1629004, baseEnd_1629004] using wordTrace_append hprefix tailTrace_1629004
  have hstable : (prefixWord ++ tailWord_1629004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629004).length < 2 ^ (prefixWord ++ tailWord_1629004).sum := by decide
  have hdescent : baseEnd_1629004 < baseStart_1629004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629061 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_1629061 : Nat := 118140960795 + 1629061 * 2 ^ 59
def prefixEnd_1629061 : Nat := 4983230072969 + 3 ^ 40 * 1629061 * 2
def baseEnd_1629061 : Nat := 278830436164718675015197

theorem tailTrace_1629061 : CollatzResearch.WordTrace tailWord_1629061 prefixEnd_1629061 278830436164718675015197 := by
  unfold tailWord_1629061
  simp only [CollatzResearch.WordTrace]
  refine ⟨59416735951197693313567037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39611157300798462209044691 59416735951197693313567037)
  ·
    refine ⟨22281275981699134992587639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59416735951197693313567037 22281275981699134992587639)
    ·
      refine ⟨33421913972548702488881459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22281275981699134992587639 33421913972548702488881459)
      ·
        refine ⟨50132870958823053733322189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33421913972548702488881459 50132870958823053733322189)
        ·
          refine ⟨18799826609558645149995821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50132870958823053733322189 18799826609558645149995821)
          ·
            refine ⟨7049934978584491931248433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18799826609558645149995821 7049934978584491931248433)
            ·
              refine ⟨5287451233938368948436325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7049934978584491931248433 5287451233938368948436325)
              ·
                refine ⟨991397106363444177831811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5287451233938368948436325 991397106363444177831811)
                ·
                  refine ⟨1487095659545166266747717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991397106363444177831811 1487095659545166266747717)
                  ·
                    refine ⟨278830436164718675015197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487095659545166266747717 278830436164718675015197)
                    ·
                      rfl

theorem cell23_1629061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_1629061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629061 prefixEnd_1629061 := by exact prefixLift 1629061
  have htrace : WordTrace (prefixWord ++ tailWord_1629061) baseStart_1629061 baseEnd_1629061 := by
    simpa [prefixWord, tailWord_1629061, baseEnd_1629061] using wordTrace_append hprefix tailTrace_1629061
  have hstable : (prefixWord ++ tailWord_1629061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629061).length < 2 ^ (prefixWord ++ tailWord_1629061).sum := by decide
  have hdescent : baseEnd_1629061 < baseStart_1629061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629095 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1629095 : Nat := 118140960795 + 1629095 * 2 ^ 59
def prefixEnd_1629095 : Nat := 4983230072969 + 3 ^ 40 * 1629095 * 2
def baseEnd_1629095 : Nat := 278836255612136297340145

theorem tailTrace_1629095 : CollatzResearch.WordTrace tailWord_1629095 prefixEnd_1629095 278836255612136297340145 := by
  unfold tailWord_1629095
  simp only [CollatzResearch.WordTrace]
  refine ⟨59417976033074517120304739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39611984022049678080203159 59417976033074517120304739)
  ·
    refine ⟨89126964049611775680457109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59417976033074517120304739 89126964049611775680457109)
    ·
      refine ⟨4177826439825551985021427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89126964049611775680457109 4177826439825551985021427)
      ·
        refine ⟨6266739659738327977532141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177826439825551985021427 6266739659738327977532141)
        ·
          refine ⟨2350027372401872991574553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6266739659738327977532141 2350027372401872991574553)
          ·
            refine ⟨1762520529301404743680915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350027372401872991574553 1762520529301404743680915)
            ·
              refine ⟨2643780793952107115521373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762520529301404743680915 2643780793952107115521373)
              ·
                refine ⟨991417797732040168320515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2643780793952107115521373 991417797732040168320515)
                ·
                  refine ⟨1487126696598060252480773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991417797732040168320515 1487126696598060252480773)
                  ·
                    refine ⟨278836255612136297340145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487126696598060252480773 278836255612136297340145)
                    ·
                      rfl

theorem cell23_1629095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1629095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629095 prefixEnd_1629095 := by exact prefixLift 1629095
  have htrace : WordTrace (prefixWord ++ tailWord_1629095) baseStart_1629095 baseEnd_1629095 := by
    simpa [prefixWord, tailWord_1629095, baseEnd_1629095] using wordTrace_append hprefix tailTrace_1629095
  have hstable : (prefixWord ++ tailWord_1629095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629095).length < 2 ^ (prefixWord ++ tailWord_1629095).sum := by decide
  have hdescent : baseEnd_1629095 < baseStart_1629095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629137 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_1629137 : Nat := 118140960795 + 1629137 * 2 ^ 59
def prefixEnd_1629137 : Nat := 4983230072969 + 3 ^ 40 * 1629137 * 2
def baseEnd_1629137 : Nat := 836530333023897727695241

theorem tailTrace_1629137 : CollatzResearch.WordTrace tailWord_1629137 prefixEnd_1629137 836530333023897727695241 := by
  unfold tailWord_1629137
  simp only [CollatzResearch.WordTrace]
  refine ⟨59419507898922358293333665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39613005265948238862222443 59419507898922358293333665)
  ·
    refine ⟨44564630924191768720000249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59419507898922358293333665 44564630924191768720000249)
    ·
      refine ⟨33423473193143826540000187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44564630924191768720000249 33423473193143826540000187)
      ·
        refine ⟨50135209789715739810000281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33423473193143826540000187 50135209789715739810000281)
        ·
          refine ⟨37601407342286804857500211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50135209789715739810000281 37601407342286804857500211)
          ·
            refine ⟨56402111013430207286250317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37601407342286804857500211 56402111013430207286250317)
            ·
              refine ⟨21150791630036327732343869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56402111013430207286250317 21150791630036327732343869)
              ·
                refine ⟨7931546861263622899628951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21150791630036327732343869 7931546861263622899628951)
                ·
                  refine ⟨11897320291895434349443427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7931546861263622899628951 11897320291895434349443427)
                  ·
                    refine ⟨17845980437843151524165141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11897320291895434349443427 17845980437843151524165141)
                    ·
                      refine ⟨836530333023897727695241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17845980437843151524165141 836530333023897727695241)
                      ·
                        rfl

theorem cell23_1629137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_1629137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629137 prefixEnd_1629137 := by exact prefixLift 1629137
  have htrace : WordTrace (prefixWord ++ tailWord_1629137) baseStart_1629137 baseEnd_1629137 := by
    simpa [prefixWord, tailWord_1629137, baseEnd_1629137] using wordTrace_append hprefix tailTrace_1629137
  have hstable : (prefixWord ++ tailWord_1629137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629137).length < 2 ^ (prefixWord ++ tailWord_1629137).sum := by decide
  have hdescent : baseEnd_1629137 < baseStart_1629137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629138 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1629138 : Nat := 118140960795 + 1629138 * 2 ^ 59
def prefixEnd_1629138 : Nat := 4983230072969 + 3 ^ 40 * 1629138 * 2
def baseEnd_1629138 : Nat := 278843615501517407927579

theorem tailTrace_1629138 : CollatzResearch.WordTrace tailWord_1629138 prefixEnd_1629138 278843615501517407927579 := by
  unfold tailWord_1629138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14854886092979683866030017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39613029581279156976080045 14854886092979683866030017)
  ·
    refine ⟨11141164569734762899522513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14854886092979683866030017 11141164569734762899522513)
    ·
      refine ⟨8355873427301072174641885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11141164569734762899522513 8355873427301072174641885)
      ·
        refine ⟨3133452535237902065490707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8355873427301072174641885 3133452535237902065490707)
        ·
          refine ⟨4700178802856853098236061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133452535237902065490707 4700178802856853098236061)
          ·
            refine ⟨1762567051071319911838523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4700178802856853098236061 1762567051071319911838523)
            ·
              refine ⟨2643850576606979867757785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762567051071319911838523 2643850576606979867757785)
              ·
                refine ⟨1982887932455234900818339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643850576606979867757785 1982887932455234900818339)
                ·
                  refine ⟨2974331898682852351227509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982887932455234900818339 2974331898682852351227509)
                  ·
                    refine ⟨278843615501517407927579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2974331898682852351227509 278843615501517407927579)
                    ·
                      rfl

theorem cell23_1629138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1629138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629138 prefixEnd_1629138 := by exact prefixLift 1629138
  have htrace : WordTrace (prefixWord ++ tailWord_1629138) baseStart_1629138 baseEnd_1629138 := by
    simpa [prefixWord, tailWord_1629138, baseEnd_1629138] using wordTrace_append hprefix tailTrace_1629138
  have hstable : (prefixWord ++ tailWord_1629138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629138).length < 2 ^ (prefixWord ++ tailWord_1629138).sum := by decide
  have hdescent : baseEnd_1629138 < baseStart_1629138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629141 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1629141 : Nat := 118140960795 + 1629141 * 2 ^ 59
def prefixEnd_1629141 : Nat := 4983230072969 + 3 ^ 40 * 1629141 * 2
def baseEnd_1629141 : Nat := 836532386946515712045223

theorem tailTrace_1629141 : CollatzResearch.WordTrace tailWord_1629141 prefixEnd_1629141 836532386946515712045223 := by
  unfold tailWord_1629141
  simp only [CollatzResearch.WordTrace]
  refine ⟨59419653790907866976479277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39613102527271911317652851 59419653790907866976479277)
  ·
    refine ⟨22282370171590450116179729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59419653790907866976479277 22282370171590450116179729)
    ·
      refine ⟨16711777628692837587134797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22282370171590450116179729 16711777628692837587134797)
      ·
        refine ⟨6266916610759814095175549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16711777628692837587134797 6266916610759814095175549)
        ·
          refine ⟨2350093729034930285690831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6266916610759814095175549 2350093729034930285690831)
          ·
            refine ⟨3525140593552395428536247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350093729034930285690831 3525140593552395428536247)
            ·
              refine ⟨5287710890328593142804371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525140593552395428536247 5287710890328593142804371)
              ·
                refine ⟨7931566335492889714206557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287710890328593142804371 7931566335492889714206557)
                ·
                  refine ⟨2974337375809833642827459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7931566335492889714206557 2974337375809833642827459)
                  ·
                    refine ⟨4461506063714750464241189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2974337375809833642827459 4461506063714750464241189)
                    ·
                      refine ⟨836532386946515712045223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4461506063714750464241189 836532386946515712045223)
                      ·
                        rfl

theorem cell23_1629141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1629141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629141 prefixEnd_1629141 := by exact prefixLift 1629141
  have htrace : WordTrace (prefixWord ++ tailWord_1629141) baseStart_1629141 baseEnd_1629141 := by
    simpa [prefixWord, tailWord_1629141, baseEnd_1629141] using wordTrace_append hprefix tailTrace_1629141
  have hstable : (prefixWord ++ tailWord_1629141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629141).length < 2 ^ (prefixWord ++ tailWord_1629141).sum := by decide
  have hdescent : baseEnd_1629141 < baseStart_1629141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629177 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_1629177 : Nat := 118140960795 + 1629177 * 2 ^ 59
def prefixEnd_1629177 : Nat := 4983230072969 + 3 ^ 40 * 1629177 * 2
def baseEnd_1629177 : Nat := 278850290750025857065019

theorem tailTrace_1629177 : CollatzResearch.WordTrace tailWord_1629177 prefixEnd_1629177 278850290750025857065019 := by
  unfold tailWord_1629177
  simp only [CollatzResearch.WordTrace]
  refine ⟨59420966818777445124789785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39613977879184963416526523 59420966818777445124789785)
  ·
    refine ⟨44565725114083083843592339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59420966818777445124789785 44565725114083083843592339)
    ·
      refine ⟨66848587671124625765388509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44565725114083083843592339 66848587671124625765388509)
      ·
        refine ⟨25068220376671734662020691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66848587671124625765388509 25068220376671734662020691)
        ·
          refine ⟨37602330565007601993031037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25068220376671734662020691 37602330565007601993031037)
          ·
            refine ⟨14100873961877850747386639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37602330565007601993031037 14100873961877850747386639)
            ·
              refine ⟨21151310942816776121079959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14100873961877850747386639 21151310942816776121079959)
              ·
                refine ⟨31726966414225164181619939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21151310942816776121079959 31726966414225164181619939)
                ·
                  refine ⟨47590449621337746272429909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31726966414225164181619939 47590449621337746272429909)
                  ·
                    refine ⟨278850290750025857065019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47590449621337746272429909 278850290750025857065019)
                    ·
                      rfl

theorem cell23_1629177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_1629177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629177 prefixEnd_1629177 := by exact prefixLift 1629177
  have htrace : WordTrace (prefixWord ++ tailWord_1629177) baseStart_1629177 baseEnd_1629177 := by
    simpa [prefixWord, tailWord_1629177, baseEnd_1629177] using wordTrace_append hprefix tailTrace_1629177
  have hstable : (prefixWord ++ tailWord_1629177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629177).length < 2 ^ (prefixWord ++ tailWord_1629177).sum := by decide
  have hdescent : baseEnd_1629177 < baseStart_1629177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629187 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1629187 : Nat := 118140960795 + 1629187 * 2 ^ 59
def prefixEnd_1629187 : Nat := 4983230072969 + 3 ^ 40 * 1629187 * 2
def baseEnd_1629187 : Nat := 836556007056622532070011

theorem tailTrace_1629187 : CollatzResearch.WordTrace tailWord_1629187 prefixEnd_1629187 836556007056622532070011 := by
  unfold tailWord_1629187
  simp only [CollatzResearch.WordTrace]
  refine ⟨59421331548741216832653815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39614221032494144555102543 59421331548741216832653815)
  ·
    refine ⟨89131997323111825248980723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59421331548741216832653815 89131997323111825248980723)
    ·
      refine ⟨133697995984667737873471085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89131997323111825248980723 133697995984667737873471085)
      ·
        refine ⟨50136748494250401702551657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133697995984667737873471085 50136748494250401702551657)
        ·
          refine ⟨37602561370687801276913743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50136748494250401702551657 37602561370687801276913743)
          ·
            refine ⟨56403842056031701915370615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37602561370687801276913743 56403842056031701915370615)
            ·
              refine ⟨84605763084047552873055923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56403842056031701915370615 84605763084047552873055923)
              ·
                refine ⟨126908644626071329309583885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84605763084047552873055923 126908644626071329309583885)
                ·
                  refine ⟨47590741734776748491093957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126908644626071329309583885 47590741734776748491093957)
                  ·
                    refine ⟨8923264075270640342080117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47590741734776748491093957 8923264075270640342080117)
                    ·
                      refine ⟨836556007056622532070011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8923264075270640342080117 836556007056622532070011)
                      ·
                        rfl

theorem cell23_1629187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1629187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629187 prefixEnd_1629187 := by exact prefixLift 1629187
  have htrace : WordTrace (prefixWord ++ tailWord_1629187) baseStart_1629187 baseEnd_1629187 := by
    simpa [prefixWord, tailWord_1629187, baseEnd_1629187] using wordTrace_append hprefix tailTrace_1629187
  have hstable : (prefixWord ++ tailWord_1629187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629187).length < 2 ^ (prefixWord ++ tailWord_1629187).sum := by decide
  have hdescent : baseEnd_1629187 < baseStart_1629187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629191 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1629191 : Nat := 118140960795 + 1629191 * 2 ^ 59
def prefixEnd_1629191 : Nat := 4983230072969 + 3 ^ 40 * 1629191 * 2
def baseEnd_1629191 : Nat := 836558060979240516419993

theorem tailTrace_1629191 : CollatzResearch.WordTrace tailWord_1629191 prefixEnd_1629191 836558060979240516419993 := by
  unfold tailWord_1629191
  simp only [CollatzResearch.WordTrace]
  refine ⟨59421477440726725515799427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39614318293817817010532951 59421477440726725515799427)
  ·
    refine ⟨89132216161090088273699141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59421477440726725515799427 89132216161090088273699141)
    ·
      refine ⟨16712290530204391551318589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89132216161090088273699141 16712290530204391551318589)
      ·
        refine ⟨6267108948826646831744471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16712290530204391551318589 6267108948826646831744471)
        ·
          refine ⟨9400663423239970247616707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6267108948826646831744471 9400663423239970247616707)
          ·
            refine ⟨14100995134859955371425061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9400663423239970247616707 14100995134859955371425061)
            ·
              refine ⟨2643936587786241632142199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14100995134859955371425061 2643936587786241632142199)
              ·
                refine ⟨3965904881679362448213299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643936587786241632142199 3965904881679362448213299)
                ·
                  refine ⟨5948857322519043672319949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3965904881679362448213299 5948857322519043672319949)
                  ·
                    refine ⟨2230821495944641377119981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5948857322519043672319949 2230821495944641377119981)
                    ·
                      refine ⟨836558060979240516419993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230821495944641377119981 836558060979240516419993)
                      ·
                        rfl

theorem cell23_1629191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1629191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629191 prefixEnd_1629191 := by exact prefixLift 1629191
  have htrace : WordTrace (prefixWord ++ tailWord_1629191) baseStart_1629191 baseEnd_1629191 := by
    simpa [prefixWord, tailWord_1629191, baseEnd_1629191] using wordTrace_append hprefix tailTrace_1629191
  have hstable : (prefixWord ++ tailWord_1629191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629191).length < 2 ^ (prefixWord ++ tailWord_1629191).sum := by decide
  have hdescent : baseEnd_1629191 < baseStart_1629191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629212 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_1629212 : Nat := 118140960795 + 1629212 * 2 ^ 59
def prefixEnd_1629212 : Nat := 4983230072969 + 3 ^ 40 * 1629212 * 2
def baseEnd_1629212 : Nat := 836568844072984934257397

theorem tailTrace_1629212 : CollatzResearch.WordTrace tailWord_1629212 prefixEnd_1629212 836568844072984934257397 := by
  unfold tailWord_1629212
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711121686825323051156945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39614828915767097401542593 29711121686825323051156945)
  ·
    refine ⟨22283341265118992288367709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29711121686825323051156945 22283341265118992288367709)
    ·
      refine ⟨8356252974419622108137891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22283341265118992288367709 8356252974419622108137891)
      ·
        refine ⟨12534379461629433162206837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356252974419622108137891 12534379461629433162206837)
        ·
          refine ⟨1175098074527759358956891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12534379461629433162206837 1175098074527759358956891)
          ·
            refine ⟨1762647111791639038435337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175098074527759358956891 1762647111791639038435337)
            ·
              refine ⟨1321985333843729278826503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762647111791639038435337 1321985333843729278826503)
              ·
                refine ⟨1982978000765593918239755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321985333843729278826503 1982978000765593918239755)
                ·
                  refine ⟨2974467001148390877359633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982978000765593918239755 2974467001148390877359633)
                  ·
                    refine ⟨2230850250861293158019725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2974467001148390877359633 2230850250861293158019725)
                    ·
                      refine ⟨836568844072984934257397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230850250861293158019725 836568844072984934257397)
                      ·
                        rfl

theorem cell23_1629212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_1629212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629212 prefixEnd_1629212 := by exact prefixLift 1629212
  have htrace : WordTrace (prefixWord ++ tailWord_1629212) baseStart_1629212 baseEnd_1629212 := by
    simpa [prefixWord, tailWord_1629212, baseEnd_1629212] using wordTrace_append hprefix tailTrace_1629212
  have hstable : (prefixWord ++ tailWord_1629212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629212).length < 2 ^ (prefixWord ++ tailWord_1629212).sum := by decide
  have hdescent : baseEnd_1629212 < baseStart_1629212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629264 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_1629264 : Nat := 118140960795 + 1629264 * 2 ^ 59
def prefixEnd_1629264 : Nat := 4983230072969 + 3 ^ 40 * 1629264 * 2
def baseEnd_1629264 : Nat := 836595545067018730807157

theorem tailTrace_1629264 : CollatzResearch.WordTrace tailWord_1629264 prefixEnd_1629264 836595545067018730807157 := by
  unfold tailWord_1629264
  simp only [CollatzResearch.WordTrace]
  refine ⟨29712069984731129491603423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39616093312974839322137897 29712069984731129491603423)
  ·
    refine ⟨44568104977096694237405135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29712069984731129491603423 44568104977096694237405135)
    ·
      refine ⟨66852157465645041356107703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44568104977096694237405135 66852157465645041356107703)
      ·
        refine ⟨100278236198467562034161555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66852157465645041356107703 100278236198467562034161555)
        ·
          refine ⟨150417354297701343051242333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100278236198467562034161555 150417354297701343051242333)
          ·
            refine ⟨56406507861638003644215875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150417354297701343051242333 56406507861638003644215875)
            ·
              refine ⟨84609761792457005466323813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56406507861638003644215875 84609761792457005466323813)
              ·
                refine ⟨15864330336085688524935715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84609761792457005466323813 15864330336085688524935715)
                ·
                  refine ⟨23796495504128532787403573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15864330336085688524935715 23796495504128532787403573)
                  ·
                    refine ⟨2230921453512049948819085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23796495504128532787403573 2230921453512049948819085)
                    ·
                      refine ⟨836595545067018730807157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2230921453512049948819085 836595545067018730807157)
                      ·
                        rfl

theorem cell23_1629264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_1629264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629264 prefixEnd_1629264 := by exact prefixLift 1629264
  have htrace : WordTrace (prefixWord ++ tailWord_1629264) baseStart_1629264 baseEnd_1629264 := by
    simpa [prefixWord, tailWord_1629264, baseEnd_1629264] using wordTrace_append hprefix tailTrace_1629264
  have hstable : (prefixWord ++ tailWord_1629264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629264).length < 2 ^ (prefixWord ++ tailWord_1629264).sum := by decide
  have hdescent : baseEnd_1629264 < baseStart_1629264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629304 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_1629304 : Nat := 118140960795 + 1629304 * 2 ^ 59
def prefixEnd_1629304 : Nat := 4983230072969 + 3 ^ 40 * 1629304 * 2
def baseEnd_1629304 : Nat := 836616084293198574306973

theorem tailTrace_1629304 : CollatzResearch.WordTrace tailWord_1629304 prefixEnd_1629304 836616084293198574306973 := by
  unfold tailWord_1629304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29712799444658672907331483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39617065926211563876441977 29712799444658672907331483)
  ·
    refine ⟨44569199166988009360997225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29712799444658672907331483 44569199166988009360997225)
    ·
      refine ⟨33426899375241007020747919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44569199166988009360997225 33426899375241007020747919)
      ·
        refine ⟨50140349062861510531121879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33426899375241007020747919 50140349062861510531121879)
        ·
          refine ⟨75210523594292265796682819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50140349062861510531121879 75210523594292265796682819)
          ·
            refine ⟨112815785391438398695024229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75210523594292265796682819 112815785391438398695024229)
            ·
              refine ⟨21152959760894699755317043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112815785391438398695024229 21152959760894699755317043)
              ·
                refine ⟨31729439641342049632975565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21152959760894699755317043 31729439641342049632975565)
                ·
                  refine ⟨11898539865503268612365837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31729439641342049632975565 11898539865503268612365837)
                  ·
                    refine ⟨4461952449563725729637189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11898539865503268612365837 4461952449563725729637189)
                    ·
                      refine ⟨836616084293198574306973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4461952449563725729637189 836616084293198574306973)
                      ·
                        rfl

theorem cell23_1629304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_1629304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629304 prefixEnd_1629304 := by exact prefixLift 1629304
  have htrace : WordTrace (prefixWord ++ tailWord_1629304) baseStart_1629304 baseEnd_1629304 := by
    simpa [prefixWord, tailWord_1629304, baseEnd_1629304] using wordTrace_append hprefix tailTrace_1629304
  have hstable : (prefixWord ++ tailWord_1629304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629304).length < 2 ^ (prefixWord ++ tailWord_1629304).sum := by decide
  have hdescent : baseEnd_1629304 < baseStart_1629304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629321 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_1629321 : Nat := 118140960795 + 1629321 * 2 ^ 59
def prefixEnd_1629321 : Nat := 4983230072969 + 3 ^ 40 * 1629321 * 2
def baseEnd_1629321 : Nat := 836624813464325007794395

theorem tailTrace_1629321 : CollatzResearch.WordTrace tailWord_1629321 prefixEnd_1629321 836624813464325007794395 := by
  unfold tailWord_1629321
  simp only [CollatzResearch.WordTrace]
  refine ⟨59426218930255757718031817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39617479286837171812021211 59426218930255757718031817)
  ·
    refine ⟨44569664197691818288523863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59426218930255757718031817 44569664197691818288523863)
    ·
      refine ⟨66854496296537727432785795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44569664197691818288523863 66854496296537727432785795)
      ·
        refine ⟨100281744444806591149178693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66854496296537727432785795 100281744444806591149178693)
        ·
          refine ⟨18802827083401235840471005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100281744444806591149178693 18802827083401235840471005)
          ·
            refine ⟨7051060156275463440176627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18802827083401235840471005 7051060156275463440176627)
            ·
              refine ⟨10576590234413195160264941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051060156275463440176627 10576590234413195160264941)
              ·
                refine ⟨3966221337904948185099353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10576590234413195160264941 3966221337904948185099353)
                ·
                  refine ⟨2974666003428711138824515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3966221337904948185099353 2974666003428711138824515)
                  ·
                    refine ⟨4461999005143066708236773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2974666003428711138824515 4461999005143066708236773)
                    ·
                      refine ⟨836624813464325007794395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4461999005143066708236773 836624813464325007794395)
                      ·
                        rfl

theorem cell23_1629321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_1629321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629321 prefixEnd_1629321 := by exact prefixLift 1629321
  have htrace : WordTrace (prefixWord ++ tailWord_1629321) baseStart_1629321 baseEnd_1629321 := by
    simpa [prefixWord, tailWord_1629321, baseEnd_1629321] using wordTrace_append hprefix tailTrace_1629321
  have hstable : (prefixWord ++ tailWord_1629321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629321).length < 2 ^ (prefixWord ++ tailWord_1629321).sum := by decide
  have hdescent : baseEnd_1629321 < baseStart_1629321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629338 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1629338 : Nat := 118140960795 + 1629338 * 2 ^ 59
def prefixEnd_1629338 : Nat := 4983230072969 + 3 ^ 40 * 1629338 * 2
def baseEnd_1629338 : Nat := 836633542635451441281817

theorem tailTrace_1629338 : CollatzResearch.WordTrace tailWord_1629338 prefixEnd_1629338 836633542635451441281817 := by
  unfold tailWord_1629338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856709742798542405350167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39617892647462779747600445 14856709742798542405350167)
  ·
    refine ⟨22285064614197813608025251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14856709742798542405350167 22285064614197813608025251)
    ·
      refine ⟨33427596921296720412037877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22285064614197813608025251 33427596921296720412037877)
      ·
        refine ⟨3133837211371567538628551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33427596921296720412037877 3133837211371567538628551)
        ·
          refine ⟨4700755817057351307942827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133837211371567538628551 4700755817057351307942827)
          ·
            refine ⟨7051133725586026961914241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700755817057351307942827 7051133725586026961914241)
            ·
              refine ⟨5288350294189520221435681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051133725586026961914241 5288350294189520221435681)
              ·
                refine ⟨3966262720642140166076761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5288350294189520221435681 3966262720642140166076761)
                ·
                  refine ⟨2974697040481605124557571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3966262720642140166076761 2974697040481605124557571)
                  ·
                    refine ⟨4462045560722407686836357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2974697040481605124557571 4462045560722407686836357)
                    ·
                      refine ⟨836633542635451441281817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4462045560722407686836357 836633542635451441281817)
                      ·
                        rfl

theorem cell23_1629338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1629338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629338 prefixEnd_1629338 := by exact prefixLift 1629338
  have htrace : WordTrace (prefixWord ++ tailWord_1629338) baseStart_1629338 baseEnd_1629338 := by
    simpa [prefixWord, tailWord_1629338, baseEnd_1629338] using wordTrace_append hprefix tailTrace_1629338
  have hstable : (prefixWord ++ tailWord_1629338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629338).length < 2 ^ (prefixWord ++ tailWord_1629338).sum := by decide
  have hdescent : baseEnd_1629338 < baseStart_1629338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629451 : List Nat := [1, 1, 1, 1, 5, 5, 9]
def baseStart_1629451 : Nat := 118140960795 + 1629451 * 2 ^ 59
def prefixEnd_1629451 : Nat := 4983230072969 + 3 ^ 40 * 1629451 * 2
def baseEnd_1629451 : Nat := 10329525505548265421837

theorem tailTrace_1629451 : CollatzResearch.WordTrace tailWord_1629451 prefixEnd_1629451 10329525505548265421837 := by
  unfold tailWord_1629451
  simp only [CollatzResearch.WordTrace]
  refine ⟨59430960419784789920264207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39620640279856526613509471 59430960419784789920264207)
  ·
    refine ⟨89146440629677184880396311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59430960419784789920264207 89146440629677184880396311)
    ·
      refine ⟨133719660944515777320594467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89146440629677184880396311 133719660944515777320594467)
      ·
        refine ⟨200579491416773665980891701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133719660944515777320594467 200579491416773665980891701)
        ·
          refine ⟨18804327320322531185708597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200579491416773665980891701 18804327320322531185708597)
          ·
            refine ⟨1762905686280237298660181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18804327320322531185708597 1762905686280237298660181)
            ·
              refine ⟨10329525505548265421837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1762905686280237298660181 10329525505548265421837)
              ·
                rfl

theorem cell23_1629451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 9].length) (baseStart_1629451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629451 prefixEnd_1629451 := by exact prefixLift 1629451
  have htrace : WordTrace (prefixWord ++ tailWord_1629451) baseStart_1629451 baseEnd_1629451 := by
    simpa [prefixWord, tailWord_1629451, baseEnd_1629451] using wordTrace_append hprefix tailTrace_1629451
  have hstable : (prefixWord ++ tailWord_1629451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629451).length < 2 ^ (prefixWord ++ tailWord_1629451).sum := by decide
  have hdescent : baseEnd_1629451 < baseStart_1629451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629482 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1629482 : Nat := 118140960795 + 1629482 * 2 ^ 59
def prefixEnd_1629482 : Nat := 4983230072969 + 3 ^ 40 * 1629482 * 2
def baseEnd_1629482 : Nat := 836707483849698877881155

theorem tailTrace_1629482 : CollatzResearch.WordTrace tailWord_1629482 prefixEnd_1629482 836707483849698877881155 := by
  unfold tailWord_1629482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858022770668120553660675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39621394055114988143095133 14858022770668120553660675)
  ·
    refine ⟨22287034156002180830491013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14858022770668120553660675 22287034156002180830491013)
    ·
      refine ⟨4178818904250408905717065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22287034156002180830491013 4178818904250408905717065)
      ·
        refine ⟨3134114178187806679287799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4178818904250408905717065 3134114178187806679287799)
        ·
          refine ⟨4701171267281710018931699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134114178187806679287799 4701171267281710018931699)
          ·
            refine ⟨7051756900922565028397549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701171267281710018931699 7051756900922565028397549)
            ·
              refine ⟨2644408837845961885649081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7051756900922565028397549 2644408837845961885649081)
              ·
                refine ⟨1983306628384471414236811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644408837845961885649081 1983306628384471414236811)
                ·
                  refine ⟨2974959942576707121355217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983306628384471414236811 2974959942576707121355217)
                  ·
                    refine ⟨2231219956932530341016413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2974959942576707121355217 2231219956932530341016413)
                    ·
                      refine ⟨836707483849698877881155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2231219956932530341016413 836707483849698877881155)
                      ·
                        rfl

theorem cell23_1629482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1629482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629482 prefixEnd_1629482 := by exact prefixLift 1629482
  have htrace : WordTrace (prefixWord ++ tailWord_1629482) baseStart_1629482 baseEnd_1629482 := by
    simpa [prefixWord, tailWord_1629482, baseEnd_1629482] using wordTrace_append hprefix tailTrace_1629482
  have hstable : (prefixWord ++ tailWord_1629482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629482).length < 2 ^ (prefixWord ++ tailWord_1629482).sum := by decide
  have hdescent : baseEnd_1629482 < baseStart_1629482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629526 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1629526 : Nat := 118140960795 + 1629526 * 2 ^ 59
def prefixEnd_1629526 : Nat := 4983230072969 + 3 ^ 40 * 1629526 * 2
def baseEnd_1629526 : Nat := 836730076998496705730953

theorem tailTrace_1629526 : CollatzResearch.WordTrace tailWord_1629526 prefixEnd_1629526 836730076998496705730953 := by
  unfold tailWord_1629526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714605993407067358077777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39622463929675385152829621 3714605993407067358077777)
  ·
    refine ⟨2785954495055300518558333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3714605993407067358077777 2785954495055300518558333)
    ·
      refine ⟨1044732935645737694459375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2785954495055300518558333 1044732935645737694459375)
      ·
        refine ⟨1567099403468606541689063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044732935645737694459375 1567099403468606541689063)
        ·
          refine ⟨2350649105202909812533595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567099403468606541689063 2350649105202909812533595)
          ·
            refine ⟨3525973657804364718800393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350649105202909812533595 3525973657804364718800393)
            ·
              refine ⟨2644480243353273539100295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525973657804364718800393 2644480243353273539100295)
              ·
                refine ⟨3966720365029910308650443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644480243353273539100295 3966720365029910308650443)
                ·
                  refine ⟨5950080547544865462975665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966720365029910308650443 5950080547544865462975665)
                  ·
                    refine ⟨4462560410658649097231749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5950080547544865462975665 4462560410658649097231749)
                    ·
                      refine ⟨836730076998496705730953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4462560410658649097231749 836730076998496705730953)
                      ·
                        rfl

theorem cell23_1629526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1629526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629526 prefixEnd_1629526 := by exact prefixLift 1629526
  have htrace : WordTrace (prefixWord ++ tailWord_1629526) baseStart_1629526 baseEnd_1629526 := by
    simpa [prefixWord, tailWord_1629526, baseEnd_1629526] using wordTrace_append hprefix tailTrace_1629526
  have hstable : (prefixWord ++ tailWord_1629526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629526).length < 2 ^ (prefixWord ++ tailWord_1629526).sum := by decide
  have hdescent : baseEnd_1629526 < baseStart_1629526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629535 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 6, 2, 2]
def baseStart_1629535 : Nat := 118140960795 + 1629535 * 2 ^ 59
def prefixEnd_1629535 : Nat := 4983230072969 + 3 ^ 40 * 1629535 * 2
def baseEnd_1629535 : Nat := 836734698324387170518411

theorem tailTrace_1629535 : CollatzResearch.WordTrace tailWord_1629535 prefixEnd_1629535 836734698324387170518411 := by
  unfold tailWord_1629535
  simp only [CollatzResearch.WordTrace]
  refine ⟨59434024151480472266322059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39622682767653648177548039 59434024151480472266322059)
  ·
    refine ⟨89151036227220708399483089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59434024151480472266322059 89151036227220708399483089)
    ·
      refine ⟨66863277170415531299612317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89151036227220708399483089 66863277170415531299612317)
      ·
        refine ⟨25073728938905824237354619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66863277170415531299612317 25073728938905824237354619)
        ·
          refine ⟨37610593408358736356031929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25073728938905824237354619 37610593408358736356031929)
          ·
            refine ⟨28207945056269052267023947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37610593408358736356031929 28207945056269052267023947)
            ·
              refine ⟨42311917584403578400535921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28207945056269052267023947 42311917584403578400535921)
              ·
                refine ⟨31733938188302683800401941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42311917584403578400535921 31733938188302683800401941)
                ·
                  refine ⟨1487528352576688303143841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31733938188302683800401941 1487528352576688303143841)
                  ·
                    refine ⟨1115646264432516227357881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487528352576688303143841 1115646264432516227357881)
                    ·
                      refine ⟨836734698324387170518411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115646264432516227357881 836734698324387170518411)
                      ·
                        rfl

theorem cell23_1629535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_1629535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629535 prefixEnd_1629535 := by exact prefixLift 1629535
  have htrace : WordTrace (prefixWord ++ tailWord_1629535) baseStart_1629535 baseEnd_1629535 := by
    simpa [prefixWord, tailWord_1629535, baseEnd_1629535] using wordTrace_append hprefix tailTrace_1629535
  have hstable : (prefixWord ++ tailWord_1629535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629535).length < 2 ^ (prefixWord ++ tailWord_1629535).sum := by decide
  have hdescent : baseEnd_1629535 < baseStart_1629535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629569 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_1629569 : Nat := 118140960795 + 1629569 * 2 ^ 59
def prefixEnd_1629569 : Nat := 4983230072969 + 3 ^ 40 * 1629569 * 2
def baseEnd_1629569 : Nat := 836752156666640037493255

theorem tailTrace_1629569 : CollatzResearch.WordTrace tailWord_1629569 prefixEnd_1629569 836752156666640037493255 := by
  unfold tailWord_1629569
  simp only [CollatzResearch.WordTrace]
  refine ⟨59435264233357296073059761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39623509488904864048706507 59435264233357296073059761)
  ·
    refine ⟨44576448175017972054794821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59435264233357296073059761 44576448175017972054794821)
    ·
      refine ⟨8358084032815869760274029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44576448175017972054794821 8358084032815869760274029)
      ·
        refine ⟨3134281512305951160102761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8358084032815869760274029 3134281512305951160102761)
        ·
          refine ⟨2350711134229463370077071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134281512305951160102761 2350711134229463370077071)
          ·
            refine ⟨3526066701344195055115607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350711134229463370077071 3526066701344195055115607)
            ·
              refine ⟨5289100052016292582673411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526066701344195055115607 5289100052016292582673411)
              ·
                refine ⟨7933650078024438874010117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289100052016292582673411 7933650078024438874010117)
                ·
                  refine ⟨1487559389629582288876897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7933650078024438874010117 1487559389629582288876897)
                  ·
                    refine ⟨1115669542222186716657673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487559389629582288876897 1115669542222186716657673)
                    ·
                      refine ⟨836752156666640037493255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115669542222186716657673 836752156666640037493255)
                      ·
                        rfl

theorem cell23_1629569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_1629569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629569 prefixEnd_1629569 := by exact prefixLift 1629569
  have htrace : WordTrace (prefixWord ++ tailWord_1629569) baseStart_1629569 baseEnd_1629569 := by
    simpa [prefixWord, tailWord_1629569, baseEnd_1629569] using wordTrace_append hprefix tailTrace_1629569
  have hstable : (prefixWord ++ tailWord_1629569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629569).length < 2 ^ (prefixWord ++ tailWord_1629569).sum := by decide
  have hdescent : baseEnd_1629569 < baseStart_1629569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629575 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 5]
def baseStart_1629575 : Nat := 118140960795 + 1629575 * 2 ^ 59
def prefixEnd_1629575 : Nat := 4983230072969 + 3 ^ 40 * 1629575 * 2
def baseEnd_1629575 : Nat := 92972804172285223779803

theorem tailTrace_1629575 : CollatzResearch.WordTrace tailWord_1629575 prefixEnd_1629575 92972804172285223779803 := by
  unfold tailWord_1629575
  simp only [CollatzResearch.WordTrace]
  refine ⟨59435483071335559097778179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39623655380890372731852119 59435483071335559097778179)
  ·
    refine ⟨89153224607003338646667269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59435483071335559097778179 89153224607003338646667269)
    ·
      refine ⟨16716229613813125996250113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89153224607003338646667269 16716229613813125996250113)
      ·
        refine ⟨12537172210359844497187585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16716229613813125996250113 12537172210359844497187585)
        ·
          refine ⟨9402879157769883372890689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12537172210359844497187585 9402879157769883372890689)
          ·
            refine ⟨7052159368327412529668017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9402879157769883372890689 7052159368327412529668017)
            ·
              refine ⟨5289119526245559397251013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7052159368327412529668017 5289119526245559397251013)
              ·
                refine ⟨991709911171042386984565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5289119526245559397251013 991709911171042386984565)
                ·
                  refine ⟨92972804172285223779803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 991709911171042386984565 92972804172285223779803)
                  ·
                    rfl

theorem cell23_1629575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 5].length) (baseStart_1629575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629575 prefixEnd_1629575 := by exact prefixLift 1629575
  have htrace : WordTrace (prefixWord ++ tailWord_1629575) baseStart_1629575 baseEnd_1629575 := by
    simpa [prefixWord, tailWord_1629575, baseEnd_1629575] using wordTrace_append hprefix tailTrace_1629575
  have hstable : (prefixWord ++ tailWord_1629575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629575).length < 2 ^ (prefixWord ++ tailWord_1629575).sum := by decide
  have hdescent : baseEnd_1629575 < baseStart_1629575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629586 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1629586 : Nat := 118140960795 + 1629586 * 2 ^ 59
def prefixEnd_1629586 : Nat := 4983230072969 + 3 ^ 40 * 1629586 * 2
def baseEnd_1629586 : Nat := 836760885837766470980677

theorem tailTrace_1629586 : CollatzResearch.WordTrace tailWord_1629586 prefixEnd_1629586 836760885837766470980677 := by
  unfold tailWord_1629586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858971068573926994107153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39623922849530471984285741 14858971068573926994107153)
  ·
    refine ⟨11144228301430445245580365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14858971068573926994107153 11144228301430445245580365)
    ·
      refine ⟨4179085613036416967092637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11144228301430445245580365 4179085613036416967092637)
      ·
        refine ⟨1567157104888656362659739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4179085613036416967092637 1567157104888656362659739)
        ·
          refine ⟨2350735657332984543989609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567157104888656362659739 2350735657332984543989609)
          ·
            refine ⟨1763051742999738407992207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350735657332984543989609 1763051742999738407992207)
            ·
              refine ⟨2644577614499607611988311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763051742999738407992207 2644577614499607611988311)
              ·
                refine ⟨3966866421749411417982467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644577614499607611988311 3966866421749411417982467)
                ·
                  refine ⟨5950299632624117126973701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966866421749411417982467 5950299632624117126973701)
                  ·
                    refine ⟨1115681181117021961307569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950299632624117126973701 1115681181117021961307569)
                    ·
                      refine ⟨836760885837766470980677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115681181117021961307569 836760885837766470980677)
                      ·
                        rfl

theorem cell23_1629586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1629586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629586 prefixEnd_1629586 := by exact prefixLift 1629586
  have htrace : WordTrace (prefixWord ++ tailWord_1629586) baseStart_1629586 baseEnd_1629586 := by
    simpa [prefixWord, tailWord_1629586, baseEnd_1629586] using wordTrace_append hprefix tailTrace_1629586
  have hstable : (prefixWord ++ tailWord_1629586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629586).length < 2 ^ (prefixWord ++ tailWord_1629586).sum := by decide
  have hdescent : baseEnd_1629586 < baseStart_1629586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629635 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 3, 4]
def baseStart_1629635 : Nat := 118140960795 + 1629635 * 2 ^ 59
def prefixEnd_1629635 : Nat := 4983230072969 + 3 ^ 40 * 1629635 * 2
def baseEnd_1629635 : Nat := 278928682129945593089317

theorem tailTrace_1629635 : CollatzResearch.WordTrace tailWord_1629635 prefixEnd_1629635 278928682129945593089317 := by
  unfold tailWord_1629635
  simp only [CollatzResearch.WordTrace]
  refine ⟨59437671451118189344962359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39625114300745459563308239 59437671451118189344962359)
  ·
    refine ⟨89156507176677284017443539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59437671451118189344962359 89156507176677284017443539)
    ·
      refine ⟨133734760765015926026165309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89156507176677284017443539 133734760765015926026165309)
      ·
        refine ⟨50150535286880972259811991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133734760765015926026165309 50150535286880972259811991)
        ·
          refine ⟨75225802930321458389717987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50150535286880972259811991 75225802930321458389717987)
          ·
            refine ⟨112838704395482187584576981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75225802930321458389717987 112838704395482187584576981)
            ·
              refine ⟨2644657134269113771513523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112838704395482187584576981 2644657134269113771513523)
              ·
                refine ⟨3966985701403670657270285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644657134269113771513523 3966985701403670657270285)
                ·
                  refine ⟨1487619638026376496476357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3966985701403670657270285 1487619638026376496476357)
                  ·
                    refine ⟨278928682129945593089317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487619638026376496476357 278928682129945593089317)
                    ·
                      rfl

theorem cell23_1629635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 4].length) (baseStart_1629635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629635 prefixEnd_1629635 := by exact prefixLift 1629635
  have htrace : WordTrace (prefixWord ++ tailWord_1629635) baseStart_1629635 baseEnd_1629635 := by
    simpa [prefixWord, tailWord_1629635, baseEnd_1629635] using wordTrace_append hprefix tailTrace_1629635
  have hstable : (prefixWord ++ tailWord_1629635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629635).length < 2 ^ (prefixWord ++ tailWord_1629635).sum := by decide
  have hdescent : baseEnd_1629635 < baseStart_1629635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629648 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 6]
def baseStart_1629648 : Nat := 118140960795 + 1629648 * 2 ^ 59
def prefixEnd_1629648 : Nat := 4983230072969 + 3 ^ 40 * 1629648 * 2
def baseEnd_1629648 : Nat := 92976969070927247600599

theorem tailTrace_1629648 : CollatzResearch.WordTrace tailWord_1629648 prefixEnd_1629648 92976969070927247600599 := by
  unfold tailWord_1629648
  simp only [CollatzResearch.WordTrace]
  refine ⟨29719072800035546282592799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39625430400047395043457065 29719072800035546282592799)
  ·
    refine ⟨44578609200053319423889199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29719072800035546282592799 44578609200053319423889199)
    ·
      refine ⟨66867913800079979135833799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44578609200053319423889199 66867913800079979135833799)
      ·
        refine ⟨100301870700119968703750699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66867913800079979135833799 100301870700119968703750699)
        ·
          refine ⟨150452806050179953055626049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100301870700119968703750699 150452806050179953055626049)
          ·
            refine ⟨112839604537634964791719537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150452806050179953055626049 112839604537634964791719537)
            ·
              refine ⟨84629703403226223593789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112839604537634964791719537 84629703403226223593789653)
              ·
                refine ⟨1983508673513114615479445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84629703403226223593789653 1983508673513114615479445)
                ·
                  refine ⟨92976969070927247600599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1983508673513114615479445 92976969070927247600599)
                  ·
                    rfl

theorem cell23_1629648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_1629648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629648 prefixEnd_1629648 := by exact prefixLift 1629648
  have htrace : WordTrace (prefixWord ++ tailWord_1629648) baseStart_1629648 baseEnd_1629648 := by
    simpa [prefixWord, tailWord_1629648, baseEnd_1629648] using wordTrace_append hprefix tailTrace_1629648
  have hstable : (prefixWord ++ tailWord_1629648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629648).length < 2 ^ (prefixWord ++ tailWord_1629648).sum := by decide
  have hdescent : baseEnd_1629648 < baseStart_1629648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629675 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 3]
def baseStart_1629675 : Nat := 118140960795 + 1629675 * 2 ^ 59
def prefixEnd_1629675 : Nat := 4983230072969 + 3 ^ 40 * 1629675 * 2
def baseEnd_1629675 : Nat := 836806585616016622767767

theorem tailTrace_1629675 : CollatzResearch.WordTrace tailWord_1629675 prefixEnd_1629675 836806585616016622767767 := by
  unfold tailWord_1629675
  simp only [CollatzResearch.WordTrace]
  refine ⟨59439130370973276176418479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39626086913982184117612319 59439130370973276176418479)
  ·
    refine ⟨89158695556459914264627719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59439130370973276176418479 89158695556459914264627719)
    ·
      refine ⟨133738043334689871396941579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89158695556459914264627719 133738043334689871396941579)
      ·
        refine ⟨200607065002034807095412369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133738043334689871396941579 200607065002034807095412369)
        ·
          refine ⟨150455298751526105321559277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200607065002034807095412369 150455298751526105321559277)
          ·
            refine ⟨56420737031822289495584729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150455298751526105321559277 56420737031822289495584729)
            ·
              refine ⟨42315552773866717121688547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56420737031822289495584729 42315552773866717121688547)
              ·
                refine ⟨63473329160800075682532821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42315552773866717121688547 63473329160800075682532821)
                ·
                  refine ⟨1487656152206251773809363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63473329160800075682532821 1487656152206251773809363)
                  ·
                    refine ⟨2231484228309377660714045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1487656152206251773809363 2231484228309377660714045)
                    ·
                      refine ⟨836806585616016622767767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2231484228309377660714045 836806585616016622767767)
                      ·
                        rfl

theorem cell23_1629675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 3].length) (baseStart_1629675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629675 prefixEnd_1629675 := by exact prefixLift 1629675
  have htrace : WordTrace (prefixWord ++ tailWord_1629675) baseStart_1629675 baseEnd_1629675 := by
    simpa [prefixWord, tailWord_1629675, baseEnd_1629675] using wordTrace_append hprefix tailTrace_1629675
  have hstable : (prefixWord ++ tailWord_1629675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629675).length < 2 ^ (prefixWord ++ tailWord_1629675).sum := by decide
  have hdescent : baseEnd_1629675 < baseStart_1629675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629682 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_1629682 : Nat := 118140960795 + 1629682 * 2 ^ 59
def prefixEnd_1629682 : Nat := 4983230072969 + 3 ^ 40 * 1629682 * 2
def baseEnd_1629682 : Nat := 92978908886733121708915

theorem tailTrace_1629682 : CollatzResearch.WordTrace tailWord_1629682 prefixEnd_1629682 92978908886733121708915 := by
  unfold tailWord_1629682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14859846420486979092980825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39626257121298610914615533 14859846420486979092980825)
  ·
    refine ⟨11144884815365234319735619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14859846420486979092980825 11144884815365234319735619)
    ·
      refine ⟨16717327223047851479603429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11144884815365234319735619 16717327223047851479603429)
      ·
        refine ⟨3134498854321472152425643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16717327223047851479603429 3134498854321472152425643)
        ·
          refine ⟨4701748281482208228638465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134498854321472152425643 4701748281482208228638465)
          ·
            refine ⟨3526311211111656171478849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4701748281482208228638465 3526311211111656171478849)
            ·
              refine ⟨2644733408333742128609137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3526311211111656171478849 2644733408333742128609137)
              ·
                refine ⟨1983550056250306596456853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644733408333742128609137 1983550056250306596456853)
                ·
                  refine ⟨92978908886733121708915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1983550056250306596456853 92978908886733121708915)
                  ·
                    rfl

theorem cell23_1629682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_1629682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629682 prefixEnd_1629682 := by exact prefixLift 1629682
  have htrace : WordTrace (prefixWord ++ tailWord_1629682) baseStart_1629682 baseEnd_1629682 := by
    simpa [prefixWord, tailWord_1629682, baseEnd_1629682] using wordTrace_append hprefix tailTrace_1629682
  have hstable : (prefixWord ++ tailWord_1629682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629682).length < 2 ^ (prefixWord ++ tailWord_1629682).sum := by decide
  have hdescent : baseEnd_1629682 < baseStart_1629682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629686 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1629686 : Nat := 118140960795 + 1629686 * 2 ^ 59
def prefixEnd_1629686 : Nat := 4983230072969 + 3 ^ 40 * 1629686 * 2
def baseEnd_1629686 : Nat := 278937411301072026576739

theorem tailTrace_1629686 : CollatzResearch.WordTrace tailWord_1629686 prefixEnd_1629686 278937411301072026576739 := by
  unfold tailWord_1629686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714970723370839065941807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39626354382622283370045941 3714970723370839065941807)
  ·
    refine ⟨5572456085056258598912711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714970723370839065941807 5572456085056258598912711)
    ·
      refine ⟨8358684127584387898369067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572456085056258598912711 8358684127584387898369067)
      ·
        refine ⟨12538026191376581847553601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8358684127584387898369067 12538026191376581847553601)
        ·
          refine ⟨9403519643532436385665201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12538026191376581847553601 9403519643532436385665201)
          ·
            refine ⟨7052639732649327289248901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9403519643532436385665201 7052639732649327289248901)
            ·
              refine ⟨1322369949871748866734169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7052639732649327289248901 1322369949871748866734169)
              ·
                refine ⟨991777462403811650050627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322369949871748866734169 991777462403811650050627)
                ·
                  refine ⟨1487666193605717475075941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991777462403811650050627 1487666193605717475075941)
                  ·
                    refine ⟨278937411301072026576739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487666193605717475075941 278937411301072026576739)
                    ·
                      rfl

theorem cell23_1629686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1629686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629686 prefixEnd_1629686 := by exact prefixLift 1629686
  have htrace : WordTrace (prefixWord ++ tailWord_1629686) baseStart_1629686 baseEnd_1629686 := by
    simpa [prefixWord, tailWord_1629686, baseEnd_1629686] using wordTrace_append hprefix tailTrace_1629686
  have hstable : (prefixWord ++ tailWord_1629686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629686).length < 2 ^ (prefixWord ++ tailWord_1629686).sum := by decide
  have hdescent : baseEnd_1629686 < baseStart_1629686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629715 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 4]
def baseStart_1629715 : Nat := 118140960795 + 1629715 * 2 ^ 59
def prefixEnd_1629715 : Nat := 4983230072969 + 3 ^ 40 * 1629715 * 2
def baseEnd_1629715 : Nat := 836827124842196466267583

theorem tailTrace_1629715 : CollatzResearch.WordTrace tailWord_1629715 prefixEnd_1629715 836827124842196466267583 := by
  unfold tailWord_1629715
  simp only [CollatzResearch.WordTrace]
  refine ⟨59440589290828363007874599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39627059527218908671916399 59440589290828363007874599)
  ·
    refine ⟨89160883936242544511811899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59440589290828363007874599 89160883936242544511811899)
    ·
      refine ⟨133741325904363816767717849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89160883936242544511811899 133741325904363816767717849)
      ·
        refine ⟨100305994428272862575788387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133741325904363816767717849 100305994428272862575788387)
        ·
          refine ⟨150458991642409293863682581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100305994428272862575788387 150458991642409293863682581)
          ·
            refine ⟨7052765233237935649860121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150458991642409293863682581 7052765233237935649860121)
            ·
              refine ⟨5289573924928451737395091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7052765233237935649860121 5289573924928451737395091)
              ·
                refine ⟨7934360887392677606092637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289573924928451737395091 7934360887392677606092637)
                ·
                  refine ⟨2975385332772254102284739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7934360887392677606092637 2975385332772254102284739)
                  ·
                    refine ⟨4463077999158381153427109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975385332772254102284739 4463077999158381153427109)
                    ·
                      refine ⟨836827124842196466267583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4463077999158381153427109 836827124842196466267583)
                      ·
                        rfl

theorem cell23_1629715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_1629715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629715 prefixEnd_1629715 := by exact prefixLift 1629715
  have htrace : WordTrace (prefixWord ++ tailWord_1629715) baseStart_1629715 baseEnd_1629715 := by
    simpa [prefixWord, tailWord_1629715, baseEnd_1629715] using wordTrace_append hprefix tailTrace_1629715
  have hstable : (prefixWord ++ tailWord_1629715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629715).length < 2 ^ (prefixWord ++ tailWord_1629715).sum := by decide
  have hdescent : baseEnd_1629715 < baseStart_1629715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629725 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1629725 : Nat := 118140960795 + 1629725 * 2 ^ 59
def prefixEnd_1629725 : Nat := 4983230072969 + 3 ^ 40 * 1629725 * 2
def baseEnd_1629725 : Nat := 278944086549580475714179

theorem tailTrace_1629725 : CollatzResearch.WordTrace tailWord_1629725 prefixEnd_1629725 278944086549580475714179 := by
  unfold tailWord_1629725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59440954020792134715738629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39627302680528089810492419 59440954020792134715738629)
  ·
    refine ⟨11145178878898525259200993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59440954020792134715738629 11145178878898525259200993)
    ·
      refine ⟨8358884159173893944400745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11145178878898525259200993 8358884159173893944400745)
      ·
        refine ⟨6269163119380420458300559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8358884159173893944400745 6269163119380420458300559)
        ·
          refine ⟨9403744679070630687450839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269163119380420458300559 9403744679070630687450839)
          ·
            refine ⟨14105617018605946031176259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9403744679070630687450839 14105617018605946031176259)
            ·
              refine ⟨21158425527908919046764389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14105617018605946031176259 21158425527908919046764389)
              ·
                refine ⟨3967204786482922321268323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21158425527908919046764389 3967204786482922321268323)
                ·
                  refine ⟨5950807179724383481902485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967204786482922321268323 5950807179724383481902485)
                  ·
                    refine ⟨278944086549580475714179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5950807179724383481902485 278944086549580475714179)
                    ·
                      rfl

theorem cell23_1629725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1629725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629725 prefixEnd_1629725 := by exact prefixLift 1629725
  have htrace : WordTrace (prefixWord ++ tailWord_1629725) baseStart_1629725 baseEnd_1629725 := by
    simpa [prefixWord, tailWord_1629725, baseEnd_1629725] using wordTrace_append hprefix tailTrace_1629725
  have hstable : (prefixWord ++ tailWord_1629725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629725).length < 2 ^ (prefixWord ++ tailWord_1629725).sum := by decide
  have hdescent : baseEnd_1629725 < baseStart_1629725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629729 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 1, 5]
def baseStart_1629729 : Nat := 118140960795 + 1629729 * 2 ^ 59
def prefixEnd_1629729 : Nat := 4983230072969 + 3 ^ 40 * 1629729 * 2
def baseEnd_1629729 : Nat := 278944771190453137164173

theorem tailTrace_1629729 : CollatzResearch.WordTrace tailWord_1629729 prefixEnd_1629729 278944771190453137164173 := by
  unfold tailWord_1629729
  simp only [CollatzResearch.WordTrace]
  refine ⟨59441099912777643398884241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39627399941851762265922827 59441099912777643398884241)
  ·
    refine ⟨44580824934583232549163181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59441099912777643398884241 44580824934583232549163181)
    ·
      refine ⟨16717809350468712205936193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44580824934583232549163181 16717809350468712205936193)
      ·
        refine ⟨12538357012851534154452145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16717809350468712205936193 12538357012851534154452145)
        ·
          refine ⟨9403767759638650615839109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12538357012851534154452145 9403767759638650615839109)
          ·
            refine ⟨1763206454932246990469833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9403767759638650615839109 1763206454932246990469833)
            ·
              refine ⟨1322404841199185242852375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763206454932246990469833 1322404841199185242852375)
              ·
                refine ⟨1983607261798777864278563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322404841199185242852375 1983607261798777864278563)
                ·
                  refine ⟨2975410892698166796417845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983607261798777864278563 2975410892698166796417845)
                  ·
                    refine ⟨278944771190453137164173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2975410892698166796417845 278944771190453137164173)
                    ·
                      rfl

theorem cell23_1629729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_1629729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629729 prefixEnd_1629729 := by exact prefixLift 1629729
  have htrace : WordTrace (prefixWord ++ tailWord_1629729) baseStart_1629729 baseEnd_1629729 := by
    simpa [prefixWord, tailWord_1629729, baseEnd_1629729] using wordTrace_append hprefix tailTrace_1629729
  have hstable : (prefixWord ++ tailWord_1629729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629729).length < 2 ^ (prefixWord ++ tailWord_1629729).sum := by decide
  have hdescent : baseEnd_1629729 < baseStart_1629729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629749 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_1629749 : Nat := 118140960795 + 1629749 * 2 ^ 59
def prefixEnd_1629749 : Nat := 4983230072969 + 3 ^ 40 * 1629749 * 2
def baseEnd_1629749 : Nat := 836844583184449333242427

theorem tailTrace_1629749 : CollatzResearch.WordTrace tailWord_1629749 prefixEnd_1629749 836844583184449333242427 := by
  unfold tailWord_1629749
  simp only [CollatzResearch.WordTrace]
  refine ⟨59441829372705186814612301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39627886248470124543074867 59441829372705186814612301)
  ·
    refine ⟨22290686014764445055479613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59441829372705186814612301 22290686014764445055479613)
    ·
      refine ⟨8359007255536666895804855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22290686014764445055479613 8359007255536666895804855)
      ·
        refine ⟨12538510883305000343707283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8359007255536666895804855 12538510883305000343707283)
        ·
          refine ⟨18807766324957500515560925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12538510883305000343707283 18807766324957500515560925)
          ·
            refine ⟨7052912371859062693335347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18807766324957500515560925 7052912371859062693335347)
            ·
              refine ⟨10579368557788594040003021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052912371859062693335347 10579368557788594040003021)
              ·
                refine ⟨3967263209170722765001133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10579368557788594040003021 3967263209170722765001133)
                ·
                  refine ⟨1487723703439021036875425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3967263209170722765001133 1487723703439021036875425)
                  ·
                    refine ⟨1115792777579265777656569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487723703439021036875425 1115792777579265777656569)
                    ·
                      refine ⟨836844583184449333242427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115792777579265777656569 836844583184449333242427)
                      ·
                        rfl

theorem cell23_1629749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_1629749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629749 prefixEnd_1629749 := by exact prefixLift 1629749
  have htrace : WordTrace (prefixWord ++ tailWord_1629749) baseStart_1629749 baseEnd_1629749 := by
    simpa [prefixWord, tailWord_1629749, baseEnd_1629749] using wordTrace_append hprefix tailTrace_1629749
  have hstable : (prefixWord ++ tailWord_1629749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629749).length < 2 ^ (prefixWord ++ tailWord_1629749).sum := by decide
  have hdescent : baseEnd_1629749 < baseStart_1629749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629759 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 2, 4]
def baseStart_1629759 : Nat := 118140960795 + 1629759 * 2 ^ 59
def prefixEnd_1629759 : Nat := 4983230072969 + 3 ^ 40 * 1629759 * 2
def baseEnd_1629759 : Nat := 278949905996998098039127

theorem tailTrace_1629759 : CollatzResearch.WordTrace tailWord_1629759 prefixEnd_1629759 278949905996998098039127 := by
  unfold tailWord_1629759
  simp only [CollatzResearch.WordTrace]
  refine ⟨59442194102668958522476331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39628129401779305681650887 59442194102668958522476331)
  ·
    refine ⟨89163291154003437783714497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59442194102668958522476331 89163291154003437783714497)
    ·
      refine ⟨66872468365502578337785873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89163291154003437783714497 66872468365502578337785873)
      ·
        refine ⟨50154351274126933753339405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66872468365502578337785873 50154351274126933753339405)
        ·
          refine ⟨18807881727797600157502277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50154351274126933753339405 18807881727797600157502277)
          ·
            refine ⟨3526477823962050029531677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18807881727797600157502277 3526477823962050029531677)
            ·
              refine ⟨1322429183985768761074379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526477823962050029531677 1322429183985768761074379)
              ·
                refine ⟨1983643775978653141611569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322429183985768761074379 1983643775978653141611569)
                ·
                  refine ⟨1487732831983989856208677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1983643775978653141611569 1487732831983989856208677)
                  ·
                    refine ⟨278949905996998098039127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487732831983989856208677 278949905996998098039127)
                    ·
                      rfl

theorem cell23_1629759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 4].length) (baseStart_1629759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629759 prefixEnd_1629759 := by exact prefixLift 1629759
  have htrace : WordTrace (prefixWord ++ tailWord_1629759) baseStart_1629759 baseEnd_1629759 := by
    simpa [prefixWord, tailWord_1629759, baseEnd_1629759] using wordTrace_append hprefix tailTrace_1629759
  have hstable : (prefixWord ++ tailWord_1629759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629759).length < 2 ^ (prefixWord ++ tailWord_1629759).sum := by decide
  have hdescent : baseEnd_1629759 < baseStart_1629759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629772 : List Nat := [2, 2, 1, 3, 1, 5, 2, 7]
def baseStart_1629772 : Nat := 118140960795 + 1629772 * 2 ^ 59
def prefixEnd_1629772 : Nat := 4983230072969 + 3 ^ 40 * 1629772 * 2
def baseEnd_1629772 : Nat := 30994681231092694194623

theorem tailTrace_1629772 : CollatzResearch.WordTrace tailWord_1629772 prefixEnd_1629772 30994681231092694194623 := by
  unfold tailWord_1629772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721334125810930871349785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39628445501081241161799713 29721334125810930871349785)
  ·
    refine ⟨22291000594358198153512339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29721334125810930871349785 22291000594358198153512339)
    ·
      refine ⟨33436500891537297230268509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22291000594358198153512339 33436500891537297230268509)
      ·
        refine ⟨12538687834326486461350691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33436500891537297230268509 12538687834326486461350691)
        ·
          refine ⟨18808031751489729692026037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12538687834326486461350691 18808031751489729692026037)
          ·
            refine ⟨1763252976702162158627441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18808031751489729692026037 1763252976702162158627441)
            ·
              refine ⟨1322439732526621618970581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763252976702162158627441 1322439732526621618970581)
              ·
                refine ⟨30994681231092694194623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1322439732526621618970581 30994681231092694194623)
                ·
                  rfl

theorem cell23_1629772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 7].length) (baseStart_1629772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629772 prefixEnd_1629772 := by exact prefixLift 1629772
  have htrace : WordTrace (prefixWord ++ tailWord_1629772) baseStart_1629772 baseEnd_1629772 := by
    simpa [prefixWord, tailWord_1629772, baseEnd_1629772] using wordTrace_append hprefix tailTrace_1629772
  have hstable : (prefixWord ++ tailWord_1629772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629772).length < 2 ^ (prefixWord ++ tailWord_1629772).sum := by decide
  have hdescent : baseEnd_1629772 < baseStart_1629772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629783 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 1, 2, 2]
def baseStart_1629783 : Nat := 118140960795 + 1629783 * 2 ^ 59
def prefixEnd_1629783 : Nat := 4983230072969 + 3 ^ 40 * 1629783 * 2
def baseEnd_1629783 : Nat := 836862041526702200217271

theorem tailTrace_1629783 : CollatzResearch.WordTrace tailWord_1629783 prefixEnd_1629783 836862041526702200217271 := by
  unfold tailWord_1629783
  simp only [CollatzResearch.WordTrace]
  refine ⟨59443069454582010621350003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39628712969721340414233335 59443069454582010621350003)
  ·
    refine ⟨89164604181873015932025005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59443069454582010621350003 89164604181873015932025005)
    ·
      refine ⟨33436726568202380974509377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89164604181873015932025005 33436726568202380974509377)
      ·
        refine ⟨25077544926151785730882033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33436726568202380974509377 25077544926151785730882033)
        ·
          refine ⟨18808158694613839298161525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25077544926151785730882033 18808158694613839298161525)
          ·
            refine ⟨1763264877620047434202643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18808158694613839298161525 1763264877620047434202643)
            ·
              refine ⟨2644897316430071151303965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763264877620047434202643 2644897316430071151303965)
              ·
                refine ⟨991836493661276681738987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2644897316430071151303965 991836493661276681738987)
                ·
                  refine ⟨1487754740491915022608481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991836493661276681738987 1487754740491915022608481)
                  ·
                    refine ⟨1115816055368936266956361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487754740491915022608481 1115816055368936266956361)
                    ·
                      refine ⟨836862041526702200217271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115816055368936266956361 836862041526702200217271)
                      ·
                        rfl

theorem cell23_1629783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_1629783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629783 prefixEnd_1629783 := by exact prefixLift 1629783
  have htrace : WordTrace (prefixWord ++ tailWord_1629783) baseStart_1629783 baseEnd_1629783 := by
    simpa [prefixWord, tailWord_1629783, baseEnd_1629783] using wordTrace_append hprefix tailTrace_1629783
  have hstable : (prefixWord ++ tailWord_1629783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629783).length < 2 ^ (prefixWord ++ tailWord_1629783).sum := by decide
  have hdescent : baseEnd_1629783 < baseStart_1629783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629789 : List Nat := [1, 4, 4, 2, 1, 2, 9]
def baseStart_1629789 : Nat := 118140960795 + 1629789 * 2 ^ 59
def prefixEnd_1629789 : Nat := 4983230072969 + 3 ^ 40 * 1629789 * 2
def baseEnd_1629789 : Nat := 10331668177909002182003

theorem tailTrace_1629789 : CollatzResearch.WordTrace tailWord_1629789 prefixEnd_1629789 10331668177909002182003 := by
  unfold tailWord_1629789
  simp only [CollatzResearch.WordTrace]
  refine ⟨59443288292560273646068421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39628858861706849097378947 59443288292560273646068421)
  ·
    refine ⟨11145616554855051308637829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59443288292560273646068421 11145616554855051308637829)
    ·
      refine ⟨2089803104035322120369593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11145616554855051308637829 2089803104035322120369593)
      ·
        refine ⟨1567352328026491590277195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2089803104035322120369593 1567352328026491590277195)
        ·
          refine ⟨2351028492039737385415793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567352328026491590277195 2351028492039737385415793)
          ·
            refine ⟨1763271369029803039061845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2351028492039737385415793 1763271369029803039061845)
            ·
              refine ⟨10331668177909002182003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1763271369029803039061845 10331668177909002182003)
              ·
                rfl

theorem cell23_1629789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 9].length) (baseStart_1629789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629789 prefixEnd_1629789 := by exact prefixLift 1629789
  have htrace : WordTrace (prefixWord ++ tailWord_1629789) baseStart_1629789 baseEnd_1629789 := by
    simpa [prefixWord, tailWord_1629789, baseEnd_1629789] using wordTrace_append hprefix tailTrace_1629789
  have hstable : (prefixWord ++ tailWord_1629789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629789).length < 2 ^ (prefixWord ++ tailWord_1629789).sum := by decide
  have hdescent : baseEnd_1629789 < baseStart_1629789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629792 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 5, 3, 2]
def baseStart_1629792 : Nat := 118140960795 + 1629792 * 2 ^ 59
def prefixEnd_1629792 : Nat := 4983230072969 + 3 ^ 40 * 1629792 * 2
def baseEnd_1629792 : Nat := 836866662852592665004729

theorem tailTrace_1629792 : CollatzResearch.WordTrace tailWord_1629792 prefixEnd_1629792 836866662852592665004729 := by
  unfold tailWord_1629792
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721698855774702579213815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39628931807699603438951753 29721698855774702579213815)
  ·
    refine ⟨44582548283662053868820723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29721698855774702579213815 44582548283662053868820723)
    ·
      refine ⟨66873822425493080803231085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44582548283662053868820723 66873822425493080803231085)
      ·
        refine ⟨25077683409559905301211657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66873822425493080803231085 25077683409559905301211657)
        ·
          refine ⟨18808262557169928975908743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25077683409559905301211657 18808262557169928975908743)
          ·
            refine ⟨28212393835754893463863115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18808262557169928975908743 28212393835754893463863115)
            ·
              refine ⟨42318590753632340195794673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28212393835754893463863115 42318590753632340195794673)
              ·
                refine ⟨31738943065224255146846005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42318590753632340195794673 31738943065224255146846005)
                ·
                  refine ⟨2975525912364773920016813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31738943065224255146846005 2975525912364773920016813)
                  ·
                    refine ⟨1115822217136790220006305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2975525912364773920016813 1115822217136790220006305)
                    ·
                      refine ⟨836866662852592665004729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115822217136790220006305 836866662852592665004729)
                      ·
                        rfl

theorem cell23_1629792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_1629792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629792 prefixEnd_1629792 := by exact prefixLift 1629792
  have htrace : WordTrace (prefixWord ++ tailWord_1629792) baseStart_1629792 baseEnd_1629792 := by
    simpa [prefixWord, tailWord_1629792, baseEnd_1629792] using wordTrace_append hprefix tailTrace_1629792
  have hstable : (prefixWord ++ tailWord_1629792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629792).length < 2 ^ (prefixWord ++ tailWord_1629792).sum := by decide
  have hdescent : baseEnd_1629792 < baseStart_1629792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629800 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1629800 : Nat := 118140960795 + 1629800 * 2 ^ 59
def prefixEnd_1629800 : Nat := 4983230072969 + 3 ^ 40 * 1629800 * 2
def baseEnd_1629800 : Nat := 836870770697828633704693

theorem tailTrace_1629800 : CollatzResearch.WordTrace tailWord_1629800 prefixEnd_1629800 836870770697828633704693 := by
  unfold tailWord_1629800
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721844747760211262359427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39629126330346948349812569 29721844747760211262359427)
  ·
    refine ⟨44582767121640316893539141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29721844747760211262359427 44582767121640316893539141)
    ·
      refine ⟨8359268835307559417538589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44582767121640316893539141 8359268835307559417538589)
      ·
        refine ⟨3134725813240334781576971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8359268835307559417538589 3134725813240334781576971)
        ·
          refine ⟨4702088719860502172365457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134725813240334781576971 4702088719860502172365457)
          ·
            refine ⟨3526566539895376629274093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4702088719860502172365457 3526566539895376629274093)
            ·
              refine ⟨1322462452460766235977785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526566539895376629274093 1322462452460766235977785)
              ·
                refine ⟨991846839345574676983339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322462452460766235977785 991846839345574676983339)
                ·
                  refine ⟨1487770259018362015475009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991846839345574676983339 1487770259018362015475009)
                  ·
                    refine ⟨1115827694263771511606257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487770259018362015475009 1115827694263771511606257)
                    ·
                      refine ⟨836870770697828633704693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115827694263771511606257 836870770697828633704693)
                      ·
                        rfl

theorem cell23_1629800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1629800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629800 prefixEnd_1629800 := by exact prefixLift 1629800
  have htrace : WordTrace (prefixWord ++ tailWord_1629800) baseStart_1629800 baseEnd_1629800 := by
    simpa [prefixWord, tailWord_1629800, baseEnd_1629800] using wordTrace_append hprefix tailTrace_1629800
  have hstable : (prefixWord ++ tailWord_1629800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629800).length < 2 ^ (prefixWord ++ tailWord_1629800).sum := by decide
  have hdescent : baseEnd_1629800 < baseStart_1629800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629856 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 2, 2, 2]
def baseStart_1629856 : Nat := 118140960795 + 1629856 * 2 ^ 59
def prefixEnd_1629856 : Nat := 4983230072969 + 3 ^ 40 * 1629856 * 2
def baseEnd_1629856 : Nat := 836899525614480414604435

theorem tailTrace_1629856 : CollatzResearch.WordTrace tailWord_1629856 prefixEnd_1629856 836899525614480414604435 := by
  unfold tailWord_1629856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29722865991658772044378711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39630487988878362725838281 29722865991658772044378711)
  ·
    refine ⟨44584298987488158066568067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29722865991658772044378711 44584298987488158066568067)
    ·
      refine ⟨66876448481232237099852101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44584298987488158066568067 66876448481232237099852101)
      ·
        refine ⟨12539334090231044456222269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66876448481232237099852101 12539334090231044456222269)
        ·
          refine ⟨4702250283836641671083351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12539334090231044456222269 4702250283836641671083351)
          ·
            refine ⟨7053375425754962506625027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4702250283836641671083351 7053375425754962506625027)
            ·
              refine ⟨10580063138632443759937541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053375425754962506625027 10580063138632443759937541)
              ·
                refine ⟨1983761838493583204988289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10580063138632443759937541 1983761838493583204988289)
                ·
                  refine ⟨1487821378870187403741217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1983761838493583204988289 1487821378870187403741217)
                  ·
                    refine ⟨1115866034152640552805913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487821378870187403741217 1115866034152640552805913)
                    ·
                      refine ⟨836899525614480414604435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1115866034152640552805913 836899525614480414604435)
                      ·
                        rfl

theorem cell23_1629856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_1629856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629856 prefixEnd_1629856 := by exact prefixLift 1629856
  have htrace : WordTrace (prefixWord ++ tailWord_1629856) baseStart_1629856 baseEnd_1629856 := by
    simpa [prefixWord, tailWord_1629856, baseEnd_1629856] using wordTrace_append hprefix tailTrace_1629856
  have hstable : (prefixWord ++ tailWord_1629856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629856).length < 2 ^ (prefixWord ++ tailWord_1629856).sum := by decide
  have hdescent : baseEnd_1629856 < baseStart_1629856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629875 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 1, 7]
def baseStart_1629875 : Nat := 118140960795 + 1629875 * 2 ^ 59
def prefixEnd_1629875 : Nat := 4983230072969 + 3 ^ 40 * 1629875 * 2
def baseEnd_1629875 : Nat := 278969760582305280088949

theorem tailTrace_1629875 : CollatzResearch.WordTrace tailWord_1629875 prefixEnd_1629875 278969760582305280088949 := by
  unfold tailWord_1629875
  simp only [CollatzResearch.WordTrace]
  refine ⟨59446424970248710333699079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39630949980165806889132719 59446424970248710333699079)
  ·
    refine ⟨89169637455373065500548619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59446424970248710333699079 89169637455373065500548619)
    ·
      refine ⟨133754456183059598250822929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89169637455373065500548619 133754456183059598250822929)
      ·
        refine ⟨100315842137294698688117197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133754456183059598250822929 100315842137294698688117197)
        ·
          refine ⟨37618440801485512008043949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100315842137294698688117197 37618440801485512008043949)
          ·
            refine ⟨14106915300557067003016481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37618440801485512008043949 14106915300557067003016481)
            ·
              refine ⟨10580186475417800252262361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14106915300557067003016481 10580186475417800252262361)
              ·
                refine ⟨7935139856563350189196771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580186475417800252262361 7935139856563350189196771)
                ·
                  refine ⟨11902709784845025283795157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935139856563350189196771 11902709784845025283795157)
                  ·
                    refine ⟨278969760582305280088949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11902709784845025283795157 278969760582305280088949)
                    ·
                      rfl

theorem cell23_1629875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 7].length) (baseStart_1629875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629875 prefixEnd_1629875 := by exact prefixLift 1629875
  have htrace : WordTrace (prefixWord ++ tailWord_1629875) baseStart_1629875 baseEnd_1629875 := by
    simpa [prefixWord, tailWord_1629875, baseEnd_1629875] using wordTrace_append hprefix tailTrace_1629875
  have hstable : (prefixWord ++ tailWord_1629875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629875).length < 2 ^ (prefixWord ++ tailWord_1629875).sum := by decide
  have hdescent : baseEnd_1629875 < baseStart_1629875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629892 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1629892 : Nat := 118140960795 + 1629892 * 2 ^ 59
def prefixEnd_1629892 : Nat := 4983230072969 + 3 ^ 40 * 1629892 * 2
def baseEnd_1629892 : Nat := 278972670306014091251423

theorem tailTrace_1629892 : CollatzResearch.WordTrace tailWord_1629892 prefixEnd_1629892 278972670306014091251423 := by
  unfold tailWord_1629892
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723522505593561118533965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39631363340791414824711953 29723522505593561118533965)
  ·
    refine ⟨11146320939597585419450237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29723522505593561118533965 11146320939597585419450237)
    ·
      refine ⟨4179870352349094532293839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11146320939597585419450237 4179870352349094532293839)
      ·
        refine ⟨6269805528523641798440759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179870352349094532293839 6269805528523641798440759)
        ·
          refine ⟨9404708292785462697661139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269805528523641798440759 9404708292785462697661139)
          ·
            refine ⟨14107062439178194046491709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404708292785462697661139 14107062439178194046491709)
            ·
              refine ⟨5290148414691822767434391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14107062439178194046491709 5290148414691822767434391)
              ·
                refine ⟨7935222622037734151151587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290148414691822767434391 7935222622037734151151587)
                ·
                  refine ⟨11902833933056601226727381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935222622037734151151587 11902833933056601226727381)
                  ·
                    refine ⟨278972670306014091251423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11902833933056601226727381 278972670306014091251423)
                    ·
                      rfl

theorem cell23_1629892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1629892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629892 prefixEnd_1629892 := by exact prefixLift 1629892
  have htrace : WordTrace (prefixWord ++ tailWord_1629892) baseStart_1629892 baseEnd_1629892 := by
    simpa [prefixWord, tailWord_1629892, baseEnd_1629892] using wordTrace_append hprefix tailTrace_1629892
  have hstable : (prefixWord ++ tailWord_1629892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629892).length < 2 ^ (prefixWord ++ tailWord_1629892).sum := by decide
  have hdescent : baseEnd_1629892 < baseStart_1629892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629912 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1629912 : Nat := 118140960795 + 1629912 * 2 ^ 59
def prefixEnd_1629912 : Nat := 4983230072969 + 3 ^ 40 * 1629912 * 2
def baseEnd_1629912 : Nat := 836928280531132195504177

theorem tailTrace_1629912 : CollatzResearch.WordTrace tailWord_1629912 prefixEnd_1629912 836928280531132195504177 := by
  unfold tailWord_1629912
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723887235557332826397995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39631849647409777101863993 29723887235557332826397995)
  ·
    refine ⟨44585830853335999239596993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29723887235557332826397995 44585830853335999239596993)
    ·
      refine ⟨33439373140001999429697745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44585830853335999239596993 33439373140001999429697745)
      ·
        refine ⟨25079529855001499572273309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33439373140001999429697745 25079529855001499572273309)
        ·
          refine ⟨9404823695625562339602491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25079529855001499572273309 9404823695625562339602491)
          ·
            refine ⟨14107235543438343509403737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404823695625562339602491 14107235543438343509403737)
            ·
              refine ⟨10580426657578757632052803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14107235543438343509403737 10580426657578757632052803)
              ·
                refine ⟨15870639986368136448079205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10580426657578757632052803 15870639986368136448079205)
                ·
                  refine ⟨2975744997444025584014851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15870639986368136448079205 2975744997444025584014851)
                  ·
                    refine ⟨4463617496166038376022277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2975744997444025584014851 4463617496166038376022277)
                    ·
                      refine ⟨836928280531132195504177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4463617496166038376022277 836928280531132195504177)
                      ·
                        rfl

theorem cell23_1629912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1629912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629912 prefixEnd_1629912 := by exact prefixLift 1629912
  have htrace : WordTrace (prefixWord ++ tailWord_1629912) baseStart_1629912 baseEnd_1629912 := by
    simpa [prefixWord, tailWord_1629912, baseEnd_1629912] using wordTrace_append hprefix tailTrace_1629912
  have hstable : (prefixWord ++ tailWord_1629912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629912).length < 2 ^ (prefixWord ++ tailWord_1629912).sum := by decide
  have hdescent : baseEnd_1629912 < baseStart_1629912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629932 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_1629932 : Nat := 118140960795 + 1629932 * 2 ^ 59
def prefixEnd_1629932 : Nat := 4983230072969 + 3 ^ 40 * 1629932 * 2
def baseEnd_1629932 : Nat := 836938550144222117254085

theorem tailTrace_1629932 : CollatzResearch.WordTrace tailWord_1629932 prefixEnd_1629932 836938550144222117254085 := by
  unfold tailWord_1629932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29724251965521104534262025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39632335954028139379016033 29724251965521104534262025)
  ·
    refine ⟨22293188974140828400696519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29724251965521104534262025 22293188974140828400696519)
    ·
      refine ⟨33439783461211242601044779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22293188974140828400696519 33439783461211242601044779)
      ·
        refine ⟨50159675191816863901567169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33439783461211242601044779 50159675191816863901567169)
        ·
          refine ⟨37619756393862647926175377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50159675191816863901567169 37619756393862647926175377)
          ·
            refine ⟨28214817295396985944631533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37619756393862647926175377 28214817295396985944631533)
            ·
              refine ⟨10580556485773869729236825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28214817295396985944631533 10580556485773869729236825)
              ·
                refine ⟨7935417364330402296927619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580556485773869729236825 7935417364330402296927619)
                ·
                  refine ⟨11903126046495603445391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935417364330402296927619 11903126046495603445391429)
                  ·
                    refine ⟨2231836133717925646010893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11903126046495603445391429 2231836133717925646010893)
                    ·
                      refine ⟨836938550144222117254085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2231836133717925646010893 836938550144222117254085)
                      ·
                        rfl

theorem cell23_1629932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_1629932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629932 prefixEnd_1629932 := by exact prefixLift 1629932
  have htrace : WordTrace (prefixWord ++ tailWord_1629932) baseStart_1629932 baseEnd_1629932 := by
    simpa [prefixWord, tailWord_1629932, baseEnd_1629932] using wordTrace_append hprefix tailTrace_1629932
  have hstable : (prefixWord ++ tailWord_1629932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629932).length < 2 ^ (prefixWord ++ tailWord_1629932).sum := by decide
  have hdescent : baseEnd_1629932 < baseStart_1629932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629945 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1629945 : Nat := 118140960795 + 1629945 * 2 ^ 59
def prefixEnd_1629945 : Nat := 4983230072969 + 3 ^ 40 * 1629945 * 2
def baseEnd_1629945 : Nat := 836945225392730566391525

theorem tailTrace_1629945 : CollatzResearch.WordTrace tailWord_1629945 prefixEnd_1629945 836945225392730566391525 := by
  unfold tailWord_1629945
  simp only [CollatzResearch.WordTrace]
  refine ⟨59448978079995112288747289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39632652053330074859164859 59448978079995112288747289)
  ·
    refine ⟨44586733559996334216560467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59448978079995112288747289 44586733559996334216560467)
    ·
      refine ⟨66880100339994501324840701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44586733559996334216560467 66880100339994501324840701)
      ·
        refine ⟨25080037627497937996815263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66880100339994501324840701 25080037627497937996815263)
        ·
          refine ⟨37620056441246906995222895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25080037627497937996815263 37620056441246906995222895)
          ·
            refine ⟨56430084661870360492834343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37620056441246906995222895 56430084661870360492834343)
            ·
              refine ⟨84645126992805540739251515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56430084661870360492834343 84645126992805540739251515)
              ·
                refine ⟨126967690489208311108877273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84645126992805540739251515 126967690489208311108877273)
                ·
                  refine ⟨95225767866906233331657955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126967690489208311108877273 95225767866906233331657955)
                  ·
                    refine ⟨142838651800359349997486933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95225767866906233331657955 142838651800359349997486933)
                    ·
                      refine ⟨836945225392730566391525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 142838651800359349997486933 836945225392730566391525)
                      ·
                        rfl

theorem cell23_1629945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1629945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629945 prefixEnd_1629945 := by exact prefixLift 1629945
  have htrace : WordTrace (prefixWord ++ tailWord_1629945) baseStart_1629945 baseEnd_1629945 := by
    simpa [prefixWord, tailWord_1629945, baseEnd_1629945] using wordTrace_append hprefix tailTrace_1629945
  have hstable : (prefixWord ++ tailWord_1629945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629945).length < 2 ^ (prefixWord ++ tailWord_1629945).sum := by decide
  have hdescent : baseEnd_1629945 < baseStart_1629945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629973 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1629973 : Nat := 118140960795 + 1629973 * 2 ^ 59
def prefixEnd_1629973 : Nat := 4983230072969 + 3 ^ 40 * 1629973 * 2
def baseEnd_1629973 : Nat := 278986534283685485613799

theorem tailTrace_1629973 : CollatzResearch.WordTrace tailWord_1629973 prefixEnd_1629973 278986534283685485613799 := by
  unfold tailWord_1629973
  simp only [CollatzResearch.WordTrace]
  refine ⟨59449999323893673070766573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39633332882595782047177715 59449999323893673070766573)
  ·
    refine ⟨22293749746460127401537465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59449999323893673070766573 22293749746460127401537465)
    ·
      refine ⟨16720312309845095551153099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22293749746460127401537465 16720312309845095551153099)
      ·
        refine ⟨25080468464767643326729649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16720312309845095551153099 25080468464767643326729649)
        ·
          refine ⟨18810351348575732495047237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25080468464767643326729649 18810351348575732495047237)
          ·
            refine ⟨3526940877857949842821357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18810351348575732495047237 3526940877857949842821357)
            ·
              refine ⟨1322602829196731191058009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526940877857949842821357 1322602829196731191058009)
              ·
                refine ⟨991952121897548393293507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322602829196731191058009 991952121897548393293507)
                ·
                  refine ⟨1487928182846322589940261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991952121897548393293507 1487928182846322589940261)
                  ·
                    refine ⟨278986534283685485613799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487928182846322589940261 278986534283685485613799)
                    ·
                      rfl

theorem cell23_1629973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1629973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1629973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1629973 prefixEnd_1629973 := by exact prefixLift 1629973
  have htrace : WordTrace (prefixWord ++ tailWord_1629973) baseStart_1629973 baseEnd_1629973 := by
    simpa [prefixWord, tailWord_1629973, baseEnd_1629973] using wordTrace_append hprefix tailTrace_1629973
  have hstable : (prefixWord ++ tailWord_1629973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629973).length < 2 ^ (prefixWord ++ tailWord_1629973).sum := by decide
  have hdescent : baseEnd_1629973 < baseStart_1629973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630012 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_1630012 : Nat := 118140960795 + 1630012 * 2 ^ 59
def prefixEnd_1630012 : Nat := 4983230072969 + 3 ^ 40 * 1630012 * 2
def baseEnd_1630012 : Nat := 278993209532193934751239

theorem tailTrace_1630012 : CollatzResearch.WordTrace tailWord_1630012 prefixEnd_1630012 278993209532193934751239 := by
  unfold tailWord_1630012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725710885376191365718145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39634281180501588487624193 29725710885376191365718145)
  ·
    refine ⟨22294283164032143524288609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29725710885376191365718145 22294283164032143524288609)
    ·
      refine ⟨16720712373024107643216457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22294283164032143524288609 16720712373024107643216457)
      ·
        refine ⟨12540534279768080732412343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16720712373024107643216457 12540534279768080732412343)
        ·
          refine ⟨18810801419652121098618515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540534279768080732412343 18810801419652121098618515)
          ·
            refine ⟨28216202129478181647927773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18810801419652121098618515 28216202129478181647927773)
            ·
              refine ⟨10581075798554318117972915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28216202129478181647927773 10581075798554318117972915)
              ·
                refine ⟨15871613697831477176959373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581075798554318117972915 15871613697831477176959373)
                ·
                  refine ⟨5951855136686803941359765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15871613697831477176959373 5951855136686803941359765)
                  ·
                    refine ⟨278993209532193934751239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5951855136686803941359765 278993209532193934751239)
                    ·
                      rfl

theorem cell23_1630012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_1630012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630012 prefixEnd_1630012 := by exact prefixLift 1630012
  have htrace : WordTrace (prefixWord ++ tailWord_1630012) baseStart_1630012 baseEnd_1630012 := by
    simpa [prefixWord, tailWord_1630012, baseEnd_1630012] using wordTrace_append hprefix tailTrace_1630012
  have hstable : (prefixWord ++ tailWord_1630012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630012).length < 2 ^ (prefixWord ++ tailWord_1630012).sum := by decide
  have hdescent : baseEnd_1630012 < baseStart_1630012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630032 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_1630032 : Nat := 118140960795 + 1630032 * 2 ^ 59
def prefixEnd_1630032 : Nat := 4983230072969 + 3 ^ 40 * 1630032 * 2
def baseEnd_1630032 : Nat := 836989898209671726003625

theorem tailTrace_1630032 : CollatzResearch.WordTrace tailWord_1630032 prefixEnd_1630032 836989898209671726003625 := by
  unfold tailWord_1630032
  simp only [CollatzResearch.WordTrace]
  refine ⟨29726075615339963073582175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39634767487119950764776233 29726075615339963073582175)
  ·
    refine ⟨44589113423009944610373263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29726075615339963073582175 44589113423009944610373263)
    ·
      refine ⟨66883670134514916915559895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44589113423009944610373263 66883670134514916915559895)
      ·
        refine ⟨100325505201772375373339843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66883670134514916915559895 100325505201772375373339843)
        ·
          refine ⟨150488257802658563060009765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100325505201772375373339843 150488257802658563060009765)
          ·
            refine ⟨28216548337998480573751831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150488257802658563060009765 28216548337998480573751831)
            ·
              refine ⟨42324822506997720860627747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28216548337998480573751831 42324822506997720860627747)
              ·
                refine ⟨63487233760496581290941621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42324822506997720860627747 63487233760496581290941621)
                ·
                  refine ⟨5951928165046554496025777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63487233760496581290941621 5951928165046554496025777)
                  ·
                    refine ⟨4463946123784915872019333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951928165046554496025777 4463946123784915872019333)
                    ·
                      refine ⟨836989898209671726003625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4463946123784915872019333 836989898209671726003625)
                      ·
                        rfl

theorem cell23_1630032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_1630032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630032 prefixEnd_1630032 := by exact prefixLift 1630032
  have htrace : WordTrace (prefixWord ++ tailWord_1630032) baseStart_1630032 baseEnd_1630032 := by
    simpa [prefixWord, tailWord_1630032, baseEnd_1630032] using wordTrace_append hprefix tailTrace_1630032
  have hstable : (prefixWord ++ tailWord_1630032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630032).length < 2 ^ (prefixWord ++ tailWord_1630032).sum := by decide
  have hdescent : baseEnd_1630032 < baseStart_1630032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630049 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_1630049 : Nat := 118140960795 + 1630049 * 2 ^ 59
def prefixEnd_1630049 : Nat := 4983230072969 + 3 ^ 40 * 1630049 * 2
def baseEnd_1630049 : Nat := 836998627380798159491047

theorem tailTrace_1630049 : CollatzResearch.WordTrace tailWord_1630049 prefixEnd_1630049 836998627380798159491047 := by
  unfold tailWord_1630049
  simp only [CollatzResearch.WordTrace]
  refine ⟨59452771271618338050533201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39635180847745558700355467 59452771271618338050533201)
  ·
    refine ⟨44589578453713753537899901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59452771271618338050533201 44589578453713753537899901)
    ·
      refine ⟨16721091920142657576712463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44589578453713753537899901 16721091920142657576712463)
      ·
        refine ⟨25081637880213986365068695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16721091920142657576712463 25081637880213986365068695)
        ·
          refine ⟨37622456820320979547603043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25081637880213986365068695 37622456820320979547603043)
          ·
            refine ⟨56433685230481469321404565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37622456820320979547603043 56433685230481469321404565)
            ·
              refine ⟨2645328995178818874440839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56433685230481469321404565 2645328995178818874440839)
              ·
                refine ⟨3967993492768228311661259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645328995178818874440839 3967993492768228311661259)
                ·
                  refine ⟨5951990239152342467491889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967993492768228311661259 5951990239152342467491889)
                  ·
                    refine ⟨4463992679364256850618917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951990239152342467491889 4463992679364256850618917)
                    ·
                      refine ⟨836998627380798159491047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4463992679364256850618917 836998627380798159491047)
                      ·
                        rfl

theorem cell23_1630049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_1630049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630049 prefixEnd_1630049 := by exact prefixLift 1630049
  have htrace : WordTrace (prefixWord ++ tailWord_1630049) baseStart_1630049 baseEnd_1630049 := by
    simpa [prefixWord, tailWord_1630049, baseEnd_1630049] using wordTrace_append hprefix tailTrace_1630049
  have hstable : (prefixWord ++ tailWord_1630049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630049).length < 2 ^ (prefixWord ++ tailWord_1630049).sum := by decide
  have hdescent : baseEnd_1630049 < baseStart_1630049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630056 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1630056 : Nat := 118140960795 + 1630056 * 2 ^ 59
def prefixEnd_1630056 : Nat := 4983230072969 + 3 ^ 40 * 1630056 * 2
def baseEnd_1630056 : Nat := 837002221745379632103515

theorem tailTrace_1630056 : CollatzResearch.WordTrace tailWord_1630056 prefixEnd_1630056 837002221745379632103515 := by
  unfold tailWord_1630056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29726513291296489123019011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39635351055061985497358681 29726513291296489123019011)
  ·
    refine ⟨44589769936944733684528517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29726513291296489123019011 44589769936944733684528517)
    ·
      refine ⟨8360581863177137565849097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44589769936944733684528517 8360581863177137565849097)
      ·
        refine ⟨6270436397382853174386823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8360581863177137565849097 6270436397382853174386823)
        ·
          refine ⟨9405654596074279761580235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270436397382853174386823 9405654596074279761580235)
          ·
            refine ⟨14108481894111419642370353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405654596074279761580235 14108481894111419642370353)
            ·
              refine ⟨10581361420583564731777765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14108481894111419642370353 10581361420583564731777765)
              ·
                refine ⟨1984005266359418387208331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10581361420583564731777765 1984005266359418387208331)
                ·
                  refine ⟨2976007899539127580812497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984005266359418387208331 2976007899539127580812497)
                  ·
                    refine ⟨2232005924654345685609373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2976007899539127580812497 2232005924654345685609373)
                    ·
                      refine ⟨837002221745379632103515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2232005924654345685609373 837002221745379632103515)
                      ·
                        rfl

theorem cell23_1630056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1630056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630056 prefixEnd_1630056 := by exact prefixLift 1630056
  have htrace : WordTrace (prefixWord ++ tailWord_1630056) baseStart_1630056 baseEnd_1630056 := by
    simpa [prefixWord, tailWord_1630056, baseEnd_1630056] using wordTrace_append hprefix tailTrace_1630056
  have hstable : (prefixWord ++ tailWord_1630056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630056).length < 2 ^ (prefixWord ++ tailWord_1630056).sum := by decide
  have hdescent : baseEnd_1630056 < baseStart_1630056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630110 : List Nat := [4, 3, 1, 3, 1, 2, 2, 7]
def baseStart_1630110 : Nat := 118140960795 + 1630110 * 2 ^ 59
def prefixEnd_1630110 : Nat := 4983230072969 + 3 ^ 40 * 1630110 * 2
def baseEnd_1630110 : Nat := 31001109248174904475121

theorem tailTrace_1630110 : CollatzResearch.WordTrace tailWord_1630110 prefixEnd_1630110 31001109248174904475121 := by
  unfold tailWord_1630110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431874515549668183562973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39636664082931563645669189 7431874515549668183562973)
  ·
    refine ⟨2786952943331125568836115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7431874515549668183562973 2786952943331125568836115)
    ·
      refine ⟨4180429414996688353254173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2786952943331125568836115 4180429414996688353254173)
      ·
        refine ⟨1567661030623758132470315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4180429414996688353254173 1567661030623758132470315)
        ·
          refine ⟨2351491545935637198705473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567661030623758132470315 2351491545935637198705473)
          ·
            refine ⟨1763618659451727899029105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2351491545935637198705473 1763618659451727899029105)
            ·
              refine ⟨1322713994588795924271829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763618659451727899029105 1322713994588795924271829)
              ·
                refine ⟨31001109248174904475121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1322713994588795924271829 31001109248174904475121)
                ·
                  rfl

theorem cell23_1630110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_1630110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630110 prefixEnd_1630110 := by exact prefixLift 1630110
  have htrace : WordTrace (prefixWord ++ tailWord_1630110) baseStart_1630110 baseEnd_1630110 := by
    simpa [prefixWord, tailWord_1630110, baseEnd_1630110] using wordTrace_append hprefix tailTrace_1630110
  have hstable : (prefixWord ++ tailWord_1630110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630110).length < 2 ^ (prefixWord ++ tailWord_1630110).sum := by decide
  have hdescent : baseEnd_1630110 < baseStart_1630110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630129 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1630129 : Nat := 118140960795 + 1630129 * 2 ^ 59
def prefixEnd_1630129 : Nat := 4983230072969 + 3 ^ 40 * 1630129 * 2
def baseEnd_1630129 : Nat := 837039705833157846490679

theorem tailTrace_1630129 : CollatzResearch.WordTrace tailWord_1630129 prefixEnd_1630129 837039705833157846490679 := by
  unfold tailWord_1630129
  simp only [CollatzResearch.WordTrace]
  refine ⟨59455689111328511713445441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39637126074219007808963627 59455689111328511713445441)
  ·
    refine ⟨44591766833496383785084081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59455689111328511713445441 44591766833496383785084081)
    ·
      refine ⟨33443825125122287838813061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44591766833496383785084081 33443825125122287838813061)
      ·
        refine ⟨6270717210960428969777449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33443825125122287838813061 6270717210960428969777449)
        ·
          refine ⟨4703037908220321727333087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6270717210960428969777449 4703037908220321727333087)
          ·
            refine ⟨7054556862330482590999631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703037908220321727333087 7054556862330482590999631)
            ·
              refine ⟨10581835293495723886499447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7054556862330482590999631 10581835293495723886499447)
              ·
                refine ⟨15872752940243585829749171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581835293495723886499447 15872752940243585829749171)
                ·
                  refine ⟨23809129410365378744623757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15872752940243585829749171 23809129410365378744623757)
                  ·
                    refine ⟨8928423528887017029233909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23809129410365378744623757 8928423528887017029233909)
                    ·
                      refine ⟨837039705833157846490679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8928423528887017029233909 837039705833157846490679)
                      ·
                        rfl

theorem cell23_1630129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1630129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630129 prefixEnd_1630129 := by exact prefixLift 1630129
  have htrace : WordTrace (prefixWord ++ tailWord_1630129) baseStart_1630129 baseEnd_1630129 := by
    simpa [prefixWord, tailWord_1630129, baseEnd_1630129] using wordTrace_append hprefix tailTrace_1630129
  have hstable : (prefixWord ++ tailWord_1630129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630129).length < 2 ^ (prefixWord ++ tailWord_1630129).sum := by decide
  have hdescent : baseEnd_1630129 < baseStart_1630129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630143 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 2, 2, 2]
def baseStart_1630143 : Nat := 118140960795 + 1630143 * 2 ^ 59
def prefixEnd_1630143 : Nat := 4983230072969 + 3 ^ 40 * 1630143 * 2
def baseEnd_1630143 : Nat := 837046894562320791715615

theorem tailTrace_1630143 : CollatzResearch.WordTrace tailWord_1630143 prefixEnd_1630143 837046894562320791715615 := by
  unfold tailWord_1630143
  simp only [CollatzResearch.WordTrace]
  refine ⟨59456199733277792104455083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39637466488851861402970055 59456199733277792104455083)
  ·
    refine ⟨89184299599916688156682625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59456199733277792104455083 89184299599916688156682625)
    ·
      refine ⟨66888224699937516117511969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89184299599916688156682625 66888224699937516117511969)
      ·
        refine ⟨50166168524953137088133977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66888224699937516117511969 50166168524953137088133977)
        ·
          refine ⟨37624626393714852816100483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50166168524953137088133977 37624626393714852816100483)
          ·
            refine ⟨56436939590572279224150725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37624626393714852816100483 56436939590572279224150725)
            ·
              refine ⟨10581926173232302354528261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56436939590572279224150725 10581926173232302354528261)
              ·
                refine ⟨1984111157481056691474049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10581926173232302354528261 1984111157481056691474049)
                ·
                  refine ⟨1488083368110792518605537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1984111157481056691474049 1488083368110792518605537)
                  ·
                    refine ⟨1116062526083094388954153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488083368110792518605537 1116062526083094388954153)
                    ·
                      refine ⟨837046894562320791715615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116062526083094388954153 837046894562320791715615)
                      ·
                        rfl

theorem cell23_1630143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_1630143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630143 prefixEnd_1630143 := by exact prefixLift 1630143
  have htrace : WordTrace (prefixWord ++ tailWord_1630143) baseStart_1630143 baseEnd_1630143 := by
    simpa [prefixWord, tailWord_1630143, baseEnd_1630143] using wordTrace_append hprefix tailTrace_1630143
  have hstable : (prefixWord ++ tailWord_1630143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630143).length < 2 ^ (prefixWord ++ tailWord_1630143).sum := by decide
  have hdescent : baseEnd_1630143 < baseStart_1630143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630159 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_1630159 : Nat := 118140960795 + 1630159 * 2 ^ 59
def prefixEnd_1630159 : Nat := 4983230072969 + 3 ^ 40 * 1630159 * 2
def baseEnd_1630159 : Nat := 837055110252792729115541

theorem tailTrace_1630159 : CollatzResearch.WordTrace tailWord_1630159 prefixEnd_1630159 837055110252792729115541 := by
  unfold tailWord_1630159
  simp only [CollatzResearch.WordTrace]
  refine ⟨59456783301219826837037531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39637855534146551224691687 59456783301219826837037531)
  ·
    refine ⟨89185174951829740255556297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59456783301219826837037531 89185174951829740255556297)
    ·
      refine ⟨66888881213872305191667223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89185174951829740255556297 66888881213872305191667223)
      ·
        refine ⟨100333321820808457787500835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66888881213872305191667223 100333321820808457787500835)
        ·
          refine ⟨150499982731212686681251253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100333321820808457787500835 150499982731212686681251253)
          ·
            refine ⟨14109373381051189376367305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150499982731212686681251253 14109373381051189376367305)
            ·
              refine ⟨10582030035788392032275479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14109373381051189376367305 10582030035788392032275479)
              ·
                refine ⟨15873045053682588048413219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10582030035788392032275479 15873045053682588048413219)
                ·
                  refine ⟨23809567580523882072619829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15873045053682588048413219 23809567580523882072619829)
                  ·
                    refine ⟨2232146960674113944308109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23809567580523882072619829 2232146960674113944308109)
                    ·
                      refine ⟨837055110252792729115541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2232146960674113944308109 837055110252792729115541)
                      ·
                        rfl

theorem cell23_1630159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_1630159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630159 prefixEnd_1630159 := by exact prefixLift 1630159
  have htrace : WordTrace (prefixWord ++ tailWord_1630159) baseStart_1630159 baseEnd_1630159 := by
    simpa [prefixWord, tailWord_1630159, baseEnd_1630159] using wordTrace_append hprefix tailTrace_1630159
  have hstable : (prefixWord ++ tailWord_1630159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630159).length < 2 ^ (prefixWord ++ tailWord_1630159).sum := by decide
  have hdescent : baseEnd_1630159 < baseStart_1630159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630160 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 2, 2, 2]
def baseStart_1630160 : Nat := 118140960795 + 1630160 * 2 ^ 59
def prefixEnd_1630160 : Nat := 4983230072969 + 3 ^ 40 * 1630160 * 2
def baseEnd_1630160 : Nat := 837055623733447225203037

theorem tailTrace_1630160 : CollatzResearch.WordTrace tailWord_1630160 prefixEnd_1630160 837055623733447225203037 := by
  unfold tailWord_1630160
  simp only [CollatzResearch.WordTrace]
  refine ⟨29728409887108102003911967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39637879849477469338549289 29728409887108102003911967)
  ·
    refine ⟨44592614830662153005867951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29728409887108102003911967 44592614830662153005867951)
    ·
      refine ⟨66888922245993229508801927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44592614830662153005867951 66888922245993229508801927)
      ·
        refine ⟨100333383368989844263202891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66888922245993229508801927 100333383368989844263202891)
        ·
          refine ⟨150500075053484766394804337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100333383368989844263202891 150500075053484766394804337)
          ·
            refine ⟨112875056290113574796103253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150500075053484766394804337 112875056290113574796103253)
            ·
              refine ⟨1322754565899768454641835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 112875056290113574796103253 1322754565899768454641835)
              ·
                refine ⟨1984131848849652681962753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322754565899768454641835 1984131848849652681962753)
                ·
                  refine ⟨1488098886637239511472065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1984131848849652681962753 1488098886637239511472065)
                  ·
                    refine ⟨1116074164977929633604049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488098886637239511472065 1116074164977929633604049)
                    ·
                      refine ⟨837055623733447225203037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116074164977929633604049 837055623733447225203037)
                      ·
                        rfl

theorem cell23_1630160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 2, 2].length) (baseStart_1630160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630160 prefixEnd_1630160 := by exact prefixLift 1630160
  have htrace : WordTrace (prefixWord ++ tailWord_1630160) baseStart_1630160 baseEnd_1630160 := by
    simpa [prefixWord, tailWord_1630160, baseEnd_1630160] using wordTrace_append hprefix tailTrace_1630160
  have hstable : (prefixWord ++ tailWord_1630160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630160).length < 2 ^ (prefixWord ++ tailWord_1630160).sum := by decide
  have hdescent : baseEnd_1630160 < baseStart_1630160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630239 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 8]
def baseStart_1630239 : Nat := 118140960795 + 1630239 * 2 ^ 59
def prefixEnd_1630239 : Nat := 4983230072969 + 3 ^ 40 * 1630239 * 2
def baseEnd_1630239 : Nat := 93010687633905824012797

theorem tailTrace_1630239 : CollatzResearch.WordTrace tailWord_1630239 prefixEnd_1630239 93010687633905824012797 := by
  unfold tailWord_1630239
  simp only [CollatzResearch.WordTrace]
  refine ⟨59459701140930000499949771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39639800760620000333299847 59459701140930000499949771)
  ·
    refine ⟨89189551711395000749924657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59459701140930000499949771 89189551711395000749924657)
    ·
      refine ⟨66892163783546250562443493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89189551711395000749924657 66892163783546250562443493)
      ·
        refine ⟨12542280709414921980458155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66892163783546250562443493 12542280709414921980458155)
        ·
          refine ⟨18813421064122382970687233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12542280709414921980458155 18813421064122382970687233)
          ·
            refine ⟨14110065798091787228015425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18813421064122382970687233 14110065798091787228015425)
            ·
              refine ⟨10582549348568840421011569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14110065798091787228015425 10582549348568840421011569)
              ·
                refine ⟨7936912011426630315758677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10582549348568840421011569 7936912011426630315758677)
                ·
                  refine ⟨93010687633905824012797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7936912011426630315758677 93010687633905824012797)
                  ·
                    rfl

theorem cell23_1630239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 8].length) (baseStart_1630239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630239 prefixEnd_1630239 := by exact prefixLift 1630239
  have htrace : WordTrace (prefixWord ++ tailWord_1630239) baseStart_1630239 baseEnd_1630239 := by
    simpa [prefixWord, tailWord_1630239, baseEnd_1630239] using wordTrace_append hprefix tailTrace_1630239
  have hstable : (prefixWord ++ tailWord_1630239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630239).length < 2 ^ (prefixWord ++ tailWord_1630239).sum := by decide
  have hdescent : baseEnd_1630239 < baseStart_1630239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630256 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 6]
def baseStart_1630256 : Nat := 118140960795 + 1630256 * 2 ^ 59
def prefixEnd_1630256 : Nat := 4983230072969 + 3 ^ 40 * 1630256 * 2
def baseEnd_1630256 : Nat := 93011657541808761066955

theorem tailTrace_1630256 : CollatzResearch.WordTrace tailWord_1630256 prefixEnd_1630256 93011657541808761066955 := by
  unfold tailWord_1630256
  simp only [CollatzResearch.WordTrace]
  refine ⟨29730160590934206201659311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39640214121245608268879081 29730160590934206201659311)
  ·
    refine ⟨44595240886401309302488967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29730160590934206201659311 44595240886401309302488967)
    ·
      refine ⟨66892861329601963953733451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44595240886401309302488967 66892861329601963953733451)
      ·
        refine ⟨100339291994402945930600177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66892861329601963953733451 100339291994402945930600177)
        ·
          refine ⟨75254468995802209447950133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100339291994402945930600177 75254468995802209447950133)
          ·
            refine ⟨7055106468356457135745325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75254468995802209447950133 7055106468356457135745325)
            ·
              refine ⟨2645664925633671425904497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7055106468356457135745325 2645664925633671425904497)
              ·
                refine ⟨1984248694225253569428373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645664925633671425904497 1984248694225253569428373)
                ·
                  refine ⟨93011657541808761066955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1984248694225253569428373 93011657541808761066955)
                  ·
                    rfl

theorem cell23_1630256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_1630256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630256 prefixEnd_1630256 := by exact prefixLift 1630256
  have htrace : WordTrace (prefixWord ++ tailWord_1630256) baseStart_1630256 baseEnd_1630256 := by
    simpa [prefixWord, tailWord_1630256, baseEnd_1630256] using wordTrace_append hprefix tailTrace_1630256
  have hstable : (prefixWord ++ tailWord_1630256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630256).length < 2 ^ (prefixWord ++ tailWord_1630256).sum := by decide
  have hdescent : baseEnd_1630256 < baseStart_1630256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630259 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_1630259 : Nat := 118140960795 + 1630259 * 2 ^ 59
def prefixEnd_1630259 : Nat := 4983230072969 + 3 ^ 40 * 1630259 * 2
def baseEnd_1630259 : Nat := 837106458318242337865081

theorem tailTrace_1630259 : CollatzResearch.WordTrace tailWord_1630259 prefixEnd_1630259 837106458318242337865081 := by
  unfold tailWord_1630259
  simp only [CollatzResearch.WordTrace]
  refine ⟨59460430600857543915677831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39640287067238362610451887 59460430600857543915677831)
  ·
    refine ⟨89190645901286315873516747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59460430600857543915677831 89190645901286315873516747)
    ·
      refine ⟨133785968851929473810275121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89190645901286315873516747 133785968851929473810275121)
      ·
        refine ⟨100339476638947105357706341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133785968851929473810275121 100339476638947105357706341)
        ·
          refine ⟨18813651869802582254569939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100339476638947105357706341 18813651869802582254569939)
          ·
            refine ⟨28220477804703873381854909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18813651869802582254569939 28220477804703873381854909)
            ·
              refine ⟨10582679176763952518195591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28220477804703873381854909 10582679176763952518195591)
              ·
                refine ⟨15874018765145928777293387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10582679176763952518195591 15874018765145928777293387)
                ·
                  refine ⟨23811028147718893165940081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15874018765145928777293387 23811028147718893165940081)
                  ·
                    refine ⟨17858271110789169874455061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23811028147718893165940081 17858271110789169874455061)
                    ·
                      refine ⟨837106458318242337865081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17858271110789169874455061 837106458318242337865081)
                      ·
                        rfl

theorem cell23_1630259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_1630259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630259 prefixEnd_1630259 := by exact prefixLift 1630259
  have htrace : WordTrace (prefixWord ++ tailWord_1630259) baseStart_1630259 baseEnd_1630259 := by
    simpa [prefixWord, tailWord_1630259, baseEnd_1630259] using wordTrace_append hprefix tailTrace_1630259
  have hstable : (prefixWord ++ tailWord_1630259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630259).length < 2 ^ (prefixWord ++ tailWord_1630259).sum := by decide
  have hdescent : baseEnd_1630259 < baseStart_1630259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630293 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_1630293 : Nat := 118140960795 + 1630293 * 2 ^ 59
def prefixEnd_1630293 : Nat := 4983230072969 + 3 ^ 40 * 1630293 * 2
def baseEnd_1630293 : Nat := 837123916660495204839925

theorem tailTrace_1630293 : CollatzResearch.WordTrace tailWord_1630293 prefixEnd_1630293 837123916660495204839925 := by
  unfold tailWord_1630293
  simp only [CollatzResearch.WordTrace]
  refine ⟨59461670682734367722415533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39641113788489578481610355 59461670682734367722415533)
  ·
    refine ⟨22298126506025387895905825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59461670682734367722415533 22298126506025387895905825)
    ·
      refine ⟨16723594879519040921929369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22298126506025387895905825 16723594879519040921929369)
      ·
        refine ⟨12542696159639280691447027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16723594879519040921929369 12542696159639280691447027)
        ·
          refine ⟨18814044239458921037170541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12542696159639280691447027 18814044239458921037170541)
          ·
            refine ⟨7055266589797095388938953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18814044239458921037170541 7055266589797095388938953)
            ·
              refine ⟨5291449942347821541704215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055266589797095388938953 5291449942347821541704215)
              ·
                refine ⟨7937174913521732312556323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291449942347821541704215 7937174913521732312556323)
                ·
                  refine ⟨11905762370282598468834485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7937174913521732312556323 11905762370282598468834485)
                  ·
                    refine ⟨1116165222213993606453233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11905762370282598468834485 1116165222213993606453233)
                    ·
                      refine ⟨837123916660495204839925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116165222213993606453233 837123916660495204839925)
                      ·
                        rfl

theorem cell23_1630293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_1630293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630293 prefixEnd_1630293 := by exact prefixLift 1630293
  have htrace : WordTrace (prefixWord ++ tailWord_1630293) baseStart_1630293 baseEnd_1630293 := by
    simpa [prefixWord, tailWord_1630293, baseEnd_1630293] using wordTrace_append hprefix tailTrace_1630293
  have hstable : (prefixWord ++ tailWord_1630293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630293).length < 2 ^ (prefixWord ++ tailWord_1630293).sum := by decide
  have hdescent : baseEnd_1630293 < baseStart_1630293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630294 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1630294 : Nat := 118140960795 + 1630294 * 2 ^ 59
def prefixEnd_1630294 : Nat := 4983230072969 + 3 ^ 40 * 1630294 * 2
def baseEnd_1630294 : Nat := 279041476713716566975807

theorem tailTrace_1630294 : CollatzResearch.WordTrace tailWord_1630294 prefixEnd_1630294 279041476713716566975807 := by
  unfold tailWord_1630294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716356697233171555825121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39641138103820496595467957 3716356697233171555825121)
  ·
    refine ⟨2787267522924878666868841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3716356697233171555825121 2787267522924878666868841)
    ·
      refine ⟨2090450642193659000151631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2787267522924878666868841 2090450642193659000151631)
      ·
        refine ⟨3135675963290488500227447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090450642193659000151631 3135675963290488500227447)
        ·
          refine ⟨4703513944935732750341171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135675963290488500227447 4703513944935732750341171)
          ·
            refine ⟨7055270917403599125511757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703513944935732750341171 7055270917403599125511757)
            ·
              refine ⟨2645726594026349672066909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7055270917403599125511757 2645726594026349672066909)
              ·
                refine ⟨992147472759881127025091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2645726594026349672066909 992147472759881127025091)
                ·
                  refine ⟨1488221209139821690537637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992147472759881127025091 1488221209139821690537637)
                  ·
                    refine ⟨279041476713716566975807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488221209139821690537637 279041476713716566975807)
                    ·
                      rfl

theorem cell23_1630294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1630294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630294 prefixEnd_1630294 := by exact prefixLift 1630294
  have htrace : WordTrace (prefixWord ++ tailWord_1630294) baseStart_1630294 baseEnd_1630294 := by
    simpa [prefixWord, tailWord_1630294, baseEnd_1630294] using wordTrace_append hprefix tailTrace_1630294
  have hstable : (prefixWord ++ tailWord_1630294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630294).length < 2 ^ (prefixWord ++ tailWord_1630294).sum := by decide
  have hdescent : baseEnd_1630294 < baseStart_1630294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630336 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_1630336 : Nat := 118140960795 + 1630336 * 2 ^ 59
def prefixEnd_1630336 : Nat := 4983230072969 + 3 ^ 40 * 1630336 * 2
def baseEnd_1630336 : Nat := 837145996328638536602227

theorem tailTrace_1630336 : CollatzResearch.WordTrace tailWord_1630336 prefixEnd_1630336 837145996328638536602227 := by
  unfold tailWord_1630336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731619510789293033115431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39642159347719057377487241 29731619510789293033115431)
  ·
    refine ⟨44597429266183939549673147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29731619510789293033115431 44597429266183939549673147)
    ·
      refine ⟨66896143899275909324509721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44597429266183939549673147 66896143899275909324509721)
      ·
        refine ⟨50172107924456931993382291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66896143899275909324509721 50172107924456931993382291)
        ·
          refine ⟨75258161886685397990073437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50172107924456931993382291 75258161886685397990073437)
          ·
            refine ⟨28221810707507024246277539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75258161886685397990073437 28221810707507024246277539)
            ·
              refine ⟨42332716061260536369416309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28221810707507024246277539 42332716061260536369416309)
              ·
                refine ⟨3968692130743175284632779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42332716061260536369416309 3968692130743175284632779)
                ·
                  refine ⟨5953038196114762926949169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968692130743175284632779 5953038196114762926949169)
                  ·
                    refine ⟨4464778647086072195211877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5953038196114762926949169 4464778647086072195211877)
                    ·
                      refine ⟨837145996328638536602227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4464778647086072195211877 837145996328638536602227)
                      ·
                        rfl

theorem cell23_1630336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_1630336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630336 prefixEnd_1630336 := by exact prefixLift 1630336
  have htrace : WordTrace (prefixWord ++ tailWord_1630336) baseStart_1630336 baseEnd_1630336 := by
    simpa [prefixWord, tailWord_1630336, baseEnd_1630336] using wordTrace_append hprefix tailTrace_1630336
  have hstable : (prefixWord ++ tailWord_1630336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630336).length < 2 ^ (prefixWord ++ tailWord_1630336).sum := by decide
  have hdescent : baseEnd_1630336 < baseStart_1630336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630337 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1630337 : Nat := 118140960795 + 1630337 * 2 ^ 59
def prefixEnd_1630337 : Nat := 4983230072969 + 3 ^ 40 * 1630337 * 2
def baseEnd_1630337 : Nat := 279048836603097677563241

theorem tailTrace_1630337 : CollatzResearch.WordTrace tailWord_1630337 prefixEnd_1630337 279048836603097677563241 := by
  unfold tailWord_1630337
  simp only [CollatzResearch.WordTrace]
  refine ⟨59463275494574963237017265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39642183663049975491344843 59463275494574963237017265)
  ·
    refine ⟨44597456620931222427762949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59463275494574963237017265 44597456620931222427762949)
    ·
      refine ⟨8362023116424604205205553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44597456620931222427762949 8362023116424604205205553)
      ·
        refine ⟨6271517337318453153904165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8362023116424604205205553 6271517337318453153904165)
        ·
          refine ⟨1175909500747209966357031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6271517337318453153904165 1175909500747209966357031)
          ·
            refine ⟨1763864251120814949535547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175909500747209966357031 1763864251120814949535547)
            ·
              refine ⟨2645796376681222424303321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763864251120814949535547 2645796376681222424303321)
              ·
                refine ⟨1984347282510916818227491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645796376681222424303321 1984347282510916818227491)
                ·
                  refine ⟨2976520923766375227341237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984347282510916818227491 2976520923766375227341237)
                  ·
                    refine ⟨279048836603097677563241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2976520923766375227341237 279048836603097677563241)
                    ·
                      rfl

theorem cell23_1630337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1630337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630337 prefixEnd_1630337 := by exact prefixLift 1630337
  have htrace : WordTrace (prefixWord ++ tailWord_1630337) baseStart_1630337 baseEnd_1630337 := by
    simpa [prefixWord, tailWord_1630337, baseEnd_1630337] using wordTrace_append hprefix tailTrace_1630337
  have hstable : (prefixWord ++ tailWord_1630337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630337).length < 2 ^ (prefixWord ++ tailWord_1630337).sum := by decide
  have hdescent : baseEnd_1630337 < baseStart_1630337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630340 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_1630340 : Nat := 118140960795 + 1630340 * 2 ^ 59
def prefixEnd_1630340 : Nat := 4983230072969 + 3 ^ 40 * 1630340 * 2
def baseEnd_1630340 : Nat := 837148050251256520952209

theorem tailTrace_1630340 : CollatzResearch.WordTrace tailWord_1630340 prefixEnd_1630340 837148050251256520952209 := by
  unfold tailWord_1630340
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731692456782047374688237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39642256609042729832917649 29731692456782047374688237)
  ·
    refine ⟨11149384671293267765508089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29731692456782047374688237 11149384671293267765508089)
    ·
      refine ⟨8362038503469950824131067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11149384671293267765508089 8362038503469950824131067)
      ·
        refine ⟨12543057755204926236196601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362038503469950824131067 12543057755204926236196601)
        ·
          refine ⟨9407293316403694677147451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12543057755204926236196601 9407293316403694677147451)
          ·
            refine ⟨14110939974605542015721177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9407293316403694677147451 14110939974605542015721177)
            ·
              refine ⟨10583204980954156511790883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14110939974605542015721177 10583204980954156511790883)
              ·
                refine ⟨15874807471431234767686325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10583204980954156511790883 15874807471431234767686325)
                ·
                  refine ⟨1488263200446678259470593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15874807471431234767686325 1488263200446678259470593)
                  ·
                    refine ⟨1116197400335008694602945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488263200446678259470593 1116197400335008694602945)
                    ·
                      refine ⟨837148050251256520952209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116197400335008694602945 837148050251256520952209)
                      ·
                        rfl

theorem cell23_1630340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_1630340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630340 prefixEnd_1630340 := by exact prefixLift 1630340
  have htrace : WordTrace (prefixWord ++ tailWord_1630340) baseStart_1630340 baseEnd_1630340 := by
    simpa [prefixWord, tailWord_1630340, baseEnd_1630340] using wordTrace_append hprefix tailTrace_1630340
  have hstable : (prefixWord ++ tailWord_1630340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630340).length < 2 ^ (prefixWord ++ tailWord_1630340).sum := by decide
  have hdescent : baseEnd_1630340 < baseStart_1630340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630346 : List Nat := [3, 1, 2, 3, 1, 2, 2, 9]
def baseStart_1630346 : Nat := 118140960795 + 1630346 * 2 ^ 59
def prefixEnd_1630346 : Nat := 4983230072969 + 3 ^ 40 * 1630346 * 2
def baseEnd_1630346 : Nat := 31005597449451240647303

theorem tailTrace_1630346 : CollatzResearch.WordTrace tailWord_1630346 prefixEnd_1630346 31005597449451240647303 := by
  unfold tailWord_1630346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14865900937885589443523723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39642402501028238516063261 14865900937885589443523723)
  ·
    refine ⟨22298851406828384165285585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14865900937885589443523723 22298851406828384165285585)
    ·
      refine ⟨16724138555121288123964189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22298851406828384165285585 16724138555121288123964189)
      ·
        refine ⟨6271551958170483046486571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16724138555121288123964189 6271551958170483046486571)
        ·
          refine ⟨9407327937255724569729857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271551958170483046486571 9407327937255724569729857)
          ·
            refine ⟨7055495952941793427297393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9407327937255724569729857 7055495952941793427297393)
            ·
              refine ⟨5291621964706345070473045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055495952941793427297393 5291621964706345070473045)
              ·
                refine ⟨31005597449451240647303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5291621964706345070473045 31005597449451240647303)
                ·
                  rfl

theorem cell23_1630346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_1630346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630346 prefixEnd_1630346 := by exact prefixLift 1630346
  have htrace : WordTrace (prefixWord ++ tailWord_1630346) baseStart_1630346 baseEnd_1630346 := by
    simpa [prefixWord, tailWord_1630346, baseEnd_1630346] using wordTrace_append hprefix tailTrace_1630346
  have hstable : (prefixWord ++ tailWord_1630346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630346).length < 2 ^ (prefixWord ++ tailWord_1630346).sum := by decide
  have hdescent : baseEnd_1630346 < baseStart_1630346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630357 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_1630357 : Nat := 118140960795 + 1630357 * 2 ^ 59
def prefixEnd_1630357 : Nat := 4983230072969 + 3 ^ 40 * 1630357 * 2
def baseEnd_1630357 : Nat := 837156779422382954439631

theorem tailTrace_1630357 : CollatzResearch.WordTrace tailWord_1630357 prefixEnd_1630357 837156779422382954439631 := by
  unfold tailWord_1630357
  simp only [CollatzResearch.WordTrace]
  refine ⟨59464004954502506652745325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39642669969668337768496883 59464004954502506652745325)
  ·
    refine ⟨22299001857938439994779497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59464004954502506652745325 22299001857938439994779497)
    ·
      refine ⟨16724251393453829996084623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22299001857938439994779497 16724251393453829996084623)
      ·
        refine ⟨25086377090180744994126935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16724251393453829996084623 25086377090180744994126935)
        ·
          refine ⟨37629565635271117491190403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25086377090180744994126935 37629565635271117491190403)
          ·
            refine ⟨56444348452906676236785605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37629565635271117491190403 56444348452906676236785605)
            ·
              refine ⟨10583315334920001794397301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56444348452906676236785605 10583315334920001794397301)
              ·
                refine ⟨992185812648750168224747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10583315334920001794397301 992185812648750168224747)
                ·
                  refine ⟨1488278718973125252337121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992185812648750168224747 1488278718973125252337121)
                  ·
                    refine ⟨1116209039229843939252841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488278718973125252337121 1116209039229843939252841)
                    ·
                      refine ⟨837156779422382954439631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116209039229843939252841 837156779422382954439631)
                      ·
                        rfl

theorem cell23_1630357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_1630357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630357 prefixEnd_1630357 := by exact prefixLift 1630357
  have htrace : WordTrace (prefixWord ++ tailWord_1630357) baseStart_1630357 baseEnd_1630357 := by
    simpa [prefixWord, tailWord_1630357, baseEnd_1630357] using wordTrace_append hprefix tailTrace_1630357
  have hstable : (prefixWord ++ tailWord_1630357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630357).length < 2 ^ (prefixWord ++ tailWord_1630357).sum := by decide
  have hdescent : baseEnd_1630357 < baseStart_1630357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630360 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1630360 : Nat := 118140960795 + 1630360 * 2 ^ 59
def prefixEnd_1630360 : Nat := 4983230072969 + 3 ^ 40 * 1630360 * 2
def baseEnd_1630360 : Nat := 837158319864346442702117

theorem tailTrace_1630360 : CollatzResearch.WordTrace tailWord_1630360 prefixEnd_1630360 837158319864346442702117 := by
  unfold tailWord_1630360
  simp only [CollatzResearch.WordTrace]
  refine ⟨29732057186745819082552267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39642742915661092110069689 29732057186745819082552267)
  ·
    refine ⟨44598085780118728623828401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29732057186745819082552267 44598085780118728623828401)
    ·
      refine ⟨33448564335089046467871301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44598085780118728623828401 33448564335089046467871301)
      ·
        refine ⟨6271605812829196212725869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33448564335089046467871301 6271605812829196212725869)
        ·
          refine ⟨2351852179810948579772201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6271605812829196212725869 2351852179810948579772201)
          ·
            refine ⟨1763889134858211434829151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2351852179810948579772201 1763889134858211434829151)
            ·
              refine ⟨2645833702287317152243727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763889134858211434829151 2645833702287317152243727)
              ·
                refine ⟨3968750553430975728365591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645833702287317152243727 3968750553430975728365591)
                ·
                  refine ⟨5953125830146463592548387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968750553430975728365591 5953125830146463592548387)
                  ·
                    refine ⟨8929688745219695388822581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5953125830146463592548387 8929688745219695388822581)
                    ·
                      refine ⟨837158319864346442702117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8929688745219695388822581 837158319864346442702117)
                      ·
                        rfl

theorem cell23_1630360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1630360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630360 prefixEnd_1630360 := by exact prefixLift 1630360
  have htrace : WordTrace (prefixWord ++ tailWord_1630360) baseStart_1630360 baseEnd_1630360 := by
    simpa [prefixWord, tailWord_1630360, baseEnd_1630360] using wordTrace_append hprefix tailTrace_1630360
  have hstable : (prefixWord ++ tailWord_1630360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630360).length < 2 ^ (prefixWord ++ tailWord_1630360).sum := by decide
  have hdescent : baseEnd_1630360 < baseStart_1630360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630400 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 3, 3, 2]
def baseStart_1630400 : Nat := 118140960795 + 1630400 * 2 ^ 59
def prefixEnd_1630400 : Nat := 4983230072969 + 3 ^ 40 * 1630400 * 2
def baseEnd_1630400 : Nat := 837178859090526286201933

theorem tailTrace_1630400 : CollatzResearch.WordTrace tailWord_1630400 prefixEnd_1630400 837178859090526286201933 := by
  unfold tailWord_1630400
  simp only [CollatzResearch.WordTrace]
  refine ⟨29732786646673362498280327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39643715528897816664373769 29732786646673362498280327)
  ·
    refine ⟨44599179970010043747420491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29732786646673362498280327 44599179970010043747420491)
    ·
      refine ⟨66898769955015065621130737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44599179970010043747420491 66898769955015065621130737)
      ·
        refine ⟨50174077466261299215848053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66898769955015065621130737 50174077466261299215848053)
        ·
          refine ⟨4703819762461996801485755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50174077466261299215848053 4703819762461996801485755)
          ·
            refine ⟨7055729643692995202228633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703819762461996801485755 7055729643692995202228633)
            ·
              refine ⟨5291797232769746401671475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055729643692995202228633 5291797232769746401671475)
              ·
                refine ⟨7937695849154619602507213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291797232769746401671475 7937695849154619602507213)
                ·
                  refine ⟨2976635943432982350940205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7937695849154619602507213 2976635943432982350940205)
                  ·
                    refine ⟨1116238478787368381602577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976635943432982350940205 1116238478787368381602577)
                    ·
                      refine ⟨837178859090526286201933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116238478787368381602577 837178859090526286201933)
                      ·
                        rfl

theorem cell23_1630400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_1630400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630400 prefixEnd_1630400 := by exact prefixLift 1630400
  have htrace : WordTrace (prefixWord ++ tailWord_1630400) baseStart_1630400 baseEnd_1630400 := by
    simpa [prefixWord, tailWord_1630400, baseEnd_1630400] using wordTrace_append hprefix tailTrace_1630400
  have hstable : (prefixWord ++ tailWord_1630400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630400).length < 2 ^ (prefixWord ++ tailWord_1630400).sum := by decide
  have hdescent : baseEnd_1630400 < baseStart_1630400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630417 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 1, 3, 2]
def baseStart_1630417 : Nat := 118140960795 + 1630417 * 2 ^ 59
def prefixEnd_1630417 : Nat := 4983230072969 + 3 ^ 40 * 1630417 * 2
def baseEnd_1630417 : Nat := 837187588261652719689355

theorem tailTrace_1630417 : CollatzResearch.WordTrace tailWord_1630417 prefixEnd_1630417 837187588261652719689355 := by
  unfold tailWord_1630417
  simp only [CollatzResearch.WordTrace]
  refine ⟨59466193334285136899929505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39644128889523424599953003 59466193334285136899929505)
  ·
    refine ⟨44599645000713852674947129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59466193334285136899929505 44599645000713852674947129)
    ·
      refine ⟨33449733750535389506210347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44599645000713852674947129 33449733750535389506210347)
      ·
        refine ⟨50174600625803084259315521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33449733750535389506210347 50174600625803084259315521)
        ·
          refine ⟨37630950469352313194486641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50174600625803084259315521 37630950469352313194486641)
          ·
            refine ⟨28223212852014234895864981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37630950469352313194486641 28223212852014234895864981)
            ·
              refine ⟨1322963102438167260743671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28223212852014234895864981 1322963102438167260743671)
              ·
                refine ⟨1984444653657250891115507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322963102438167260743671 1984444653657250891115507)
                ·
                  refine ⟨2976666980485876336673261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984444653657250891115507 2976666980485876336673261)
                  ·
                    refine ⟨1116250117682203626252473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2976666980485876336673261 1116250117682203626252473)
                    ·
                      refine ⟨837187588261652719689355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116250117682203626252473 837187588261652719689355)
                      ·
                        rfl

theorem cell23_1630417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_1630417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630417 prefixEnd_1630417 := by exact prefixLift 1630417
  have htrace : WordTrace (prefixWord ++ tailWord_1630417) baseStart_1630417 baseEnd_1630417 := by
    simpa [prefixWord, tailWord_1630417, baseEnd_1630417] using wordTrace_append hprefix tailTrace_1630417
  have hstable : (prefixWord ++ tailWord_1630417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630417).length < 2 ^ (prefixWord ++ tailWord_1630417).sum := by decide
  have hdescent : baseEnd_1630417 < baseStart_1630417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630447 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 1, 4, 2]
def baseStart_1630447 : Nat := 118140960795 + 1630447 * 2 ^ 59
def prefixEnd_1630447 : Nat := 4983230072969 + 3 ^ 40 * 1630447 * 2
def baseEnd_1630447 : Nat := 837202992681287602314217

theorem tailTrace_1630447 : CollatzResearch.WordTrace tailWord_1630447 prefixEnd_1630447 837202992681287602314217 := by
  unfold tailWord_1630447
  simp only [CollatzResearch.WordTrace]
  refine ⟨59467287524176452023521595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39644858349450968015681063 59467287524176452023521595)
  ·
    refine ⟨89200931286264678035282393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59467287524176452023521595 89200931286264678035282393)
    ·
      refine ⟨66900698464698508526461795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89200931286264678035282393 66900698464698508526461795)
      ·
        refine ⟨100351047697047762789692693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66900698464698508526461795 100351047697047762789692693)
        ·
          refine ⟨4703955360799113880766845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100351047697047762789692693 4703955360799113880766845)
          ·
            refine ⟨1763983260299667705287567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4703955360799113880766845 1763983260299667705287567)
            ·
              refine ⟨2645974890449501557931351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763983260299667705287567 2645974890449501557931351)
              ·
                refine ⟨3968962335674252336897027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645974890449501557931351 3968962335674252336897027)
                ·
                  refine ⟨5953443503511378505345541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968962335674252336897027 5953443503511378505345541)
                  ·
                    refine ⟨1116270656908383469752289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953443503511378505345541 1116270656908383469752289)
                    ·
                      refine ⟨837202992681287602314217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116270656908383469752289 837202992681287602314217)
                      ·
                        rfl

theorem cell23_1630447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 4, 2].length) (baseStart_1630447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630447 prefixEnd_1630447 := by exact prefixLift 1630447
  have htrace : WordTrace (prefixWord ++ tailWord_1630447) baseStart_1630447 baseEnd_1630447 := by
    simpa [prefixWord, tailWord_1630447, baseEnd_1630447] using wordTrace_append hprefix tailTrace_1630447
  have hstable : (prefixWord ++ tailWord_1630447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630447).length < 2 ^ (prefixWord ++ tailWord_1630447).sum := by decide
  have hdescent : baseEnd_1630447 < baseStart_1630447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630487 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 5]
def baseStart_1630487 : Nat := 118140960795 + 1630487 * 2 ^ 59
def prefixEnd_1630487 : Nat := 4983230072969 + 3 ^ 40 * 1630487 * 2
def baseEnd_1630487 : Nat := 93024836878607493979337

theorem tailTrace_1630487 : CollatzResearch.WordTrace tailWord_1630487 prefixEnd_1630487 93024836878607493979337 := by
  unfold tailWord_1630487
  simp only [CollatzResearch.WordTrace]
  refine ⟨59468746444031538854977715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39645830962687692569985143 59468746444031538854977715)
  ·
    refine ⟨89203119666047308282466573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59468746444031538854977715 89203119666047308282466573)
    ·
      refine ⟨33451169874767740605924965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89203119666047308282466573 33451169874767740605924965)
      ·
        refine ⟨6272094351518951363610931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33451169874767740605924965 6272094351518951363610931)
        ·
          refine ⟨9408141527278427045416397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6272094351518951363610931 9408141527278427045416397)
          ·
            refine ⟨3528053072729410142031149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9408141527278427045416397 3528053072729410142031149)
            ·
              refine ⟨1323019902273528803261681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3528053072729410142031149 1323019902273528803261681)
              ·
                refine ⟨992264926705146602446261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323019902273528803261681 992264926705146602446261)
                ·
                  refine ⟨93024836878607493979337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992264926705146602446261 93024836878607493979337)
                  ·
                    rfl

theorem cell23_1630487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 5].length) (baseStart_1630487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630487 prefixEnd_1630487 := by exact prefixLift 1630487
  have htrace : WordTrace (prefixWord ++ tailWord_1630487) baseStart_1630487 baseEnd_1630487 := by
    simpa [prefixWord, tailWord_1630487, baseEnd_1630487] using wordTrace_append hprefix tailTrace_1630487
  have hstable : (prefixWord ++ tailWord_1630487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630487).length < 2 ^ (prefixWord ++ tailWord_1630487).sum := by decide
  have hdescent : baseEnd_1630487 < baseStart_1630487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630540 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1630540 : Nat := 118140960795 + 1630540 * 2 ^ 59
def prefixEnd_1630540 : Nat := 4983230072969 + 3 ^ 40 * 1630540 * 2
def baseEnd_1630540 : Nat := 837250746382155738451289

theorem tailTrace_1630540 : CollatzResearch.WordTrace tailWord_1630540 prefixEnd_1630540 837250746382155738451289 := by
  unfold tailWord_1630540
  simp only [CollatzResearch.WordTrace]
  refine ⟨29735339756419764453328537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39647119675226352604438049 29735339756419764453328537)
  ·
    refine ⟨22301504817314823339996403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29735339756419764453328537 22301504817314823339996403)
    ·
      refine ⟨33452257225972235009994605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22301504817314823339996403 33452257225972235009994605)
      ·
        refine ⟨12544596459739588128747977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33452257225972235009994605 12544596459739588128747977)
        ·
          refine ⟨9408447344804691096560983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12544596459739588128747977 9408447344804691096560983)
          ·
            refine ⟨14112671017207036644841475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408447344804691096560983 14112671017207036644841475)
            ·
              refine ⟨21169006525810554967262213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14112671017207036644841475 21169006525810554967262213)
              ·
                refine ⟨3969188723589479056361665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21169006525810554967262213 3969188723589479056361665)
                ·
                  refine ⟨2976891542692109292271249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969188723589479056361665 2976891542692109292271249)
                  ·
                    refine ⟨2232668657019081969203437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2976891542692109292271249 2232668657019081969203437)
                    ·
                      refine ⟨837250746382155738451289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2232668657019081969203437 837250746382155738451289)
                      ·
                        rfl

theorem cell23_1630540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1630540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630540 prefixEnd_1630540 := by exact prefixLift 1630540
  have htrace : WordTrace (prefixWord ++ tailWord_1630540) baseStart_1630540 baseEnd_1630540 := by
    simpa [prefixWord, tailWord_1630540, baseEnd_1630540] using wordTrace_append hprefix tailTrace_1630540
  have hstable : (prefixWord ++ tailWord_1630540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630540).length < 2 ^ (prefixWord ++ tailWord_1630540).sum := by decide
  have hdescent : baseEnd_1630540 < baseStart_1630540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630553 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_1630553 : Nat := 118140960795 + 1630553 * 2 ^ 59
def prefixEnd_1630553 : Nat := 4983230072969 + 3 ^ 40 * 1630553 * 2
def baseEnd_1630553 : Nat := 837257421630664187588729

theorem tailTrace_1630553 : CollatzResearch.WordTrace tailWord_1630553 prefixEnd_1630553 837257421630664187588729 := by
  unfold tailWord_1630553
  simp only [CollatzResearch.WordTrace]
  refine ⟨59471153661792432126880313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39647435774528288084586875 59471153661792432126880313)
  ·
    refine ⟨44603365246344324095160235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59471153661792432126880313 44603365246344324095160235)
    ·
      refine ⟨66905047869516486142740353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44603365246344324095160235 66905047869516486142740353)
      ·
        refine ⟨50178785902137364607055265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66905047869516486142740353 50178785902137364607055265)
        ·
          refine ⟨37634089426603023455291449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50178785902137364607055265 37634089426603023455291449)
          ·
            refine ⟨28225567069952267591468587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37634089426603023455291449 28225567069952267591468587)
            ·
              refine ⟨42338350604928401387202881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28225567069952267591468587 42338350604928401387202881)
              ·
                refine ⟨31753762953696301040402161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42338350604928401387202881 31753762953696301040402161)
                ·
                  refine ⟨23815322215272225780301621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31753762953696301040402161 23815322215272225780301621)
                  ·
                    refine ⟨2232686457681771166903277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23815322215272225780301621 2232686457681771166903277)
                    ·
                      refine ⟨837257421630664187588729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2232686457681771166903277 837257421630664187588729)
                      ·
                        rfl

theorem cell23_1630553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_1630553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630553 prefixEnd_1630553 := by exact prefixLift 1630553
  have htrace : WordTrace (prefixWord ++ tailWord_1630553) baseStart_1630553 baseEnd_1630553 := by
    simpa [prefixWord, tailWord_1630553, baseEnd_1630553] using wordTrace_append hprefix tailTrace_1630553
  have hstable : (prefixWord ++ tailWord_1630553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630553).length < 2 ^ (prefixWord ++ tailWord_1630553).sum := by decide
  have hdescent : baseEnd_1630553 < baseStart_1630553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630604 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 1, 1, 3]
def baseStart_1630604 : Nat := 118140960795 + 1630604 * 2 ^ 59
def prefixEnd_1630604 : Nat := 4983230072969 + 3 ^ 40 * 1630604 * 2
def baseEnd_1630604 : Nat := 837283609144043488050995

theorem tailTrace_1630604 : CollatzResearch.WordTrace tailWord_1630604 prefixEnd_1630604 837283609144043488050995 := by
  unfold tailWord_1630604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29736506892303833918493433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39648675856405111891324577 29736506892303833918493433)
  ·
    refine ⟨22302380169227875438870075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29736506892303833918493433 22302380169227875438870075)
    ·
      refine ⟨33453570253841813158305113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22302380169227875438870075 33453570253841813158305113)
      ·
        refine ⟨25090177690381359868728835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33453570253841813158305113 25090177690381359868728835)
        ·
          refine ⟨37635266535572039803093253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25090177690381359868728835 37635266535572039803093253)
          ·
            refine ⟨7056612475419757463079985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37635266535572039803093253 7056612475419757463079985)
            ·
              refine ⟨5292459356564818097309989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7056612475419757463079985 5292459356564818097309989)
              ·
                refine ⟨992336129355903393245623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5292459356564818097309989 992336129355903393245623)
                ·
                  refine ⟨1488504194033855089868435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992336129355903393245623 1488504194033855089868435)
                  ·
                    refine ⟨2232756291050782634802653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1488504194033855089868435 2232756291050782634802653)
                    ·
                      refine ⟨837283609144043488050995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2232756291050782634802653 837283609144043488050995)
                      ·
                        rfl

theorem cell23_1630604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_1630604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630604 prefixEnd_1630604 := by exact prefixLift 1630604
  have htrace : WordTrace (prefixWord ++ tailWord_1630604) baseStart_1630604 baseEnd_1630604 := by
    simpa [prefixWord, tailWord_1630604, baseEnd_1630604] using wordTrace_append hprefix tailTrace_1630604
  have hstable : (prefixWord ++ tailWord_1630604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630604).length < 2 ^ (prefixWord ++ tailWord_1630604).sum := by decide
  have hdescent : baseEnd_1630604 < baseStart_1630604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630627 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1630627 : Nat := 118140960795 + 1630627 * 2 ^ 59
def prefixEnd_1630627 : Nat := 4983230072969 + 3 ^ 40 * 1630627 * 2
def baseEnd_1630627 : Nat := 837295419199096898063389

theorem tailTrace_1630627 : CollatzResearch.WordTrace tailWord_1630627 prefixEnd_1630627 837295419199096898063389 := by
  unfold tailWord_1630627
  simp only [CollatzResearch.WordTrace]
  refine ⟨59473852663524342765074135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39649235109016228510049423 59473852663524342765074135)
  ·
    refine ⟨89210778995286514147611203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59473852663524342765074135 89210778995286514147611203)
    ·
      refine ⟨133816168492929771221416805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89210778995286514147611203 133816168492929771221416805)
      ·
        refine ⟨25090531592424332104015651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133816168492929771221416805 25090531592424332104015651)
        ·
          refine ⟨37635797388636498156023477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25090531592424332104015651 37635797388636498156023477)
          ·
            refine ⟨3528356005184671702127201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37635797388636498156023477 3528356005184671702127201)
            ·
              refine ⟨2646267003888503776595401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528356005184671702127201 2646267003888503776595401)
              ·
                refine ⟨1984700252916377832446551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646267003888503776595401 1984700252916377832446551)
                ·
                  refine ⟨2977050379374566748669827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984700252916377832446551 2977050379374566748669827)
                  ·
                    refine ⟨4465575569061850123004741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2977050379374566748669827 4465575569061850123004741)
                    ·
                      refine ⟨837295419199096898063389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4465575569061850123004741 837295419199096898063389)
                      ·
                        rfl

theorem cell23_1630627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1630627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630627 prefixEnd_1630627 := by exact prefixLift 1630627
  have htrace : WordTrace (prefixWord ++ tailWord_1630627) baseStart_1630627 baseEnd_1630627 := by
    simpa [prefixWord, tailWord_1630627, baseEnd_1630627] using wordTrace_append hprefix tailTrace_1630627
  have hstable : (prefixWord ++ tailWord_1630627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630627).length < 2 ^ (prefixWord ++ tailWord_1630627).sum := by decide
  have hdescent : baseEnd_1630627 < baseStart_1630627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630647 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_1630647 : Nat := 118140960795 + 1630647 * 2 ^ 59
def prefixEnd_1630647 : Nat := 4983230072969 + 3 ^ 40 * 1630647 * 2
def baseEnd_1630647 : Nat := 837305688812186819813297

theorem tailTrace_1630647 : CollatzResearch.WordTrace tailWord_1630647 prefixEnd_1630647 837305688812186819813297 := by
  unfold tailWord_1630647
  simp only [CollatzResearch.WordTrace]
  refine ⟨59474582123451886180802195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39649721415634590787201463 59474582123451886180802195)
  ·
    refine ⟨89211873185177829271203293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59474582123451886180802195 89211873185177829271203293)
    ·
      refine ⟨33454452444441685976701235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89211873185177829271203293 33454452444441685976701235)
      ·
        refine ⟨50181678666662528965051853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33454452444441685976701235 50181678666662528965051853)
        ·
          refine ⟨18818129499998448361894445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50181678666662528965051853 18818129499998448361894445)
          ·
            refine ⟨7056798562499418135710417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18818129499998448361894445 7056798562499418135710417)
            ·
              refine ⟨5292598921874563601782813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7056798562499418135710417 5292598921874563601782813)
              ·
                refine ⟨1984724595702961350668555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5292598921874563601782813 1984724595702961350668555)
                ·
                  refine ⟨2977086893554442026002833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984724595702961350668555 2977086893554442026002833)
                  ·
                    refine ⟨2232815170165831519502125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2977086893554442026002833 2232815170165831519502125)
                    ·
                      refine ⟨837305688812186819813297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2232815170165831519502125 837305688812186819813297)
                      ·
                        rfl

theorem cell23_1630647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_1630647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630647 prefixEnd_1630647 := by exact prefixLift 1630647
  have htrace : WordTrace (prefixWord ++ tailWord_1630647) baseStart_1630647 baseEnd_1630647 := by
    simpa [prefixWord, tailWord_1630647, baseEnd_1630647] using wordTrace_append hprefix tailTrace_1630647
  have hstable : (prefixWord ++ tailWord_1630647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630647).length < 2 ^ (prefixWord ++ tailWord_1630647).sum := by decide
  have hdescent : baseEnd_1630647 < baseStart_1630647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630717 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_1630717 : Nat := 118140960795 + 1630717 * 2 ^ 59
def prefixEnd_1630717 : Nat := 4983230072969 + 3 ^ 40 * 1630717 * 2
def baseEnd_1630717 : Nat := 837341632458001545937975

theorem tailTrace_1630717 : CollatzResearch.WordTrace tailWord_1630717 prefixEnd_1630717 837341632458001545937975 := by
  unfold tailWord_1630717
  simp only [CollatzResearch.WordTrace]
  refine ⟨59477135233198288135850405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39651423488798858757233603 59477135233198288135850405)
  ·
    refine ⟨11151962856224679025471951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59477135233198288135850405 11151962856224679025471951)
    ·
      refine ⟨16727944284337018538207927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11151962856224679025471951 16727944284337018538207927)
      ·
        refine ⟨25091916426505527807311891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16727944284337018538207927 25091916426505527807311891)
        ·
          refine ⟨37637874639758291710967837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25091916426505527807311891 37637874639758291710967837)
          ·
            refine ⟨14114202989909359391612939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37637874639758291710967837 14114202989909359391612939)
            ·
              refine ⟨21171304484864039087419409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14114202989909359391612939 21171304484864039087419409)
              ·
                refine ⟨15878478363648029315564557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21171304484864039087419409 15878478363648029315564557)
                ·
                  refine ⟨5954429386368010993336709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15878478363648029315564557 5954429386368010993336709)
                  ·
                    refine ⟨1116455509944002061250633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954429386368010993336709 1116455509944002061250633)
                    ·
                      refine ⟨837341632458001545937975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116455509944002061250633 837341632458001545937975)
                      ·
                        rfl

theorem cell23_1630717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_1630717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630717 prefixEnd_1630717 := by exact prefixLift 1630717
  have htrace : WordTrace (prefixWord ++ tailWord_1630717) baseStart_1630717 baseEnd_1630717 := by
    simpa [prefixWord, tailWord_1630717, baseEnd_1630717] using wordTrace_append hprefix tailTrace_1630717
  have hstable : (prefixWord ++ tailWord_1630717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630717).length < 2 ^ (prefixWord ++ tailWord_1630717).sum := by decide
  have hdescent : baseEnd_1630717 < baseStart_1630717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630727 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 2, 6]
def baseStart_1630727 : Nat := 118140960795 + 1630727 * 2 ^ 59
def prefixEnd_1630727 : Nat := 4983230072969 + 3 ^ 40 * 1630727 * 2
def baseEnd_1630727 : Nat := 279115589088182168937643

theorem tailTrace_1630727 : CollatzResearch.WordTrace tailWord_1630727 prefixEnd_1630727 279115589088182168937643 := by
  unfold tailWord_1630727
  simp only [CollatzResearch.WordTrace]
  refine ⟨59477499963162059843714435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39651666642108039895809623 59477499963162059843714435)
  ·
    refine ⟨89216249944743089765571653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59477499963162059843714435 89216249944743089765571653)
    ·
      refine ⟨16728046864639329331044685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89216249944743089765571653 16728046864639329331044685)
      ·
        refine ⟨6273017574239748499141757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16728046864639329331044685 6273017574239748499141757)
        ·
          refine ⟨2352381590339905687178159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6273017574239748499141757 2352381590339905687178159)
          ·
            refine ⟨3528572385509858530767239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352381590339905687178159 3528572385509858530767239)
            ·
              refine ⟨5292858578264787796150859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528572385509858530767239 5292858578264787796150859)
              ·
                refine ⟨7939287867397181694226289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292858578264787796150859 7939287867397181694226289)
                ·
                  refine ⟨5954465900547886270669717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939287867397181694226289 5954465900547886270669717)
                  ·
                    refine ⟨279115589088182168937643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5954465900547886270669717 279115589088182168937643)
                    ·
                      rfl

theorem cell23_1630727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_1630727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630727 prefixEnd_1630727 := by exact prefixLift 1630727
  have htrace : WordTrace (prefixWord ++ tailWord_1630727) baseStart_1630727 baseEnd_1630727 := by
    simpa [prefixWord, tailWord_1630727, baseEnd_1630727] using wordTrace_append hprefix tailTrace_1630727
  have hstable : (prefixWord ++ tailWord_1630727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630727).length < 2 ^ (prefixWord ++ tailWord_1630727).sum := by decide
  have hdescent : baseEnd_1630727 < baseStart_1630727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630734 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1630734 : Nat := 118140960795 + 1630734 * 2 ^ 59
def prefixEnd_1630734 : Nat := 4983230072969 + 3 ^ 40 * 1630734 * 2
def baseEnd_1630734 : Nat := 837350361629127979425397

theorem tailTrace_1630734 : CollatzResearch.WordTrace tailWord_1630734 prefixEnd_1630734 837350361629127979425397 := by
  unfold tailWord_1630734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7434719409267087504902407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39651836849424466692812837 7434719409267087504902407)
  ·
    refine ⟨11152079113900631257353611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7434719409267087504902407 11152079113900631257353611)
    ·
      refine ⟨16728118670850946886030417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152079113900631257353611 16728118670850946886030417)
      ·
        refine ⟨12546089003138210164522813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16728118670850946886030417 12546089003138210164522813)
        ·
          refine ⟨4704783376176828811696055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12546089003138210164522813 4704783376176828811696055)
          ·
            refine ⟨7057175064265243217544083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704783376176828811696055 7057175064265243217544083)
            ·
              refine ⟨10585762596397864826316125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057175064265243217544083 10585762596397864826316125)
              ·
                refine ⟨3969660973649199309868547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10585762596397864826316125 3969660973649199309868547)
                ·
                  refine ⟨5954491460473798964802821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969660973649199309868547 5954491460473798964802821)
                  ·
                    refine ⟨1116467148838837305900529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954491460473798964802821 1116467148838837305900529)
                    ·
                      refine ⟨837350361629127979425397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116467148838837305900529 837350361629127979425397)
                      ·
                        rfl

theorem cell23_1630734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1630734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630734 prefixEnd_1630734 := by exact prefixLift 1630734
  have htrace : WordTrace (prefixWord ++ tailWord_1630734) baseStart_1630734 baseEnd_1630734 := by
    simpa [prefixWord, tailWord_1630734, baseEnd_1630734] using wordTrace_append hprefix tailTrace_1630734
  have hstable : (prefixWord ++ tailWord_1630734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630734).length < 2 ^ (prefixWord ++ tailWord_1630734).sum := by decide
  have hdescent : baseEnd_1630734 < baseStart_1630734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630757 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 5]
def baseStart_1630757 : Nat := 118140960795 + 1630757 * 2 ^ 59
def prefixEnd_1630757 : Nat := 4983230072969 + 3 ^ 40 * 1630757 * 2
def baseEnd_1630757 : Nat := 93040241298242376604199

theorem tailTrace_1630757 : CollatzResearch.WordTrace tailWord_1630757 prefixEnd_1630757 93040241298242376604199 := by
  unfold tailWord_1630757
  simp only [CollatzResearch.WordTrace]
  refine ⟨59478594153053374967306525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39652396102035583311537683 59478594153053374967306525)
  ·
    refine ⟨22304472807395015612739947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59478594153053374967306525 22304472807395015612739947)
    ·
      refine ⟨33456709211092523419109921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22304472807395015612739947 33456709211092523419109921)
      ·
        refine ⟨25092531908319392564332441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33456709211092523419109921 25092531908319392564332441)
        ·
          refine ⟨18819398931239544423249331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25092531908319392564332441 18819398931239544423249331)
          ·
            refine ⟨28229098396859316634873997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18819398931239544423249331 28229098396859316634873997)
            ·
              refine ⟨10585911898822243738077749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28229098396859316634873997 10585911898822243738077749)
              ·
                refine ⟨992429240514585350444789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10585911898822243738077749 992429240514585350444789)
                ·
                  refine ⟨93040241298242376604199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992429240514585350444789 93040241298242376604199)
                  ·
                    rfl

theorem cell23_1630757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_1630757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630757 prefixEnd_1630757 := by exact prefixLift 1630757
  have htrace : WordTrace (prefixWord ++ tailWord_1630757) baseStart_1630757 baseEnd_1630757 := by
    simpa [prefixWord, tailWord_1630757, baseEnd_1630757] using wordTrace_append hprefix tailTrace_1630757
  have hstable : (prefixWord ++ tailWord_1630757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630757).length < 2 ^ (prefixWord ++ tailWord_1630757).sum := by decide
  have hdescent : baseEnd_1630757 < baseStart_1630757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630774 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1630774 : Nat := 118140960795 + 1630774 * 2 ^ 59
def prefixEnd_1630774 : Nat := 4983230072969 + 3 ^ 40 * 1630774 * 2
def baseEnd_1630774 : Nat := 93041211206145313658357

theorem tailTrace_1630774 : CollatzResearch.WordTrace tailWord_1630774 prefixEnd_1630774 93041211206145313658357 := by
  unfold tailWord_1630774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717450887124486679417211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39652809462661191247116917 3717450887124486679417211)
  ·
    refine ⟨5576176330686730019125817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717450887124486679417211 5576176330686730019125817)
    ·
      refine ⟨4182132248015047514344363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5576176330686730019125817 4182132248015047514344363)
      ·
        refine ⟨6273198372022571271516545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182132248015047514344363 6273198372022571271516545)
        ·
          refine ⟨4704898779016928453637409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6273198372022571271516545 4704898779016928453637409)
          ·
            refine ⟨3528674084262696340228057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704898779016928453637409 3528674084262696340228057)
            ·
              refine ⟨2646505563197022255171043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528674084262696340228057 2646505563197022255171043)
              ·
                refine ⟨3969758344795533382756565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646505563197022255171043 3969758344795533382756565)
                ·
                  refine ⟨93041211206145313658357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3969758344795533382756565 93041211206145313658357)
                  ·
                    rfl

theorem cell23_1630774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1630774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630774 prefixEnd_1630774 := by exact prefixLift 1630774
  have htrace : WordTrace (prefixWord ++ tailWord_1630774) baseStart_1630774 baseEnd_1630774 := by
    simpa [prefixWord, tailWord_1630774, baseEnd_1630774] using wordTrace_append hprefix tailTrace_1630774
  have hstable : (prefixWord ++ tailWord_1630774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630774).length < 2 ^ (prefixWord ++ tailWord_1630774).sum := by decide
  have hdescent : baseEnd_1630774 < baseStart_1630774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630807 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1630807 : Nat := 118140960795 + 1630807 * 2 ^ 59
def prefixEnd_1630807 : Nat := 4983230072969 + 3 ^ 40 * 1630807 * 2
def baseEnd_1630807 : Nat := 837387845716906193812561

theorem tailTrace_1630807 : CollatzResearch.WordTrace tailWord_1630807 prefixEnd_1630807 837387845716906193812561 := by
  unfold tailWord_1630807
  simp only [CollatzResearch.WordTrace]
  refine ⟨59480417802872233506626675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39653611868581489004417783 59480417802872233506626675)
  ·
    refine ⟨89220626704308350259940013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59480417802872233506626675 89220626704308350259940013)
    ·
      refine ⟨33457735014115631347477505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89220626704308350259940013 33457735014115631347477505)
      ·
        refine ⟨25093301260586723510608129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33457735014115631347477505 25093301260586723510608129)
        ·
          refine ⟨18819975945440042632956097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25093301260586723510608129 18819975945440042632956097)
          ·
            refine ⟨14114981959080031974717073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18819975945440042632956097 14114981959080031974717073)
            ·
              refine ⟨10586236469310023981037805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14114981959080031974717073 10586236469310023981037805)
              ·
                refine ⟨3969838675991258992889177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10586236469310023981037805 3969838675991258992889177)
                ·
                  refine ⟨2977379006993444244666883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969838675991258992889177 2977379006993444244666883)
                  ·
                    refine ⟨4466068510490166367000325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2977379006993444244666883 4466068510490166367000325)
                    ·
                      refine ⟨837387845716906193812561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4466068510490166367000325 837387845716906193812561)
                      ·
                        rfl

theorem cell23_1630807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1630807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630807 prefixEnd_1630807 := by exact prefixLift 1630807
  have htrace : WordTrace (prefixWord ++ tailWord_1630807) baseStart_1630807 baseEnd_1630807 := by
    simpa [prefixWord, tailWord_1630807, baseEnd_1630807] using wordTrace_append hprefix tailTrace_1630807
  have hstable : (prefixWord ++ tailWord_1630807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630807).length < 2 ^ (prefixWord ++ tailWord_1630807).sum := by decide
  have hdescent : baseEnd_1630807 < baseStart_1630807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630810 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1630810 : Nat := 118140960795 + 1630810 * 2 ^ 59
def prefixEnd_1630810 : Nat := 4983230072969 + 3 ^ 40 * 1630810 * 2
def baseEnd_1630810 : Nat := 837389386158869682075047

theorem tailTrace_1630810 : CollatzResearch.WordTrace tailWord_1630810 prefixEnd_1630810 837389386158869682075047 := by
  unfold tailWord_1630810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870131805465341254746471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39653684814574243345990589 14870131805465341254746471)
  ·
    refine ⟨22305197708198011882119707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14870131805465341254746471 22305197708198011882119707)
    ·
      refine ⟨33457796562297017823179561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22305197708198011882119707 33457796562297017823179561)
      ·
        refine ⟨25093347421722763367384671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33457796562297017823179561 25093347421722763367384671)
        ·
          refine ⟨37640021132584145051077007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25093347421722763367384671 37640021132584145051077007)
          ·
            refine ⟨56460031698876217576615511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37640021132584145051077007 56460031698876217576615511)
            ·
              refine ⟨84690047548314326364923267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56460031698876217576615511 84690047548314326364923267)
              ·
                refine ⟨127035071322471489547384901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84690047548314326364923267 127035071322471489547384901)
                ·
                  refine ⟨23819075872963404290134669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127035071322471489547384901 23819075872963404290134669)
                  ·
                    refine ⟨8932153452361276608800501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23819075872963404290134669 8932153452361276608800501)
                    ·
                      refine ⟨837389386158869682075047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8932153452361276608800501 837389386158869682075047)
                      ·
                        rfl

theorem cell23_1630810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1630810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630810 prefixEnd_1630810 := by exact prefixLift 1630810
  have htrace : WordTrace (prefixWord ++ tailWord_1630810) baseStart_1630810 baseEnd_1630810 := by
    simpa [prefixWord, tailWord_1630810, baseEnd_1630810] using wordTrace_append hprefix tailTrace_1630810
  have hstable : (prefixWord ++ tailWord_1630810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630810).length < 2 ^ (prefixWord ++ tailWord_1630810).sum := by decide
  have hdescent : baseEnd_1630810 < baseStart_1630810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630907 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 8, 4]
def baseStart_1630907 : Nat := 118140960795 + 1630907 * 2 ^ 59
def prefixEnd_1630907 : Nat := 4983230072969 + 3 ^ 40 * 1630907 * 2
def baseEnd_1630907 : Nat := 279146397927451934187367

theorem tailTrace_1630907 : CollatzResearch.WordTrace tailWord_1630907 prefixEnd_1630907 279146397927451934187367 := by
  unfold tailWord_1630907
  simp only [CollatzResearch.WordTrace]
  refine ⟨59484065102509950585266975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39656043401673300390177983 59484065102509950585266975)
  ·
    refine ⟨89226097653764925877900463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59484065102509950585266975 89226097653764925877900463)
    ·
      refine ⟨133839146480647388816850695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89226097653764925877900463 133839146480647388816850695)
      ·
        refine ⟨200758719720971083225276043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133839146480647388816850695 200758719720971083225276043)
        ·
          refine ⟨301138079581456624837914065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200758719720971083225276043 301138079581456624837914065)
          ·
            refine ⟨225853559686092468628435549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301138079581456624837914065 225853559686092468628435549)
            ·
              refine ⟨84695084882284675735663331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225853559686092468628435549 84695084882284675735663331)
              ·
                refine ⟨127042627323427013603494997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84695084882284675735663331 127042627323427013603494997)
                ·
                  refine ⟨1488780788946410315665957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 127042627323427013603494997 1488780788946410315665957)
                  ·
                    refine ⟨279146397927451934187367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488780788946410315665957 279146397927451934187367)
                    ·
                      rfl

theorem cell23_1630907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 4].length) (baseStart_1630907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630907 prefixEnd_1630907 := by exact prefixLift 1630907
  have htrace : WordTrace (prefixWord ++ tailWord_1630907) baseStart_1630907 baseEnd_1630907 := by
    simpa [prefixWord, tailWord_1630907, baseEnd_1630907] using wordTrace_append hprefix tailTrace_1630907
  have hstable : (prefixWord ++ tailWord_1630907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630907).length < 2 ^ (prefixWord ++ tailWord_1630907).sum := by decide
  have hdescent : baseEnd_1630907 < baseStart_1630907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630924 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_1630924 : Nat := 118140960795 + 1630924 * 2 ^ 59
def prefixEnd_1630924 : Nat := 4983230072969 + 3 ^ 40 * 1630924 * 2
def baseEnd_1630924 : Nat := 279149307651160745349841

theorem tailTrace_1630924 : CollatzResearch.WordTrace tailWord_1630924 prefixEnd_1630924 279149307651160745349841 := by
  unfold tailWord_1630924
  simp only [CollatzResearch.WordTrace]
  refine ⟨29742342571724181244317913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39656456762298908325757217 29742342571724181244317913)
  ·
    refine ⟨22306756928793135933238435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29742342571724181244317913 22306756928793135933238435)
    ·
      refine ⟨33460135393189703899857653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22306756928793135933238435 33460135393189703899857653)
      ·
        refine ⟨3136887693111534740611655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33460135393189703899857653 3136887693111534740611655)
        ·
          refine ⟨4705331539667302110917483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136887693111534740611655 4705331539667302110917483)
          ·
            refine ⟨7057997309500953166376225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705331539667302110917483 7057997309500953166376225)
            ·
              refine ⟨5293497982125714874782169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7057997309500953166376225 5293497982125714874782169)
              ·
                refine ⟨3970123486594286156086627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5293497982125714874782169 3970123486594286156086627)
                ·
                  refine ⟨5955185229891429234129941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970123486594286156086627 5955185229891429234129941)
                  ·
                    refine ⟨279149307651160745349841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5955185229891429234129941 279149307651160745349841)
                    ·
                      rfl

theorem cell23_1630924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_1630924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630924 prefixEnd_1630924 := by exact prefixLift 1630924
  have htrace : WordTrace (prefixWord ++ tailWord_1630924) baseStart_1630924 baseEnd_1630924 := by
    simpa [prefixWord, tailWord_1630924, baseEnd_1630924] using wordTrace_append hprefix tailTrace_1630924
  have hstable : (prefixWord ++ tailWord_1630924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630924).length < 2 ^ (prefixWord ++ tailWord_1630924).sum := by decide
  have hdescent : baseEnd_1630924 < baseStart_1630924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630948 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_1630948 : Nat := 118140960795 + 1630948 * 2 ^ 59
def prefixEnd_1630948 : Nat := 4983230072969 + 3 ^ 40 * 1630948 * 2
def baseEnd_1630948 : Nat := 837460246489190142149413

theorem tailTrace_1630948 : CollatzResearch.WordTrace tailWord_1630948 prefixEnd_1630948 837460246489190142149413 := by
  unfold tailWord_1630948
  simp only [CollatzResearch.WordTrace]
  refine ⟨29742780247680707293754749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39657040330240943058339665 29742780247680707293754749)
  ·
    refine ⟨11153542592880265235158031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29742780247680707293754749 11153542592880265235158031)
    ·
      refine ⟨16730313889320397852737047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11153542592880265235158031 16730313889320397852737047)
      ·
        refine ⟨25095470833980596779105571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16730313889320397852737047 25095470833980596779105571)
        ·
          refine ⟨37643206250970895168658357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25095470833980596779105571 37643206250970895168658357)
          ·
            refine ⟨3529050586028521422061721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37643206250970895168658357 3529050586028521422061721)
            ·
              refine ⟨2646787939521391066546291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529050586028521422061721 2646787939521391066546291)
              ·
                refine ⟨3970181909282086599819437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646787939521391066546291 3970181909282086599819437)
                ·
                  refine ⟨1488818215980782474932289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3970181909282086599819437 1488818215980782474932289)
                  ·
                    refine ⟨1116613661985586856199217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488818215980782474932289 1116613661985586856199217)
                    ·
                      refine ⟨837460246489190142149413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116613661985586856199217 837460246489190142149413)
                      ·
                        rfl

theorem cell23_1630948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_1630948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630948 prefixEnd_1630948 := by exact prefixLift 1630948
  have htrace : WordTrace (prefixWord ++ tailWord_1630948) baseStart_1630948 baseEnd_1630948 := by
    simpa [prefixWord, tailWord_1630948, baseEnd_1630948] using wordTrace_append hprefix tailTrace_1630948
  have hstable : (prefixWord ++ tailWord_1630948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630948).length < 2 ^ (prefixWord ++ tailWord_1630948).sum := by decide
  have hdescent : baseEnd_1630948 < baseStart_1630948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630958 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1630958 : Nat := 118140960795 + 1630958 * 2 ^ 59
def prefixEnd_1630958 : Nat := 4983230072969 + 3 ^ 40 * 1630958 * 2
def baseEnd_1630958 : Nat := 279155127098578367674789

theorem tailTrace_1630958 : CollatzResearch.WordTrace tailWord_1630958 prefixEnd_1630958 279155127098578367674789 := by
  unfold tailWord_1630958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435740653165648286921691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39657283483550124196915685 7435740653165648286921691)
  ·
    refine ⟨11153610979748472430382537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7435740653165648286921691 11153610979748472430382537)
    ·
      refine ⟨8365208234811354322786903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11153610979748472430382537 8365208234811354322786903)
      ·
        refine ⟨12547812352217031484180355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8365208234811354322786903 12547812352217031484180355)
        ·
          refine ⟨18821718528325547226270533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12547812352217031484180355 18821718528325547226270533)
          ·
            refine ⟨3529072224061040104925725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18821718528325547226270533 3529072224061040104925725)
            ·
              refine ⟨1323402084022890039347147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3529072224061040104925725 1323402084022890039347147)
              ·
                refine ⟨1985103126034335059020721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323402084022890039347147 1985103126034335059020721)
                ·
                  refine ⟨1488827344525751294265541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985103126034335059020721 1488827344525751294265541)
                  ·
                    refine ⟨279155127098578367674789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488827344525751294265541 279155127098578367674789)
                    ·
                      rfl

theorem cell23_1630958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1630958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630958 prefixEnd_1630958 := by exact prefixLift 1630958
  have htrace : WordTrace (prefixWord ++ tailWord_1630958) baseStart_1630958 baseEnd_1630958 := by
    simpa [prefixWord, tailWord_1630958, baseEnd_1630958] using wordTrace_append hprefix tailTrace_1630958
  have hstable : (prefixWord ++ tailWord_1630958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630958).length < 2 ^ (prefixWord ++ tailWord_1630958).sum := by decide
  have hdescent : baseEnd_1630958 < baseStart_1630958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630987 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4]
def baseStart_1630987 : Nat := 118140960795 + 1630987 * 2 ^ 59
def prefixEnd_1630987 : Nat := 4983230072969 + 3 ^ 40 * 1630987 * 2
def baseEnd_1630987 : Nat := 837480272234715489561733

theorem tailTrace_1630987 : CollatzResearch.WordTrace tailWord_1630987 prefixEnd_1630987 837480272234715489561733 := by
  unfold tailWord_1630987
  simp only [CollatzResearch.WordTrace]
  refine ⟨59486982942220124248179215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39657988628146749498786143 59486982942220124248179215)
  ·
    refine ⟨89230474413330186372268823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59486982942220124248179215 89230474413330186372268823)
    ·
      refine ⟨133845711619995279558403235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89230474413330186372268823 133845711619995279558403235)
      ·
        refine ⟨200768567429992919337604853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133845711619995279558403235 200768567429992919337604853)
        ·
          refine ⟨18822053196561836187900455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200768567429992919337604853 18822053196561836187900455)
          ·
            refine ⟨28233079794842754281850683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18822053196561836187900455 28233079794842754281850683)
            ·
              refine ⟨42349619692264131422776025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28233079794842754281850683 42349619692264131422776025)
              ·
                refine ⟨31762214769198098567082019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42349619692264131422776025 31762214769198098567082019)
                ·
                  refine ⟨47643322153797147850623029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31762214769198098567082019 47643322153797147850623029)
                  ·
                    refine ⟨4466561451918482610995909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47643322153797147850623029 4466561451918482610995909)
                    ·
                      refine ⟨837480272234715489561733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4466561451918482610995909 837480272234715489561733)
                      ·
                        rfl

theorem cell23_1630987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_1630987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630987 prefixEnd_1630987 := by exact prefixLift 1630987
  have htrace : WordTrace (prefixWord ++ tailWord_1630987) baseStart_1630987 baseEnd_1630987 := by
    simpa [prefixWord, tailWord_1630987, baseEnd_1630987] using wordTrace_append hprefix tailTrace_1630987
  have hstable : (prefixWord ++ tailWord_1630987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630987).length < 2 ^ (prefixWord ++ tailWord_1630987).sum := by decide
  have hdescent : baseEnd_1630987 < baseStart_1630987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630991 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 1, 3, 2]
def baseStart_1630991 : Nat := 118140960795 + 1630991 * 2 ^ 59
def prefixEnd_1630991 : Nat := 4983230072969 + 3 ^ 40 * 1630991 * 2
def baseEnd_1630991 : Nat := 837482326157333473911715

theorem tailTrace_1630991 : CollatzResearch.WordTrace tailWord_1630991 prefixEnd_1630991 837482326157333473911715 := by
  unfold tailWord_1630991
  simp only [CollatzResearch.WordTrace]
  refine ⟨59487128834205632931324827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39658085889470421954216551 59487128834205632931324827)
  ·
    refine ⟨89230693251308449396987241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59487128834205632931324827 89230693251308449396987241)
    ·
      refine ⟨66923019938481337047740431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89230693251308449396987241 66923019938481337047740431)
      ·
        refine ⟨100384529907722005571610647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66923019938481337047740431 100384529907722005571610647)
        ·
          refine ⟨150576794861583008357415971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100384529907722005571610647 150576794861583008357415971)
          ·
            refine ⟨225865192292374512536123957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150576794861583008357415971 225865192292374512536123957)
            ·
              refine ⟨21174861777410110550261621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225865192292374512536123957 21174861777410110550261621)
              ·
                refine ⟨1985143291632197864087027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21174861777410110550261621 1985143291632197864087027)
                ·
                  refine ⟨2977714937448296796130541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985143291632197864087027 2977714937448296796130541)
                  ·
                    refine ⟨1116643101543111298548953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977714937448296796130541 1116643101543111298548953)
                    ·
                      refine ⟨837482326157333473911715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116643101543111298548953 837482326157333473911715)
                      ·
                        rfl

theorem cell23_1630991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 3, 2].length) (baseStart_1630991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1630991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1630991 prefixEnd_1630991 := by exact prefixLift 1630991
  have htrace : WordTrace (prefixWord ++ tailWord_1630991) baseStart_1630991 baseEnd_1630991 := by
    simpa [prefixWord, tailWord_1630991, baseEnd_1630991] using wordTrace_append hprefix tailTrace_1630991
  have hstable : (prefixWord ++ tailWord_1630991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630991).length < 2 ^ (prefixWord ++ tailWord_1630991).sum := by decide
  have hdescent : baseEnd_1630991 < baseStart_1630991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631054 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1631054 : Nat := 118140960795 + 1631054 * 2 ^ 59
def prefixEnd_1631054 : Nat := 4983230072969 + 3 ^ 40 * 1631054 * 2
def baseEnd_1631054 : Nat := 837514675438566727423925

theorem tailTrace_1631054 : CollatzResearch.WordTrace tailWord_1631054 prefixEnd_1631054 837514675438566727423925 := by
  unfold tailWord_1631054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7436178329122174336358527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39659617755318263127245477 7436178329122174336358527)
  ·
    refine ⟨11154267493683261504537791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7436178329122174336358527 11154267493683261504537791)
    ·
      refine ⟨16731401240524892256806687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11154267493683261504537791 16731401240524892256806687)
      ·
        refine ⟨25097101860787338385210031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16731401240524892256806687 25097101860787338385210031)
        ·
          refine ⟨37645652791181007577815047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25097101860787338385210031 37645652791181007577815047)
          ·
            refine ⟨56468479186771511366722571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37645652791181007577815047 56468479186771511366722571)
            ·
              refine ⟨84702718780157267050083857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56468479186771511366722571 84702718780157267050083857)
              ·
                refine ⟨63527039085117950287562893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84702718780157267050083857 63527039085117950287562893)
                ·
                  refine ⟨23822639656919231357836085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63527039085117950287562893 23822639656919231357836085)
                  ·
                    refine ⟨2233372467836177939797133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23822639656919231357836085 2233372467836177939797133)
                    ·
                      refine ⟨837514675438566727423925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2233372467836177939797133 837514675438566727423925)
                      ·
                        rfl

theorem cell23_1631054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1631054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631054 prefixEnd_1631054 := by exact prefixLift 1631054
  have htrace : WordTrace (prefixWord ++ tailWord_1631054) baseStart_1631054 baseEnd_1631054 := by
    simpa [prefixWord, tailWord_1631054, baseEnd_1631054] using wordTrace_append hprefix tailTrace_1631054
  have hstable : (prefixWord ++ tailWord_1631054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631054).length < 2 ^ (prefixWord ++ tailWord_1631054).sum := by decide
  have hdescent : baseEnd_1631054 < baseStart_1631054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631061 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 5]
def baseStart_1631061 : Nat := 118140960795 + 1631061 * 2 ^ 59
def prefixEnd_1631061 : Nat := 4983230072969 + 3 ^ 40 * 1631061 * 2
def baseEnd_1631061 : Nat := 93057585533683133337377

theorem tailTrace_1631061 : CollatzResearch.WordTrace tailWord_1631061 prefixEnd_1631061 93057585533683133337377 := by
  unfold tailWord_1631061
  simp only [CollatzResearch.WordTrace]
  refine ⟨59489681943952034886373037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39659787962634689924248691 59489681943952034886373037)
  ·
    refine ⟨22308630728982013082389889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59489681943952034886373037 22308630728982013082389889)
    ·
      refine ⟨16731473046736509811792417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22308630728982013082389889 16731473046736509811792417)
      ·
        refine ⟨12548604785052382358844313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16731473046736509811792417 12548604785052382358844313)
        ·
          refine ⟨9411453588789286769133235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12548604785052382358844313 9411453588789286769133235)
          ·
            refine ⟨14117180383183930153699853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411453588789286769133235 14117180383183930153699853)
            ·
              refine ⟨5293942643693973807637445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14117180383183930153699853 5293942643693973807637445)
              ·
                refine ⟨992614245692620088932021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5293942643693973807637445 992614245692620088932021)
                ·
                  refine ⟨93057585533683133337377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992614245692620088932021 93057585533683133337377)
                  ·
                    rfl

theorem cell23_1631061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_1631061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631061 prefixEnd_1631061 := by exact prefixLift 1631061
  have htrace : WordTrace (prefixWord ++ tailWord_1631061) baseStart_1631061 baseEnd_1631061 := by
    simpa [prefixWord, tailWord_1631061, baseEnd_1631061] using wordTrace_append hprefix tailTrace_1631061
  have hstable : (prefixWord ++ tailWord_1631061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631061).length < 2 ^ (prefixWord ++ tailWord_1631061).sum := by decide
  have hdescent : baseEnd_1631061 < baseStart_1631061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_1631067 : Nat := 118140960795 + 1631067 * 2 ^ 59
def prefixEnd_1631067 : Nat := 4983230072969 + 3 ^ 40 * 1631067 * 2
def baseEnd_1631067 : Nat := 837521350687075176561365

theorem tailTrace_1631067 : CollatzResearch.WordTrace tailWord_1631067 prefixEnd_1631067 837521350687075176561365 := by
  unfold tailWord_1631067
  simp only [CollatzResearch.WordTrace]
  refine ⟨59489900781930297911091455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39659933854620198607394303 59489900781930297911091455)
  ·
    refine ⟨89234851172895446866637183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59489900781930297911091455 89234851172895446866637183)
    ·
      refine ⟨133852276759343170299955775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89234851172895446866637183 133852276759343170299955775)
      ·
        refine ⟨200778415139014755449933663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133852276759343170299955775 200778415139014755449933663)
        ·
          refine ⟨301167622708522133174900495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200778415139014755449933663 301167622708522133174900495)
          ·
            refine ⟨451751434062783199762350743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301167622708522133174900495 451751434062783199762350743)
            ·
              refine ⟨677627151094174799643526115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451751434062783199762350743 677627151094174799643526115)
              ·
                refine ⟨1016440726641262199465289173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677627151094174799643526115 1016440726641262199465289173)
                ·
                  refine ⟨23822829530654582799967715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1016440726641262199465289173 23822829530654582799967715)
                  ·
                    refine ⟨35734244295981874199951573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23822829530654582799967715 35734244295981874199951573)
                    ·
                      refine ⟨837521350687075176561365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35734244295981874199951573 837521350687075176561365)
                      ·
                        rfl

theorem cell23_1631067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_1631067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631067 prefixEnd_1631067 := by exact prefixLift 1631067
  have htrace : WordTrace (prefixWord ++ tailWord_1631067) baseStart_1631067 baseEnd_1631067 := by
    simpa [prefixWord, tailWord_1631067, baseEnd_1631067] using wordTrace_append hprefix tailTrace_1631067
  have hstable : (prefixWord ++ tailWord_1631067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631067).length < 2 ^ (prefixWord ++ tailWord_1631067).sum := by decide
  have hdescent : baseEnd_1631067 < baseStart_1631067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631106 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1631106 : Nat := 118140960795 + 1631106 * 2 ^ 59
def prefixEnd_1631106 : Nat := 4983230072969 + 3 ^ 40 * 1631106 * 2
def baseEnd_1631106 : Nat := 837541376432600523973687

theorem tailTrace_1631106 : CollatzResearch.WordTrace tailWord_1631106 prefixEnd_1631106 837541376432600523973687 := by
  unfold tailWord_1631106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14872830807197251892940293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39660882152526005047840781 14872830807197251892940293)
  ·
    refine ⟨2788655776349484729926305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14872830807197251892940293 2788655776349484729926305)
    ·
      refine ⟨2091491832262113547444729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2788655776349484729926305 2091491832262113547444729)
      ·
        refine ⟨1568618874196585160583547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2091491832262113547444729 1568618874196585160583547)
        ·
          refine ⟨2352928311294877740875321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568618874196585160583547 2352928311294877740875321)
          ·
            refine ⟨1764696233471158305656491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352928311294877740875321 1764696233471158305656491)
            ·
              refine ⟨2647044350206737458484737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764696233471158305656491 2647044350206737458484737)
              ·
                refine ⟨1985283262655053093863553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647044350206737458484737 1985283262655053093863553)
                ·
                  refine ⟨1488962446991289820397665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985283262655053093863553 1488962446991289820397665)
                  ·
                    refine ⟨1116721835243467365298249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488962446991289820397665 1116721835243467365298249)
                    ·
                      refine ⟨837541376432600523973687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116721835243467365298249 837541376432600523973687)
                      ·
                        rfl

theorem cell23_1631106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1631106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631106 prefixEnd_1631106 := by exact prefixLift 1631106
  have htrace : WordTrace (prefixWord ++ tailWord_1631106) baseStart_1631106 baseEnd_1631106 := by
    simpa [prefixWord, tailWord_1631106, baseEnd_1631106] using wordTrace_append hprefix tailTrace_1631106
  have hstable : (prefixWord ++ tailWord_1631106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631106).length < 2 ^ (prefixWord ++ tailWord_1631106).sum := by decide
  have hdescent : baseEnd_1631106 < baseStart_1631106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631138 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1631138 : Nat := 118140960795 + 1631138 * 2 ^ 59
def prefixEnd_1631138 : Nat := 4983230072969 + 3 ^ 40 * 1631138 * 2
def baseEnd_1631138 : Nat := 279185935937848132924513

theorem tailTrace_1631138 : CollatzResearch.WordTrace tailWord_1631138 prefixEnd_1631138 279185935937848132924513 := by
  unfold tailWord_1631138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14873122591168269259231517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39661660243115384691284045 14873122591168269259231517)
  ·
    refine ⟨5577420971688100972211819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14873122591168269259231517 5577420971688100972211819)
    ·
      refine ⟨8366131457532151458317729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5577420971688100972211819 8366131457532151458317729)
      ·
        refine ⟨6274598593149113593738297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8366131457532151458317729 6274598593149113593738297)
        ·
          refine ⟨4705948944861835195303723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6274598593149113593738297 4705948944861835195303723)
          ·
            refine ⟨7058923417292752792955585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705948944861835195303723 7058923417292752792955585)
            ·
              refine ⟨5294192562969564594716689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7058923417292752792955585 5294192562969564594716689)
              ·
                refine ⟨3970644422227173446037517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5294192562969564594716689 3970644422227173446037517)
                ·
                  refine ⟨1488991658335190042264069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3970644422227173446037517 1488991658335190042264069)
                  ·
                    refine ⟨279185935937848132924513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488991658335190042264069 279185935937848132924513)
                    ·
                      rfl

theorem cell23_1631138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1631138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631138 prefixEnd_1631138 := by exact prefixLift 1631138
  have htrace : WordTrace (prefixWord ++ tailWord_1631138) baseStart_1631138 baseEnd_1631138 := by
    simpa [prefixWord, tailWord_1631138, baseEnd_1631138] using wordTrace_append hprefix tailTrace_1631138
  have hstable : (prefixWord ++ tailWord_1631138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631138).length < 2 ^ (prefixWord ++ tailWord_1631138).sum := by decide
  have hdescent : baseEnd_1631138 < baseStart_1631138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631172 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1631172 : Nat := 118140960795 + 1631172 * 2 ^ 59
def prefixEnd_1631172 : Nat := 4983230072969 + 3 ^ 40 * 1631172 * 2
def baseEnd_1631172 : Nat := 279191755385265755249461

theorem tailTrace_1631172 : CollatzResearch.WordTrace tailWord_1631172 prefixEnd_1631172 279191755385265755249461 := by
  unfold tailWord_1631172
  simp only [CollatzResearch.WordTrace]
  refine ⟨29746865223274950421831885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39662486964366600562442513 29746865223274950421831885)
  ·
    refine ⟨11155074458728106408186957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29746865223274950421831885 11155074458728106408186957)
    ·
      refine ⟨4183152922023039903070109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11155074458728106408186957 4183152922023039903070109)
      ·
        refine ⟨1568682345758639963651291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4183152922023039903070109 1568682345758639963651291)
        ·
          refine ⟨2353023518637959945476937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568682345758639963651291 2353023518637959945476937)
          ·
            refine ⟨1764767638978469959107703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353023518637959945476937 1764767638978469959107703)
            ·
              refine ⟨2647151458467704938661555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764767638978469959107703 2647151458467704938661555)
              ·
                refine ⟨3970727187701557407992333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647151458467704938661555 3970727187701557407992333)
                ·
                  refine ⟨1489022695388084027997125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3970727187701557407992333 1489022695388084027997125)
                  ·
                    refine ⟨279191755385265755249461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1489022695388084027997125 279191755385265755249461)
                    ·
                      rfl

theorem cell23_1631172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1631172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631172 prefixEnd_1631172 := by exact prefixLift 1631172
  have htrace : WordTrace (prefixWord ++ tailWord_1631172) baseStart_1631172 baseEnd_1631172 := by
    simpa [prefixWord, tailWord_1631172, baseEnd_1631172] using wordTrace_append hprefix tailTrace_1631172
  have hstable : (prefixWord ++ tailWord_1631172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631172).length < 2 ^ (prefixWord ++ tailWord_1631172).sum := by decide
  have hdescent : baseEnd_1631172 < baseStart_1631172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631184 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_1631184 : Nat := 118140960795 + 1631184 * 2 ^ 59
def prefixEnd_1631184 : Nat := 4983230072969 + 3 ^ 40 * 1631184 * 2
def baseEnd_1631184 : Nat := 837581427923651218798327

theorem tailTrace_1631184 : CollatzResearch.WordTrace tailWord_1631184 prefixEnd_1631184 837581427923651218798327 := by
  unfold tailWord_1631184
  simp only [CollatzResearch.WordTrace]
  refine ⟨29747084061253213446550303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39662778748337617928733737 29747084061253213446550303)
  ·
    refine ⟨44620626091879820169825455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29747084061253213446550303 44620626091879820169825455)
    ·
      refine ⟨66930939137819730254738183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44620626091879820169825455 66930939137819730254738183)
      ·
        refine ⟨100396408706729595382107275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66930939137819730254738183 100396408706729595382107275)
        ·
          refine ⟨150594613060094393073160913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100396408706729595382107275 150594613060094393073160913)
          ·
            refine ⟨112945959795070794804870685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150594613060094393073160913 112945959795070794804870685)
            ·
              refine ⟨42354734923151548051826507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112945959795070794804870685 42354734923151548051826507)
              ·
                refine ⟨63532102384727322077739761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42354734923151548051826507 63532102384727322077739761)
                ·
                  refine ⟨47649076788545491558304821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63532102384727322077739761 47649076788545491558304821)
                  ·
                    refine ⟨4467100948926139833591077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47649076788545491558304821 4467100948926139833591077)
                    ·
                      refine ⟨837581427923651218798327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4467100948926139833591077 837581427923651218798327)
                      ·
                        rfl

theorem cell23_1631184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_1631184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631184 prefixEnd_1631184 := by exact prefixLift 1631184
  have htrace : WordTrace (prefixWord ++ tailWord_1631184) baseStart_1631184 baseEnd_1631184 := by
    simpa [prefixWord, tailWord_1631184, baseEnd_1631184] using wordTrace_append hprefix tailTrace_1631184
  have hstable : (prefixWord ++ tailWord_1631184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631184).length < 2 ^ (prefixWord ++ tailWord_1631184).sum := by decide
  have hdescent : baseEnd_1631184 < baseStart_1631184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631228 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1631228 : Nat := 118140960795 + 1631228 * 2 ^ 59
def prefixEnd_1631228 : Nat := 4983230072969 + 3 ^ 40 * 1631228 * 2
def baseEnd_1631228 : Nat := 279201340357483015549375

theorem tailTrace_1631228 : CollatzResearch.WordTrace tailWord_1631228 prefixEnd_1631228 279201340357483015549375 := by
  unfold tailWord_1631228
  simp only [CollatzResearch.WordTrace]
  refine ⟨29747886467173511203851169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39663848622898014938468225 29747886467173511203851169)
  ·
    refine ⟨22310914850380133402888377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29747886467173511203851169 22310914850380133402888377)
    ·
      refine ⟨16733186137785100052166283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22310914850380133402888377 16733186137785100052166283)
      ·
        refine ⟨25099779206677650078249425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16733186137785100052166283 25099779206677650078249425)
        ·
          refine ⟨18824834405008237558687069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25099779206677650078249425 18824834405008237558687069)
          ·
            refine ⟨7059312901878089084507651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18824834405008237558687069 7059312901878089084507651)
            ·
              refine ⟨10588969352817133626761477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059312901878089084507651 10588969352817133626761477)
              ·
                refine ⟨1985431753653212555017777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10588969352817133626761477 1985431753653212555017777)
                ·
                  refine ⟨1489073815239909416263333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985431753653212555017777 1489073815239909416263333)
                  ·
                    refine ⟨279201340357483015549375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1489073815239909416263333 279201340357483015549375)
                    ·
                      rfl

theorem cell23_1631228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1631228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631228 prefixEnd_1631228 := by exact prefixLift 1631228
  have htrace : WordTrace (prefixWord ++ tailWord_1631228) baseStart_1631228 baseEnd_1631228 := by
    simpa [prefixWord, tailWord_1631228, baseEnd_1631228] using wordTrace_append hprefix tailTrace_1631228
  have hstable : (prefixWord ++ tailWord_1631228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631228).length < 2 ^ (prefixWord ++ tailWord_1631228).sum := by decide
  have hdescent : baseEnd_1631228 < baseStart_1631228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631301 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_1631301 : Nat := 118140960795 + 1631301 * 2 ^ 59
def prefixEnd_1631301 : Nat := 4983230072969 + 3 ^ 40 * 1631301 * 2
def baseEnd_1631301 : Nat := 279213835053409087011763

theorem tailTrace_1631301 : CollatzResearch.WordTrace tailWord_1631301 prefixEnd_1631301 279213835053409087011763 := by
  unfold tailWord_1631301
  simp only [CollatzResearch.WordTrace]
  refine ⟨59498435463082555875109757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39665623642055037250073171 59498435463082555875109757)
  ·
    refine ⟨22311913298655958453166159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59498435463082555875109757 22311913298655958453166159)
    ·
      refine ⟨33467869947983937679749239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22311913298655958453166159 33467869947983937679749239)
      ·
        refine ⟨50201804921975906519623859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33467869947983937679749239 50201804921975906519623859)
        ·
          refine ⟨75302707382963859779435789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50201804921975906519623859 75302707382963859779435789)
          ·
            refine ⟨28238515268611447417288421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75302707382963859779435789 28238515268611447417288421)
            ·
              refine ⟨5294721612864646390741579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28238515268611447417288421 5294721612864646390741579)
              ·
                refine ⟨7942082419296969586112369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294721612864646390741579 7942082419296969586112369)
                ·
                  refine ⟨5956561814472727189584277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942082419296969586112369 5956561814472727189584277)
                  ·
                    refine ⟨279213835053409087011763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5956561814472727189584277 279213835053409087011763)
                    ·
                      rfl

theorem cell23_1631301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_1631301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631301 prefixEnd_1631301 := by exact prefixLift 1631301
  have htrace : WordTrace (prefixWord ++ tailWord_1631301) baseStart_1631301 baseEnd_1631301 := by
    simpa [prefixWord, tailWord_1631301, baseEnd_1631301] using wordTrace_append hprefix tailTrace_1631301
  have hstable : (prefixWord ++ tailWord_1631301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631301).length < 2 ^ (prefixWord ++ tailWord_1631301).sum := by decide
  have hdescent : baseEnd_1631301 < baseStart_1631301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631302 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1631302 : Nat := 118140960795 + 1631302 * 2 ^ 59
def prefixEnd_1631302 : Nat := 4983230072969 + 3 ^ 40 * 1631302 * 2
def baseEnd_1631302 : Nat := 837642018640881757122785

theorem tailTrace_1631302 : CollatzResearch.WordTrace tailWord_1631302 prefixEnd_1631302 837642018640881757122785 := by
  unfold tailWord_1631302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859327248002466657684255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39665647957385955363930773 1859327248002466657684255)
  ·
    refine ⟨2788990872003699986526383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859327248002466657684255 2788990872003699986526383)
    ·
      refine ⟨4183486308005549979789575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788990872003699986526383 4183486308005549979789575)
      ·
        refine ⟨6275229462008324969684363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183486308005549979789575 6275229462008324969684363)
        ·
          refine ⟨9412844193012487454526545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275229462008324969684363 9412844193012487454526545)
          ·
            refine ⟨7059633144759365590894909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9412844193012487454526545 7059633144759365590894909)
            ·
              refine ⟨2647362429284762096585591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7059633144759365590894909 2647362429284762096585591)
              ·
                refine ⟨3971043643927143144878387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647362429284762096585591 3971043643927143144878387)
                ·
                  refine ⟨5956565465890714717317581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971043643927143144878387 5956565465890714717317581)
                  ·
                    refine ⟨2233712049709018018994093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5956565465890714717317581 2233712049709018018994093)
                    ·
                      refine ⟨837642018640881757122785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2233712049709018018994093 837642018640881757122785)
                      ·
                        rfl

theorem cell23_1631302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1631302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631302 prefixEnd_1631302 := by exact prefixLift 1631302
  have htrace : WordTrace (prefixWord ++ tailWord_1631302) baseStart_1631302 baseEnd_1631302 := by
    simpa [prefixWord, tailWord_1631302, baseEnd_1631302] using wordTrace_append hprefix tailTrace_1631302
  have hstable : (prefixWord ++ tailWord_1631302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631302).length < 2 ^ (prefixWord ++ tailWord_1631302).sum := by decide
  have hdescent : baseEnd_1631302 < baseStart_1631302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631321 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1631321 : Nat := 118140960795 + 1631321 * 2 ^ 59
def prefixEnd_1631321 : Nat := 4983230072969 + 3 ^ 40 * 1631321 * 2
def baseEnd_1631321 : Nat := 837651774773317182785197

theorem tailTrace_1631321 : CollatzResearch.WordTrace tailWord_1631321 prefixEnd_1631321 837651774773317182785197 := by
  unfold tailWord_1631321
  simp only [CollatzResearch.WordTrace]
  refine ⟨59499164923010099290837817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39666109948673399527225211 59499164923010099290837817)
  ·
    refine ⟨44624373692257574468128363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59499164923010099290837817 44624373692257574468128363)
    ·
      refine ⟨66936560538386361702192545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44624373692257574468128363 66936560538386361702192545)
      ·
        refine ⟨50202420403789771276644409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66936560538386361702192545 50202420403789771276644409)
        ·
          refine ⟨37651815302842328457483307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50202420403789771276644409 37651815302842328457483307)
          ·
            refine ⟨56477722954263492686224961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37651815302842328457483307 56477722954263492686224961)
            ·
              refine ⟨42358292215697619514668721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56477722954263492686224961 42358292215697619514668721)
              ·
                refine ⟨31768719161773214636001541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42358292215697619514668721 31768719161773214636001541)
                ·
                  refine ⟨5956634842832477744250289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31768719161773214636001541 5956634842832477744250289)
                  ·
                    refine ⟨4467476132124358308187717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5956634842832477744250289 4467476132124358308187717)
                    ·
                      refine ⟨837651774773317182785197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4467476132124358308187717 837651774773317182785197)
                      ·
                        rfl

theorem cell23_1631321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1631321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631321 prefixEnd_1631321 := by exact prefixLift 1631321
  have htrace : WordTrace (prefixWord ++ tailWord_1631321) baseStart_1631321 baseEnd_1631321 := by
    simpa [prefixWord, tailWord_1631321, baseEnd_1631321] using wordTrace_append hprefix tailTrace_1631321
  have hstable : (prefixWord ++ tailWord_1631321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631321).length < 2 ^ (prefixWord ++ tailWord_1631321).sum := by decide
  have hdescent : baseEnd_1631321 < baseStart_1631321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631342 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1631342 : Nat := 118140960795 + 1631342 * 2 ^ 59
def prefixEnd_1631342 : Nat := 4983230072969 + 3 ^ 40 * 1631342 * 2
def baseEnd_1631342 : Nat := 837662557867061600622601

theorem tailTrace_1631342 : CollatzResearch.WordTrace tailWord_1631342 prefixEnd_1631342 837662557867061600622601 := by
  unfold tailWord_1631342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7437491356991752484669035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39666620570622679918234853 7437491356991752484669035)
  ·
    refine ⟨11156237035487628727003553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7437491356991752484669035 11156237035487628727003553)
    ·
      refine ⟨8367177776615721545252665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11156237035487628727003553 8367177776615721545252665)
      ·
        refine ⟨6275383332461791158939499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8367177776615721545252665 6275383332461791158939499)
        ·
          refine ⟨9413074998692686738409249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275383332461791158939499 9413074998692686738409249)
          ·
            refine ⟨7059806249019515053806937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9413074998692686738409249 7059806249019515053806937)
            ·
              refine ⟨5294854686764636290355203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7059806249019515053806937 5294854686764636290355203)
              ·
                refine ⟨7942282030146954435532805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294854686764636290355203 7942282030146954435532805)
                ·
                  refine ⟨1489177880652553956662401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7942282030146954435532805 1489177880652553956662401)
                  ·
                    refine ⟨1116883410489415467496801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1489177880652553956662401 1116883410489415467496801)
                    ·
                      refine ⟨837662557867061600622601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116883410489415467496801 837662557867061600622601)
                      ·
                        rfl

theorem cell23_1631342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1631342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631342 prefixEnd_1631342 := by exact prefixLift 1631342
  have htrace : WordTrace (prefixWord ++ tailWord_1631342) baseStart_1631342 baseEnd_1631342 := by
    simpa [prefixWord, tailWord_1631342, baseEnd_1631342] using wordTrace_append hprefix tailTrace_1631342
  have hstable : (prefixWord ++ tailWord_1631342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631342).length < 2 ^ (prefixWord ++ tailWord_1631342).sum := by decide
  have hdescent : baseEnd_1631342 < baseStart_1631342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631388 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1631388 : Nat := 118140960795 + 1631388 * 2 ^ 59
def prefixEnd_1631388 : Nat := 4983230072969 + 3 ^ 40 * 1631388 * 2
def baseEnd_1631388 : Nat := 837686177977168420647389

theorem tailTrace_1631388 : CollatzResearch.WordTrace tailWord_1631388 prefixEnd_1631388 837686177977168420647389 := by
  unfold tailWord_1631388
  simp only [CollatzResearch.WordTrace]
  refine ⟨29750804306883684866763409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39667739075844913155684545 29750804306883684866763409)
  ·
    refine ⟨22313103230162763650072557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29750804306883684866763409 22313103230162763650072557)
    ·
      refine ⟨8367413711311036368777209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22313103230162763650072557 8367413711311036368777209)
      ·
        refine ⟨6275560283483277276582907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8367413711311036368777209 6275560283483277276582907)
        ·
          refine ⟨9413340425224915914874361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275560283483277276582907 9413340425224915914874361)
          ·
            refine ⟨7060005318918686936155771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9413340425224915914874361 7060005318918686936155771)
            ·
              refine ⟨10590007978378030404233657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060005318918686936155771 10590007978378030404233657)
              ·
                refine ⟨7942505983783522803175243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10590007978378030404233657 7942505983783522803175243)
                ·
                  refine ⟨11913758975675284204762865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942505983783522803175243 11913758975675284204762865)
                  ·
                    refine ⟨8935319231756463153572149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11913758975675284204762865 8935319231756463153572149)
                    ·
                      refine ⟨837686177977168420647389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8935319231756463153572149 837686177977168420647389)
                      ·
                        rfl

theorem cell23_1631388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1631388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631388 prefixEnd_1631388 := by exact prefixLift 1631388
  have htrace : WordTrace (prefixWord ++ tailWord_1631388) baseStart_1631388 baseEnd_1631388 := by
    simpa [prefixWord, tailWord_1631388, baseEnd_1631388] using wordTrace_append hprefix tailTrace_1631388
  have hstable : (prefixWord ++ tailWord_1631388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631388).length < 2 ^ (prefixWord ++ tailWord_1631388).sum := by decide
  have hdescent : baseEnd_1631388 < baseStart_1631388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631399 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 5]
def baseStart_1631399 : Nat := 118140960795 + 1631399 * 2 ^ 59
def prefixEnd_1631399 : Nat := 4983230072969 + 3 ^ 40 * 1631399 * 2
def baseEnd_1631399 : Nat := 93076869584929764178871

theorem tailTrace_1631399 : CollatzResearch.WordTrace tailWord_1631399 prefixEnd_1631399 93076869584929764178871 := by
  unfold tailWord_1631399
  simp only [CollatzResearch.WordTrace]
  refine ⟨59502009816727518612177251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39668006544485012408118167 59502009816727518612177251)
  ·
    refine ⟨89253014725091277918265877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59502009816727518612177251 89253014725091277918265877)
    ·
      refine ⟨4183735065238653652418713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89253014725091277918265877 4183735065238653652418713)
      ·
        refine ⟨3137801298928990239314035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4183735065238653652418713 3137801298928990239314035)
        ·
          refine ⟨4706701948393485358971053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137801298928990239314035 4706701948393485358971053)
          ·
            refine ⟨1765013230647557009614145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4706701948393485358971053 1765013230647557009614145)
            ·
              refine ⟨1323759922985667757210609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765013230647557009614145 1323759922985667757210609)
              ·
                refine ⟨992819942239250817907957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323759922985667757210609 992819942239250817907957)
                ·
                  refine ⟨93076869584929764178871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992819942239250817907957 93076869584929764178871)
                  ·
                    rfl

theorem cell23_1631399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 5].length) (baseStart_1631399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631399 prefixEnd_1631399 := by exact prefixLift 1631399
  have htrace : WordTrace (prefixWord ++ tailWord_1631399) baseStart_1631399 baseEnd_1631399 := by
    simpa [prefixWord, tailWord_1631399, baseEnd_1631399] using wordTrace_append hprefix tailTrace_1631399
  have hstable : (prefixWord ++ tailWord_1631399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631399).length < 2 ^ (prefixWord ++ tailWord_1631399).sum := by decide
  have hdescent : baseEnd_1631399 < baseStart_1631399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631402 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1631402 : Nat := 118140960795 + 1631402 * 2 ^ 59
def prefixEnd_1631402 : Nat := 4983230072969 + 3 ^ 40 * 1631402 * 2
def baseEnd_1631402 : Nat := 837693366706331365872325

theorem tailTrace_1631402 : CollatzResearch.WordTrace tailWord_1631402 prefixEnd_1631402 837693366706331365872325 := by
  unfold tailWord_1631402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875529808929162531134115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39668079490477766749690973 14875529808929162531134115)
  ·
    refine ⟨22313294713393743796701173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14875529808929162531134115 22313294713393743796701173)
    ·
      refine ⟨2091871379380663480940735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22313294713393743796701173 2091871379380663480940735)
      ·
        refine ⟨3137807069070995221411103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091871379380663480940735 3137807069070995221411103)
        ·
          refine ⟨4706710603606492832116655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137807069070995221411103 4706710603606492832116655)
          ·
            refine ⟨7060065905409739248174983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706710603606492832116655 7060065905409739248174983)
            ·
              refine ⟨10590098858114608872262475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060065905409739248174983 10590098858114608872262475)
              ·
                refine ⟨15885148287171913308393713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10590098858114608872262475 15885148287171913308393713)
                ·
                  refine ⟨11913861215378934981295285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15885148287171913308393713 11913861215378934981295285)
                  ·
                    refine ⟨1116924488941775154496433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11913861215378934981295285 1116924488941775154496433)
                    ·
                      refine ⟨837693366706331365872325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116924488941775154496433 837693366706331365872325)
                      ·
                        rfl

theorem cell23_1631402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1631402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631402 prefixEnd_1631402 := by exact prefixLift 1631402
  have htrace : WordTrace (prefixWord ++ tailWord_1631402) baseStart_1631402 baseEnd_1631402 := by
    simpa [prefixWord, tailWord_1631402, baseEnd_1631402] using wordTrace_append hprefix tailTrace_1631402
  have hstable : (prefixWord ++ tailWord_1631402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631402).length < 2 ^ (prefixWord ++ tailWord_1631402).sum := by decide
  have hdescent : baseEnd_1631402 < baseStart_1631402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631415 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 2, 4, 2]
def baseStart_1631415 : Nat := 118140960795 + 1631415 * 2 ^ 59
def prefixEnd_1631415 : Nat := 4983230072969 + 3 ^ 40 * 1631415 * 2
def baseEnd_1631415 : Nat := 837700041954839815009765

theorem tailTrace_1631415 : CollatzResearch.WordTrace tailWord_1631415 prefixEnd_1631415 837700041954839815009765 := by
  unfold tailWord_1631415
  simp only [CollatzResearch.WordTrace]
  refine ⟨59502593384669553344759699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39668395589779702229839799 59502593384669553344759699)
  ·
    refine ⟨89253890077004330017139549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59502593384669553344759699 89253890077004330017139549)
    ·
      refine ⟨33470208778876623756427331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89253890077004330017139549 33470208778876623756427331)
      ·
        refine ⟨50205313168314935634640997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33470208778876623756427331 50205313168314935634640997)
        ·
          refine ⟨9413496219059050431495187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50205313168314935634640997 9413496219059050431495187)
          ·
            refine ⟨14120244328588575647242781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413496219059050431495187 14120244328588575647242781)
            ·
              refine ⟨5295091623220715867716043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14120244328588575647242781 5295091623220715867716043)
              ·
                refine ⟨7942637434831073801574065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295091623220715867716043 7942637434831073801574065)
                ·
                  refine ⟨5956978076123305351180549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942637434831073801574065 5956978076123305351180549)
                  ·
                    refine ⟨1116933389273119753346353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5956978076123305351180549 1116933389273119753346353)
                    ·
                      refine ⟨837700041954839815009765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116933389273119753346353 837700041954839815009765)
                      ·
                        rfl

theorem cell23_1631415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_1631415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631415 prefixEnd_1631415 := by exact prefixLift 1631415
  have htrace : WordTrace (prefixWord ++ tailWord_1631415) baseStart_1631415 baseEnd_1631415 := by
    simpa [prefixWord, tailWord_1631415, baseEnd_1631415] using wordTrace_append hprefix tailTrace_1631415
  have hstable : (prefixWord ++ tailWord_1631415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631415).length < 2 ^ (prefixWord ++ tailWord_1631415).sum := by decide
  have hdescent : baseEnd_1631415 < baseStart_1631415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631418 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_1631418 : Nat := 118140960795 + 1631418 * 2 ^ 59
def prefixEnd_1631418 : Nat := 4983230072969 + 3 ^ 40 * 1631418 * 2
def baseEnd_1631418 : Nat := 837701582396803303272251

theorem tailTrace_1631418 : CollatzResearch.WordTrace tailWord_1631418 prefixEnd_1631418 837701582396803303272251 := by
  unfold tailWord_1631418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875675700914671214279727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39668468535772456571412605 14875675700914671214279727)
  ·
    refine ⟨22313513551372006821419591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14875675700914671214279727 22313513551372006821419591)
    ·
      refine ⟨33470270327058010232129387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22313513551372006821419591 33470270327058010232129387)
      ·
        refine ⟨50205405490587015348194081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33470270327058010232129387 50205405490587015348194081)
        ·
          refine ⟨37654054117940261511145561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50205405490587015348194081 37654054117940261511145561)
          ·
            refine ⟨28240540588455196133359171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37654054117940261511145561 28240540588455196133359171)
            ·
              refine ⟨42360810882682794200038757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28240540588455196133359171 42360810882682794200038757)
              ·
                refine ⟨7942652040503023912507267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42360810882682794200038757 7942652040503023912507267)
                ·
                  refine ⟨11913978060754535868760901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942652040503023912507267 11913978060754535868760901)
                  ·
                    refine ⟨2233870886391475475392669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11913978060754535868760901 2233870886391475475392669)
                    ·
                      refine ⟨837701582396803303272251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2233870886391475475392669 837701582396803303272251)
                      ·
                        rfl

theorem cell23_1631418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_1631418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631418 prefixEnd_1631418 := by exact prefixLift 1631418
  have htrace : WordTrace (prefixWord ++ tailWord_1631418) baseStart_1631418 baseEnd_1631418 := by
    simpa [prefixWord, tailWord_1631418, baseEnd_1631418] using wordTrace_append hprefix tailTrace_1631418
  have hstable : (prefixWord ++ tailWord_1631418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631418).length < 2 ^ (prefixWord ++ tailWord_1631418).sum := by decide
  have hdescent : baseEnd_1631418 < baseStart_1631418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631451 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 11]
def baseStart_1631451 : Nat := 118140960795 + 1631451 * 2 ^ 59
def prefixEnd_1631451 : Nat := 4983230072969 + 3 ^ 40 * 1631451 * 2
def baseEnd_1631451 : Nat := 279239509086133891386533

theorem tailTrace_1631451 : CollatzResearch.WordTrace tailWord_1631451 prefixEnd_1631451 279239509086133891386533 := by
  unfold tailWord_1631451
  simp only [CollatzResearch.WordTrace]
  refine ⟨59503906412539131493070207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39669270941692754328713471 59503906412539131493070207)
  ·
    refine ⟨89255859618808697239605311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59503906412539131493070207 89255859618808697239605311)
    ·
      refine ⟨133883789428213045859407967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89255859618808697239605311 133883789428213045859407967)
      ·
        refine ⟨200825684142319568789111951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133883789428213045859407967 200825684142319568789111951)
        ·
          refine ⟨301238526213479353183667927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200825684142319568789111951 301238526213479353183667927)
          ·
            refine ⟨451857789320219029775501891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301238526213479353183667927 451857789320219029775501891)
            ·
              refine ⟨677786683980328544663252837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451857789320219029775501891 677786683980328544663252837)
              ·
                refine ⟨127085003246311602124359907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677786683980328544663252837 127085003246311602124359907)
                ·
                  refine ⟨190627504869467403186539861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127085003246311602124359907 190627504869467403186539861)
                  ·
                    refine ⟨279239509086133891386533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 190627504869467403186539861 279239509086133891386533)
                    ·
                      rfl

theorem cell23_1631451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_1631451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631451 prefixEnd_1631451 := by exact prefixLift 1631451
  have htrace : WordTrace (prefixWord ++ tailWord_1631451) baseStart_1631451 baseEnd_1631451 := by
    simpa [prefixWord, tailWord_1631451, baseEnd_1631451] using wordTrace_append hprefix tailTrace_1631451
  have hstable : (prefixWord ++ tailWord_1631451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631451).length < 2 ^ (prefixWord ++ tailWord_1631451).sum := by decide
  have hdescent : baseEnd_1631451 < baseStart_1631451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631475 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 1, 5, 2]
def baseStart_1631475 : Nat := 118140960795 + 1631475 * 2 ^ 59
def prefixEnd_1631475 : Nat := 4983230072969 + 3 ^ 40 * 1631475 * 2
def baseEnd_1631475 : Nat := 837730850794109580259489

theorem tailTrace_1631475 : CollatzResearch.WordTrace tailWord_1631475 prefixEnd_1631475 837730850794109580259489 := by
  unfold tailWord_1631475
  simp only [CollatzResearch.WordTrace]
  refine ⟨59504781764452183591943879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39669854509634789061295919 59504781764452183591943879)
  ·
    refine ⟨89257172646678275387915819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59504781764452183591943879 89257172646678275387915819)
    ·
      refine ⟨133885758970017413081873729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89257172646678275387915819 133885758970017413081873729)
      ·
        refine ⟨100414319227513059811405297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133885758970017413081873729 100414319227513059811405297)
        ·
          refine ⟨75310739420634794858553973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100414319227513059811405297 75310739420634794858553973)
          ·
            refine ⟨7060381820684512017989435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75310739420634794858553973 7060381820684512017989435)
            ·
              refine ⟨10590572731026768026984153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060381820684512017989435 10590572731026768026984153)
              ·
                refine ⟨7942929548270076020238115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10590572731026768026984153 7942929548270076020238115)
                ·
                  refine ⟨11914394322405114030357173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942929548270076020238115 11914394322405114030357173)
                  ·
                    refine ⟨1116974467725479440345985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11914394322405114030357173 1116974467725479440345985)
                    ·
                      refine ⟨837730850794109580259489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116974467725479440345985 837730850794109580259489)
                      ·
                        rfl

theorem cell23_1631475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5, 2].length) (baseStart_1631475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631475 prefixEnd_1631475 := by exact prefixLift 1631475
  have htrace : WordTrace (prefixWord ++ tailWord_1631475) baseStart_1631475 baseEnd_1631475 := by
    simpa [prefixWord, tailWord_1631475, baseEnd_1631475] using wordTrace_append hprefix tailTrace_1631475
  have hstable : (prefixWord ++ tailWord_1631475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631475).length < 2 ^ (prefixWord ++ tailWord_1631475).sum := by decide
  have hdescent : baseEnd_1631475 < baseStart_1631475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631492 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1631492 : Nat := 118140960795 + 1631492 * 2 ^ 59
def prefixEnd_1631492 : Nat := 4983230072969 + 3 ^ 40 * 1631492 * 2
def baseEnd_1631492 : Nat := 837739579965236013746911

theorem tailTrace_1631492 : CollatzResearch.WordTrace tailWord_1631492 prefixEnd_1631492 837739579965236013746911 := by
  unfold tailWord_1631492
  simp only [CollatzResearch.WordTrace]
  refine ⟨29752700902695297747656365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39670267870260396996875153 29752700902695297747656365)
  ·
    refine ⟨11157262838510736655371137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29752700902695297747656365 11157262838510736655371137)
    ·
      refine ⟨8367947128883052491528353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11157262838510736655371137 8367947128883052491528353)
      ·
        refine ⟨6275960346662289368646265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8367947128883052491528353 6275960346662289368646265)
        ·
          refine ⟨4706970259996717026484699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6275960346662289368646265 4706970259996717026484699)
          ·
            refine ⟨7060455389995075539727049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706970259996717026484699 7060455389995075539727049)
            ·
              refine ⟨5295341542496306654795287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060455389995075539727049 5295341542496306654795287)
              ·
                refine ⟨7943012313744459982192931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295341542496306654795287 7943012313744459982192931)
                ·
                  refine ⟨11914518470616689973289397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943012313744459982192931 11914518470616689973289397)
                  ·
                    refine ⟨1116986106620314684995881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11914518470616689973289397 1116986106620314684995881)
                    ·
                      refine ⟨837739579965236013746911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1116986106620314684995881 837739579965236013746911)
                      ·
                        rfl

theorem cell23_1631492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1631492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631492 prefixEnd_1631492 := by exact prefixLift 1631492
  have htrace : WordTrace (prefixWord ++ tailWord_1631492) baseStart_1631492 baseEnd_1631492 := by
    simpa [prefixWord, tailWord_1631492, baseEnd_1631492] using wordTrace_append hprefix tailTrace_1631492
  have hstable : (prefixWord ++ tailWord_1631492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631492).length < 2 ^ (prefixWord ++ tailWord_1631492).sum := by decide
  have hdescent : baseEnd_1631492 < baseStart_1631492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631498 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1631498 : Nat := 118140960795 + 1631498 * 2 ^ 59
def prefixEnd_1631498 : Nat := 4983230072969 + 3 ^ 40 * 1631498 * 2
def baseEnd_1631498 : Nat := 279247553616387663423961

theorem tailTrace_1631498 : CollatzResearch.WordTrace tailWord_1631498 prefixEnd_1631498 279247553616387663423961 := by
  unfold tailWord_1631498
  simp only [CollatzResearch.WordTrace]
  refine ⟨14876405160842214630007787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39670413762245905680020765 14876405160842214630007787)
  ·
    refine ⟨22314607741263321945011681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14876405160842214630007787 22314607741263321945011681)
    ·
      refine ⟨16735955805947491458758761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22314607741263321945011681 16735955805947491458758761)
      ·
        refine ⟨12551966854460618594069071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16735955805947491458758761 12551966854460618594069071)
        ·
          refine ⟨18827950281690927891103607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12551966854460618594069071 18827950281690927891103607)
          ·
            refine ⟨28241925422536391836655411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18827950281690927891103607 28241925422536391836655411)
            ·
              refine ⟨42362888133804587754983117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28241925422536391836655411 42362888133804587754983117)
              ·
                refine ⟨15886083050176720408118669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42362888133804587754983117 15886083050176720408118669)
                ·
                  refine ⟨5957281143816270153044501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15886083050176720408118669 5957281143816270153044501)
                  ·
                    refine ⟨279247553616387663423961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5957281143816270153044501 279247553616387663423961)
                    ·
                      rfl

theorem cell23_1631498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1631498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631498 prefixEnd_1631498 := by exact prefixLift 1631498
  have htrace : WordTrace (prefixWord ++ tailWord_1631498) baseStart_1631498 baseEnd_1631498 := by
    simpa [prefixWord, tailWord_1631498, baseEnd_1631498] using wordTrace_append hprefix tailTrace_1631498
  have hstable : (prefixWord ++ tailWord_1631498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631498).length < 2 ^ (prefixWord ++ tailWord_1631498).sum := by decide
  have hdescent : baseEnd_1631498 < baseStart_1631498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631499 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 1, 1, 3]
def baseStart_1631499 : Nat := 118140960795 + 1631499 * 2 ^ 59
def prefixEnd_1631499 : Nat := 4983230072969 + 3 ^ 40 * 1631499 * 2
def baseEnd_1631499 : Nat := 837743174329817486359379

theorem tailTrace_1631499 : CollatzResearch.WordTrace tailWord_1631499 prefixEnd_1631499 837743174329817486359379 := by
  unfold tailWord_1631499
  simp only [CollatzResearch.WordTrace]
  refine ⟨59505657116365235690817551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39670438077576823793878367 59505657116365235690817551)
  ·
    refine ⟨89258485674547853536226327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59505657116365235690817551 89258485674547853536226327)
    ·
      refine ⟨133887728511821780304339491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89258485674547853536226327 133887728511821780304339491)
      ·
        refine ⟨200831592767732670456509237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133887728511821780304339491 200831592767732670456509237)
        ·
          refine ⟨18827961821974937855297741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200831592767732670456509237 18827961821974937855297741)
          ·
            refine ⟨7060485683240601695736653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18827961821974937855297741 7060485683240601695736653)
            ·
              refine ⟨2647682131215225635901245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7060485683240601695736653 2647682131215225635901245)
              ·
                refine ⟨992880799205709613462967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2647682131215225635901245 992880799205709613462967)
                ·
                  refine ⟨1489321198808564420194451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992880799205709613462967 1489321198808564420194451)
                  ·
                    refine ⟨2233981798212846630291677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1489321198808564420194451 2233981798212846630291677)
                    ·
                      refine ⟨837743174329817486359379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2233981798212846630291677 837743174329817486359379)
                      ·
                        rfl

theorem cell23_1631499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 1, 3].length) (baseStart_1631499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631499 prefixEnd_1631499 := by exact prefixLift 1631499
  have htrace : WordTrace (prefixWord ++ tailWord_1631499) baseStart_1631499 baseEnd_1631499 := by
    simpa [prefixWord, tailWord_1631499, baseEnd_1631499] using wordTrace_append hprefix tailTrace_1631499
  have hstable : (prefixWord ++ tailWord_1631499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631499).length < 2 ^ (prefixWord ++ tailWord_1631499).sum := by decide
  have hdescent : baseEnd_1631499 < baseStart_1631499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631505 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_1631505 : Nat := 118140960795 + 1631505 * 2 ^ 59
def prefixEnd_1631505 : Nat := 4983230072969 + 3 ^ 40 * 1631505 * 2
def baseEnd_1631505 : Nat := 837746255213744462884351

theorem tailTrace_1631505 : CollatzResearch.WordTrace tailWord_1631505 prefixEnd_1631505 837746255213744462884351 := by
  unfold tailWord_1631505
  simp only [CollatzResearch.WordTrace]
  refine ⟨59505875954343498715535969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39670583969562332477023979 59505875954343498715535969)
  ·
    refine ⟨44629406965757624036651977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59505875954343498715535969 44629406965757624036651977)
    ·
      refine ⟨33472055224318218027488983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44629406965757624036651977 33472055224318218027488983)
      ·
        refine ⟨50208082836477327041233475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33472055224318218027488983 50208082836477327041233475)
        ·
          refine ⟨75312124254715990561850213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50208082836477327041233475 75312124254715990561850213)
          ·
            refine ⟨14121023297759248230346915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75312124254715990561850213 14121023297759248230346915)
            ·
              refine ⟨21181534946638872345520373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14121023297759248230346915 21181534946638872345520373)
              ·
                refine ⟨1985768901247394282392535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21181534946638872345520373 1985768901247394282392535)
                ·
                  refine ⟨2978653351871091423588803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985768901247394282392535 2978653351871091423588803)
                  ·
                    refine ⟨4467980027806637135383205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2978653351871091423588803 4467980027806637135383205)
                    ·
                      refine ⟨837746255213744462884351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4467980027806637135383205 837746255213744462884351)
                      ·
                        rfl

theorem cell23_1631505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_1631505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631505 prefixEnd_1631505 := by exact prefixLift 1631505
  have htrace : WordTrace (prefixWord ++ tailWord_1631505) baseStart_1631505 baseEnd_1631505 := by
    simpa [prefixWord, tailWord_1631505, baseEnd_1631505] using wordTrace_append hprefix tailTrace_1631505
  have hstable : (prefixWord ++ tailWord_1631505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631505).length < 2 ^ (prefixWord ++ tailWord_1631505).sum := by decide
  have hdescent : baseEnd_1631505 < baseStart_1631505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631515 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 2, 4]
def baseStart_1631515 : Nat := 118140960795 + 1631515 * 2 ^ 59
def prefixEnd_1631515 : Nat := 4983230072969 + 3 ^ 40 * 1631515 * 2
def baseEnd_1631515 : Nat := 279250463340096474586435

theorem tailTrace_1631515 : CollatzResearch.WordTrace tailWord_1631515 prefixEnd_1631515 279250463340096474586435 := by
  unfold tailWord_1631515
  simp only [CollatzResearch.WordTrace]
  refine ⟨59506240684307270423399999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39670827122871513615599999 59506240684307270423399999)
  ·
    refine ⟨89259361026460905635099999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59506240684307270423399999 89259361026460905635099999)
    ·
      refine ⟨133889041539691358452649999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89259361026460905635099999 133889041539691358452649999)
      ·
        refine ⟨200833562309537037678974999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133889041539691358452649999 200833562309537037678974999)
        ·
          refine ⟨301250343464305556518462499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200833562309537037678974999 301250343464305556518462499)
          ·
            refine ⟨451875515196458334777693749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301250343464305556518462499 451875515196458334777693749)
            ·
              refine ⟨42363329549667968885408789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451875515196458334777693749 42363329549667968885408789)
              ·
                refine ⟨1985781072640686041503537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42363329549667968885408789 1985781072640686041503537)
                ·
                  refine ⟨1489335804480514531127653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985781072640686041503537 1489335804480514531127653)
                  ·
                    refine ⟨279250463340096474586435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1489335804480514531127653 279250463340096474586435)
                    ·
                      rfl

theorem cell23_1631515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 4].length) (baseStart_1631515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631515 prefixEnd_1631515 := by exact prefixLift 1631515
  have htrace : WordTrace (prefixWord ++ tailWord_1631515) baseStart_1631515 baseEnd_1631515 := by
    simpa [prefixWord, tailWord_1631515, baseEnd_1631515] using wordTrace_append hprefix tailTrace_1631515
  have hstable : (prefixWord ++ tailWord_1631515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631515).length < 2 ^ (prefixWord ++ tailWord_1631515).sum := by decide
  have hdescent : baseEnd_1631515 < baseStart_1631515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631525 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_1631525 : Nat := 118140960795 + 1631525 * 2 ^ 59
def prefixEnd_1631525 : Nat := 4983230072969 + 3 ^ 40 * 1631525 * 2
def baseEnd_1631525 : Nat := 837756524826834384634259

theorem tailTrace_1631525 : CollatzResearch.WordTrace tailWord_1631525 prefixEnd_1631525 837756524826834384634259 := by
  unfold tailWord_1631525
  simp only [CollatzResearch.WordTrace]
  refine ⟨59506605414271042131264029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39671070276180694754176019 59506605414271042131264029)
  ·
    refine ⟨22314977030351640799224011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59506605414271042131264029 22314977030351640799224011)
    ·
      refine ⟨33472465545527461198836017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22314977030351640799224011 33472465545527461198836017)
      ·
        refine ⟨25104349159145595899127013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33472465545527461198836017 25104349159145595899127013)
        ·
          refine ⟨4707065467339799231086315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25104349159145595899127013 4707065467339799231086315)
          ·
            refine ⟨7060598201009698846629473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707065467339799231086315 7060598201009698846629473)
            ·
              refine ⟨5295448650757274134972105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060598201009698846629473 5295448650757274134972105)
              ·
                refine ⟨3971586488067955601229079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5295448650757274134972105 3971586488067955601229079)
                ·
                  refine ⟨5957379732101933401843619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971586488067955601229079 5957379732101933401843619)
                  ·
                    refine ⟨8936069598152900102765429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957379732101933401843619 8936069598152900102765429)
                    ·
                      refine ⟨837756524826834384634259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8936069598152900102765429 837756524826834384634259)
                      ·
                        rfl

theorem cell23_1631525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_1631525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631525 prefixEnd_1631525 := by exact prefixLift 1631525
  have htrace : WordTrace (prefixWord ++ tailWord_1631525) baseStart_1631525 baseEnd_1631525 := by
    simpa [prefixWord, tailWord_1631525, baseEnd_1631525] using wordTrace_append hprefix tailTrace_1631525
  have hstable : (prefixWord ++ tailWord_1631525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631525).length < 2 ^ (prefixWord ++ tailWord_1631525).sum := by decide
  have hdescent : baseEnd_1631525 < baseStart_1631525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631556 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1631556 : Nat := 118140960795 + 1631556 * 2 ^ 59
def prefixEnd_1631556 : Nat := 4983230072969 + 3 ^ 40 * 1631556 * 2
def baseEnd_1631556 : Nat := 837772442727123763346617

theorem tailTrace_1631556 : CollatzResearch.WordTrace tailWord_1631556 prefixEnd_1631556 837772442727123763346617 := by
  unfold tailWord_1631556
  simp only [CollatzResearch.WordTrace]
  refine ⟨29753868038579367212821261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39671824051439156283761681 29753868038579367212821261)
  ·
    refine ⟨11157700514467262704807973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29753868038579367212821261 11157700514467262704807973)
    ·
      refine ⟨2092068846462611757151495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11157700514467262704807973 2092068846462611757151495)
      ·
        refine ⟨3138103269693917635727243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092068846462611757151495 3138103269693917635727243)
        ·
          refine ⟨4707154904540876453590865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138103269693917635727243 4707154904540876453590865)
          ·
            refine ⟨3530366178405657340193149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4707154904540876453590865 3530366178405657340193149)
            ·
              refine ⟨1323887316902121502572431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3530366178405657340193149 1323887316902121502572431)
              ·
                refine ⟨1985830975353182253858647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323887316902121502572431 1985830975353182253858647)
                ·
                  refine ⟨2978746463029773380787971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985830975353182253858647 2978746463029773380787971)
                  ·
                    refine ⟨4468119694544660071181957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2978746463029773380787971 4468119694544660071181957)
                    ·
                      refine ⟨837772442727123763346617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4468119694544660071181957 837772442727123763346617)
                      ·
                        rfl

theorem cell23_1631556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1631556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631556 prefixEnd_1631556 := by exact prefixLift 1631556
  have htrace : WordTrace (prefixWord ++ tailWord_1631556) baseStart_1631556 baseEnd_1631556 := by
    simpa [prefixWord, tailWord_1631556, baseEnd_1631556] using wordTrace_append hprefix tailTrace_1631556
  have hstable : (prefixWord ++ tailWord_1631556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631556).length < 2 ^ (prefixWord ++ tailWord_1631556).sum := by decide
  have hdescent : baseEnd_1631556 < baseStart_1631556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631559 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_1631559 : Nat := 118140960795 + 1631559 * 2 ^ 59
def prefixEnd_1631559 : Nat := 4983230072969 + 3 ^ 40 * 1631559 * 2
def baseEnd_1631559 : Nat := 837773983169087251609103

theorem tailTrace_1631559 : CollatzResearch.WordTrace tailWord_1631559 prefixEnd_1631559 837773983169087251609103 := by
  unfold tailWord_1631559
  simp only [CollatzResearch.WordTrace]
  refine ⟨59507845496147865938001731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39671896997431910625334487 59507845496147865938001731)
  ·
    refine ⟨89261768244221798907002597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59507845496147865938001731 89261768244221798907002597)
    ·
      refine ⟨16736581545791587295062987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89261768244221798907002597 16736581545791587295062987)
      ·
        refine ⟨25104872318687380942594481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16736581545791587295062987 25104872318687380942594481)
        ·
          refine ⟨18828654239015535706945861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25104872318687380942594481 18828654239015535706945861)
          ·
            refine ⟨3530372669815412945052349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18828654239015535706945861 3530372669815412945052349)
            ·
              refine ⟨1323889751180779854394631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3530372669815412945052349 1323889751180779854394631)
              ·
                refine ⟨1985834626771169781591947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323889751180779854394631 1985834626771169781591947)
                ·
                  refine ⟨2978751940156754672387921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985834626771169781591947 2978751940156754672387921)
                  ·
                    refine ⟨2234063955117566004290941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2978751940156754672387921 2234063955117566004290941)
                    ·
                      refine ⟨837773983169087251609103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2234063955117566004290941 837773983169087251609103)
                      ·
                        rfl

theorem cell23_1631559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_1631559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631559 prefixEnd_1631559 := by exact prefixLift 1631559
  have htrace : WordTrace (prefixWord ++ tailWord_1631559) baseStart_1631559 baseEnd_1631559 := by
    simpa [prefixWord, tailWord_1631559, baseEnd_1631559] using wordTrace_append hprefix tailTrace_1631559
  have hstable : (prefixWord ++ tailWord_1631559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631559).length < 2 ^ (prefixWord ++ tailWord_1631559).sum := by decide
  have hdescent : baseEnd_1631559 < baseStart_1631559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631573 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_1631573 : Nat := 118140960795 + 1631573 * 2 ^ 59
def prefixEnd_1631573 : Nat := 4983230072969 + 3 ^ 40 * 1631573 * 2
def baseEnd_1631573 : Nat := 837781171898250196834039

theorem tailTrace_1631573 : CollatzResearch.WordTrace tailWord_1631573 prefixEnd_1631573 837781171898250196834039 := by
  unfold tailWord_1631573
  simp only [CollatzResearch.WordTrace]
  refine ⟨59508356118097146329011373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39672237412064764219340915 59508356118097146329011373)
  ·
    refine ⟨22315633544286429873379265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59508356118097146329011373 22315633544286429873379265)
    ·
      refine ⟨16736725158214822405034449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22315633544286429873379265 16736725158214822405034449)
      ·
        refine ⟨12552543868661116803775837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16736725158214822405034449 12552543868661116803775837)
        ·
          refine ⟨4707203950747918801415939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12552543868661116803775837 4707203950747918801415939)
          ·
            refine ⟨7060805926121878202123909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707203950747918801415939 7060805926121878202123909)
            ·
              refine ⟨1323901111147852162898233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7060805926121878202123909 1323901111147852162898233)
              ·
                refine ⟨992925833360889122173675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323901111147852162898233 992925833360889122173675)
                ·
                  refine ⟨1489388750041333683260513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992925833360889122173675 1489388750041333683260513)
                  ·
                    refine ⟨1117041562531000262445385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1489388750041333683260513 1117041562531000262445385)
                    ·
                      refine ⟨837781171898250196834039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117041562531000262445385 837781171898250196834039)
                      ·
                        rfl

theorem cell23_1631573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_1631573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631573 prefixEnd_1631573 := by exact prefixLift 1631573
  have htrace : WordTrace (prefixWord ++ tailWord_1631573) baseStart_1631573 baseEnd_1631573 := by
    simpa [prefixWord, tailWord_1631573, baseEnd_1631573] using wordTrace_append hprefix tailTrace_1631573
  have hstable : (prefixWord ++ tailWord_1631573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631573).length < 2 ^ (prefixWord ++ tailWord_1631573).sum := by decide
  have hdescent : baseEnd_1631573 < baseStart_1631573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631612 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_1631612 : Nat := 118140960795 + 1631612 * 2 ^ 59
def prefixEnd_1631612 : Nat := 4983230072969 + 3 ^ 40 * 1631612 * 2
def baseEnd_1631612 : Nat := 837801197643775544246359

theorem tailTrace_1631612 : CollatzResearch.WordTrace tailWord_1631612 prefixEnd_1631612 837801197643775544246359 := by
  unfold tailWord_1631612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754889282477927994840545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39673185709970570659787393 29754889282477927994840545)
  ·
    refine ⟨22316166961858445996130409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29754889282477927994840545 22316166961858445996130409)
    ·
      refine ⟨16737125221393834497097807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22316166961858445996130409 16737125221393834497097807)
      ·
        refine ⟨25105687832090751745646711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16737125221393834497097807 25105687832090751745646711)
        ·
          refine ⟨37658531748136127618470067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25105687832090751745646711 37658531748136127618470067)
          ·
            refine ⟨56487797622204191427705101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37658531748136127618470067 56487797622204191427705101)
            ·
              refine ⟨21182924108326571785389413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56487797622204191427705101 21182924108326571785389413)
              ·
                refine ⟨3971798270311232209760515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21182924108326571785389413 3971798270311232209760515)
                ·
                  refine ⟨5957697405466848314640773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971798270311232209760515 5957697405466848314640773)
                  ·
                    refine ⟨1117068263525034058995145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957697405466848314640773 1117068263525034058995145)
                    ·
                      refine ⟨837801197643775544246359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117068263525034058995145 837801197643775544246359)
                      ·
                        rfl

theorem cell23_1631612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_1631612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631612 prefixEnd_1631612 := by exact prefixLift 1631612
  have htrace : WordTrace (prefixWord ++ tailWord_1631612) baseStart_1631612 baseEnd_1631612 := by
    simpa [prefixWord, tailWord_1631612, baseEnd_1631612] using wordTrace_append hprefix tailTrace_1631612
  have hstable : (prefixWord ++ tailWord_1631612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631612).length < 2 ^ (prefixWord ++ tailWord_1631612).sum := by decide
  have hdescent : baseEnd_1631612 < baseStart_1631612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631665 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_1631665 : Nat := 118140960795 + 1631665 * 2 ^ 59
def prefixEnd_1631665 : Nat := 4983230072969 + 3 ^ 40 * 1631665 * 2
def baseEnd_1631665 : Nat := 279276137372821278961205

theorem tailTrace_1631665 : CollatzResearch.WordTrace tailWord_1631665 prefixEnd_1631665 279276137372821278961205 := by
  unfold tailWord_1631665
  simp only [CollatzResearch.WordTrace]
  refine ⟨59511711633763846041360449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39674474422509230694240299 59511711633763846041360449)
  ·
    refine ⟨44633783725322884531020337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59511711633763846041360449 44633783725322884531020337)
    ·
      refine ⟨33475337793992163398265253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44633783725322884531020337 33475337793992163398265253)
      ·
        refine ⟨6276625836373530637174735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33475337793992163398265253 6276625836373530637174735)
        ·
          refine ⟨9414938754560295955762103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276625836373530637174735 9414938754560295955762103)
          ·
            refine ⟨14122408131840443933643155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9414938754560295955762103 14122408131840443933643155)
            ·
              refine ⟨21183612197760665900464733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14122408131840443933643155 21183612197760665900464733)
              ·
                refine ⟨7943854574160249712674275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21183612197760665900464733 7943854574160249712674275)
                ·
                  refine ⟨11915781861240374569011413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943854574160249712674275 11915781861240374569011413)
                  ·
                    refine ⟨279276137372821278961205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11915781861240374569011413 279276137372821278961205)
                    ·
                      rfl

theorem cell23_1631665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_1631665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631665 prefixEnd_1631665 := by exact prefixLift 1631665
  have htrace : WordTrace (prefixWord ++ tailWord_1631665) baseStart_1631665 baseEnd_1631665 := by
    simpa [prefixWord, tailWord_1631665, baseEnd_1631665] using wordTrace_append hprefix tailTrace_1631665
  have hstable : (prefixWord ++ tailWord_1631665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631665).length < 2 ^ (prefixWord ++ tailWord_1631665).sum := by decide
  have hdescent : baseEnd_1631665 < baseStart_1631665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631669 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 5]
def baseStart_1631669 : Nat := 118140960795 + 1631669 * 2 ^ 59
def prefixEnd_1631669 : Nat := 4983230072969 + 3 ^ 40 * 1631669 * 2
def baseEnd_1631669 : Nat := 93092274004564646803733

theorem tailTrace_1631669 : CollatzResearch.WordTrace tailWord_1631669 prefixEnd_1631669 93092274004564646803733 := by
  unfold tailWord_1631669
  simp only [CollatzResearch.WordTrace]
  refine ⟨59511857525749354724506061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39674571683832903149670707 59511857525749354724506061)
  ·
    refine ⟨22316946572156008021689773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59511857525749354724506061 22316946572156008021689773)
    ·
      refine ⟨8368854964558503008133665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22316946572156008021689773 8368854964558503008133665)
      ·
        refine ⟨6276641223418877256100249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8368854964558503008133665 6276641223418877256100249)
        ·
          refine ⟨4707480917564157942075187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6276641223418877256100249 4707480917564157942075187)
          ·
            refine ⟨7061221376346236913112781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707480917564157942075187 7061221376346236913112781)
            ·
              refine ⟨2647958016129838842417293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7061221376346236913112781 2647958016129838842417293)
              ·
                refine ⟨992984256048689565906485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2647958016129838842417293 992984256048689565906485)
                ·
                  refine ⟨93092274004564646803733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992984256048689565906485 93092274004564646803733)
                  ·
                    rfl

theorem cell23_1631669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_1631669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631669 prefixEnd_1631669 := by exact prefixLift 1631669
  have htrace : WordTrace (prefixWord ++ tailWord_1631669) baseStart_1631669 baseEnd_1631669 := by
    simpa [prefixWord, tailWord_1631669, baseEnd_1631669] using wordTrace_append hprefix tailTrace_1631669
  have hstable : (prefixWord ++ tailWord_1631669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631669).length < 2 ^ (prefixWord ++ tailWord_1631669).sum := by decide
  have hdescent : baseEnd_1631669 < baseStart_1631669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631692 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1631692 : Nat := 118140960795 + 1631692 * 2 ^ 59
def prefixEnd_1631692 : Nat := 4983230072969 + 3 ^ 40 * 1631692 * 2
def baseEnd_1631692 : Nat := 837842276096135231245991

theorem tailTrace_1631692 : CollatzResearch.WordTrace tailWord_1631692 prefixEnd_1631692 837842276096135231245991 := by
  unfold tailWord_1631692
  simp only [CollatzResearch.WordTrace]
  refine ⟨29756348202333014826296665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39675130936444019768395553 29756348202333014826296665)
  ·
    refine ⟨22317261151749761119722499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29756348202333014826296665 22317261151749761119722499)
    ·
      refine ⟨33475891727624641679583749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22317261151749761119722499 33475891727624641679583749)
      ·
        refine ⟨6276729698929620314921953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33475891727624641679583749 6276729698929620314921953)
        ·
          refine ⟨4707547274197215236191465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6276729698929620314921953 4707547274197215236191465)
          ·
            refine ⟨3530660455647911427143599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4707547274197215236191465 3530660455647911427143599)
            ·
              refine ⟨5295990683471867140715399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530660455647911427143599 5295990683471867140715399)
              ·
                refine ⟨7943986025207800711073099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295990683471867140715399 7943986025207800711073099)
                ·
                  refine ⟨11915979037811701066609649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943986025207800711073099 11915979037811701066609649)
                  ·
                    refine ⟨8936984278358775799957237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11915979037811701066609649 8936984278358775799957237)
                    ·
                      refine ⟨837842276096135231245991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8936984278358775799957237 837842276096135231245991)
                      ·
                        rfl

theorem cell23_1631692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1631692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631692 prefixEnd_1631692 := by exact prefixLift 1631692
  have htrace : WordTrace (prefixWord ++ tailWord_1631692) baseStart_1631692 baseEnd_1631692 := by
    simpa [prefixWord, tailWord_1631692, baseEnd_1631692] using wordTrace_append hprefix tailTrace_1631692
  have hstable : (prefixWord ++ tailWord_1631692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631692).length < 2 ^ (prefixWord ++ tailWord_1631692).sum := by decide
  have hdescent : baseEnd_1631692 < baseStart_1631692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631719 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1631719 : Nat := 118140960795 + 1631719 * 2 ^ 59
def prefixEnd_1631719 : Nat := 4983230072969 + 3 ^ 40 * 1631719 * 2
def baseEnd_1631719 : Nat := 837856140073806625608367

theorem tailTrace_1631719 : CollatzResearch.WordTrace tailWord_1631719 prefixEnd_1631719 837856140073806625608367 := by
  unfold tailWord_1631719
  simp only [CollatzResearch.WordTrace]
  refine ⟨59513681175568213263826211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39675787450378808842550807 59513681175568213263826211)
  ·
    refine ⟨89270521763352319895739317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59513681175568213263826211 89270521763352319895739317)
    ·
      refine ⟨8369111415314279990225561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89270521763352319895739317 8369111415314279990225561)
      ·
        refine ⟨6276833561485709992669171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8369111415314279990225561 6276833561485709992669171)
        ·
          refine ⟨9415250342228564989003757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276833561485709992669171 9415250342228564989003757)
          ·
            refine ⟨3530718878335711870876409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9415250342228564989003757 3530718878335711870876409)
            ·
              refine ⟨2648039158751783903157307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3530718878335711870876409 2648039158751783903157307)
              ·
                refine ⟨3972058738127675854735961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648039158751783903157307 3972058738127675854735961)
                ·
                  refine ⟨2979044053595756891051971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972058738127675854735961 2979044053595756891051971)
                  ·
                    refine ⟨4468566080393635336577957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2979044053595756891051971 4468566080393635336577957)
                    ·
                      refine ⟨837856140073806625608367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4468566080393635336577957 837856140073806625608367)
                      ·
                        rfl

theorem cell23_1631719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1631719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631719 prefixEnd_1631719 := by exact prefixLift 1631719
  have htrace : WordTrace (prefixWord ++ tailWord_1631719) baseStart_1631719 baseEnd_1631719 := by
    simpa [prefixWord, tailWord_1631719, baseEnd_1631719] using wordTrace_append hprefix tailTrace_1631719
  have hstable : (prefixWord ++ tailWord_1631719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631719).length < 2 ^ (prefixWord ++ tailWord_1631719).sum := by decide
  have hdescent : baseEnd_1631719 < baseStart_1631719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631772 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1631772 : Nat := 118140960795 + 1631772 * 2 ^ 59
def prefixEnd_1631772 : Nat := 4983230072969 + 3 ^ 40 * 1631772 * 2
def baseEnd_1631772 : Nat := 279294451516164972748541

theorem tailTrace_1631772 : CollatzResearch.WordTrace tailWord_1631772 prefixEnd_1631772 279294451516164972748541 := by
  unfold tailWord_1631772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29757807122188101657752785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39677076162917468877003713 29757807122188101657752785)
  ·
    refine ⟨22318355341641076243314589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29757807122188101657752785 22318355341641076243314589)
    ·
      refine ⟨8369383253115403591242971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22318355341641076243314589 8369383253115403591242971)
      ·
        refine ⟨12554074879673105386864457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8369383253115403591242971 12554074879673105386864457)
        ·
          refine ⟨9415556159754829040148343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12554074879673105386864457 9415556159754829040148343)
          ·
            refine ⟨14123334239632243560222515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9415556159754829040148343 14123334239632243560222515)
            ·
              refine ⟨21185001359448365340333773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14123334239632243560222515 21185001359448365340333773)
              ·
                refine ⟨7944375509793137002625165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21185001359448365340333773 7944375509793137002625165)
                ·
                  refine ⟨2979140816172426375984437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7944375509793137002625165 2979140816172426375984437)
                  ·
                    refine ⟨279294451516164972748541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2979140816172426375984437 279294451516164972748541)
                    ·
                      rfl

theorem cell23_1631772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1631772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631772 prefixEnd_1631772 := by exact prefixLift 1631772
  have htrace : WordTrace (prefixWord ++ tailWord_1631772) baseStart_1631772 baseEnd_1631772 := by
    simpa [prefixWord, tailWord_1631772, baseEnd_1631772] using wordTrace_append hprefix tailTrace_1631772
  have hstable : (prefixWord ++ tailWord_1631772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631772).length < 2 ^ (prefixWord ++ tailWord_1631772).sum := by decide
  have hdescent : baseEnd_1631772 < baseStart_1631772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631826 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_1631826 : Nat := 118140960795 + 1631826 * 2 ^ 59
def prefixEnd_1631826 : Nat := 4983230072969 + 3 ^ 40 * 1631826 * 2
def baseEnd_1631826 : Nat := 837911082503837706970375

theorem tailTrace_1631826 : CollatzResearch.WordTrace tailWord_1631826 prefixEnd_1631826 837911082503837706970375 := by
  unfold tailWord_1631826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14879395946545142634492833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39678389190787047025314221 14879395946545142634492833)
  ·
    refine ⟨11159546959908856975869625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14879395946545142634492833 11159546959908856975869625)
    ·
      refine ⟨8369660219931642731902219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11159546959908856975869625 8369660219931642731902219)
      ·
        refine ⟨12554490329897464097853329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8369660219931642731902219 12554490329897464097853329)
        ·
          refine ⟨9415867747423098073389997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12554490329897464097853329 9415867747423098073389997)
          ·
            refine ⟨3530950405283661777521249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9415867747423098073389997 3530950405283661777521249)
            ·
              refine ⟨2648212803962746333140937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3530950405283661777521249 2648212803962746333140937)
              ·
                refine ⟨1986159602972059749855703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648212803962746333140937 1986159602972059749855703)
                ·
                  refine ⟨2979239404458089624783555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986159602972059749855703 2979239404458089624783555)
                  ·
                    refine ⟨4468859106687134437175333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2979239404458089624783555 4468859106687134437175333)
                    ·
                      refine ⟨837911082503837706970375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4468859106687134437175333 837911082503837706970375)
                      ·
                        rfl

theorem cell23_1631826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_1631826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631826 prefixEnd_1631826 := by exact prefixLift 1631826
  have htrace : WordTrace (prefixWord ++ tailWord_1631826) baseStart_1631826 baseEnd_1631826 := by
    simpa [prefixWord, tailWord_1631826, baseEnd_1631826] using wordTrace_append hprefix tailTrace_1631826
  have hstable : (prefixWord ++ tailWord_1631826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631826).length < 2 ^ (prefixWord ++ tailWord_1631826).sum := by decide
  have hdescent : baseEnd_1631826 < baseStart_1631826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631880 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1631880 : Nat := 118140960795 + 1631880 * 2 ^ 59
def prefixEnd_1631880 : Nat := 4983230072969 + 3 ^ 40 * 1631880 * 2
def baseEnd_1631880 : Nat := 837938810459180495695127

theorem tailTrace_1631880 : CollatzResearch.WordTrace tailWord_1631880 prefixEnd_1631880 837938810459180495695127 := by
  unfold tailWord_1631880
  simp only [CollatzResearch.WordTrace]
  refine ⟨29759776663992468880218547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39679702218656625173624729 29759776663992468880218547)
  ·
    refine ⟨44639664995988703320327821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29759776663992468880218547 44639664995988703320327821)
    ·
      refine ⟨16739874373495763745122933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44639664995988703320327821 16739874373495763745122933)
      ·
        refine ⟨1569363222515227851105275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16739874373495763745122933 1569363222515227851105275)
        ·
          refine ⟨2354044833772841776657913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569363222515227851105275 2354044833772841776657913)
          ·
            refine ⟨1765533625329631332493435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354044833772841776657913 1765533625329631332493435)
            ·
              refine ⟨2648300437994446998740153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765533625329631332493435 2648300437994446998740153)
              ·
                refine ⟨1986225328495835249055115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648300437994446998740153 1986225328495835249055115)
                ·
                  refine ⟨2979337992743752873582673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986225328495835249055115 2979337992743752873582673)
                  ·
                    refine ⟨2234503494557814655187005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2979337992743752873582673 2234503494557814655187005)
                    ·
                      refine ⟨837938810459180495695127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2234503494557814655187005 837938810459180495695127)
                      ·
                        rfl

theorem cell23_1631880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1631880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631880 prefixEnd_1631880 := by exact prefixLift 1631880
  have htrace : WordTrace (prefixWord ++ tailWord_1631880) baseStart_1631880 baseEnd_1631880 := by
    simpa [prefixWord, tailWord_1631880, baseEnd_1631880] using wordTrace_append hprefix tailTrace_1631880
  have hstable : (prefixWord ++ tailWord_1631880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631880).length < 2 ^ (prefixWord ++ tailWord_1631880).sum := by decide
  have hdescent : baseEnd_1631880 < baseStart_1631880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631926 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1631926 : Nat := 118140960795 + 1631926 * 2 ^ 59
def prefixEnd_1631926 : Nat := 4983230072969 + 3 ^ 40 * 1631926 * 2
def baseEnd_1631926 : Nat := 279320810189762438573305

theorem tailTrace_1631926 : CollatzResearch.WordTrace tailWord_1631926 prefixEnd_1631926 279320810189762438573305 := by
  unfold tailWord_1631926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720076942863642976038227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39680820723878858411074421 3720076942863642976038227)
  ·
    refine ⟨5580115414295464464057341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720076942863642976038227 5580115414295464464057341)
    ·
      refine ⟨2092543280360799174021503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5580115414295464464057341 2092543280360799174021503)
      ·
        refine ⟨3138814920541198761032255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092543280360799174021503 3138814920541198761032255)
        ·
          refine ⟨4708222380811798141548383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138814920541198761032255 4708222380811798141548383)
          ·
            refine ⟨7062333571217697212322575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708222380811798141548383 7062333571217697212322575)
            ·
              refine ⟨10593500356826545818483863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062333571217697212322575 10593500356826545818483863)
              ·
                refine ⟨15890250535239818727725795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10593500356826545818483863 15890250535239818727725795)
                ·
                  refine ⟨23835375802859728091588693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15890250535239818727725795 23835375802859728091588693)
                  ·
                    refine ⟨279320810189762438573305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23835375802859728091588693 279320810189762438573305)
                    ·
                      rfl

theorem cell23_1631926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1631926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631926 prefixEnd_1631926 := by exact prefixLift 1631926
  have htrace : WordTrace (prefixWord ++ tailWord_1631926) baseStart_1631926 baseEnd_1631926 := by
    simpa [prefixWord, tailWord_1631926, baseEnd_1631926] using wordTrace_append hprefix tailTrace_1631926
  have hstable : (prefixWord ++ tailWord_1631926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631926).length < 2 ^ (prefixWord ++ tailWord_1631926).sum := by decide
  have hdescent : baseEnd_1631926 < baseStart_1631926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631933 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1631933 : Nat := 118140960795 + 1631933 * 2 ^ 59
def prefixEnd_1631933 : Nat := 4983230072969 + 3 ^ 40 * 1631933 * 2
def baseEnd_1631933 : Nat := 837966024933868788332383

theorem tailTrace_1631933 : CollatzResearch.WordTrace tailWord_1631933 prefixEnd_1631933 837966024933868788332383 := by
  unfold tailWord_1631933
  simp only [CollatzResearch.WordTrace]
  refine ⟨59521486396792927812116453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39680990931195285208077635 59521486396792927812116453)
  ·
    refine ⟨11160278699398673964771835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59521486396792927812116453 11160278699398673964771835)
    ·
      refine ⟨16740418049098010947157753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11160278699398673964771835 16740418049098010947157753)
      ·
        refine ⟨12555313536823508210368315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16740418049098010947157753 12555313536823508210368315)
        ·
          refine ⟨18832970305235262315552473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12555313536823508210368315 18832970305235262315552473)
          ·
            refine ⟨14124727728926446736664355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18832970305235262315552473 14124727728926446736664355)
            ·
              refine ⟨21187091593389670104996533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14124727728926446736664355 21187091593389670104996533)
              ·
                refine ⟨1986289836880281572343425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21187091593389670104996533 1986289836880281572343425)
                ·
                  refine ⟨1489717377660211179257569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1986289836880281572343425 1489717377660211179257569)
                  ·
                    refine ⟨1117288033245158384443177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1489717377660211179257569 1117288033245158384443177)
                    ·
                      refine ⟨837966024933868788332383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117288033245158384443177 837966024933868788332383)
                      ·
                        rfl

theorem cell23_1631933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1631933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1631933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1631933 prefixEnd_1631933 := by exact prefixLift 1631933
  have htrace : WordTrace (prefixWord ++ tailWord_1631933) baseStart_1631933 baseEnd_1631933 := by
    simpa [prefixWord, tailWord_1631933, baseEnd_1631933] using wordTrace_append hprefix tailTrace_1631933
  have hstable : (prefixWord ++ tailWord_1631933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631933).length < 2 ^ (prefixWord ++ tailWord_1631933).sum := by decide
  have hdescent : baseEnd_1631933 < baseStart_1631933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632026 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_1632026 : Nat := 118140960795 + 1632026 * 2 ^ 59
def prefixEnd_1632026 : Nat := 4983230072969 + 3 ^ 40 * 1632026 * 2
def baseEnd_1632026 : Nat := 838013778634736924469455

theorem tailTrace_1632026 : CollatzResearch.WordTrace tailWord_1632026 prefixEnd_1632026 838013778634736924469455 := by
  unfold tailWord_1632026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14881219596364001173812983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39683252256970669796834621 14881219596364001173812983)
  ·
    refine ⟨22321829394546001760719475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14881219596364001173812983 22321829394546001760719475)
    ·
      refine ⟨33482744091819002641079213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22321829394546001760719475 33482744091819002641079213)
      ·
        refine ⟨12556029034432125990404705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33482744091819002641079213 12556029034432125990404705)
        ·
          refine ⟨9417021775824094492803529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12556029034432125990404705 9417021775824094492803529)
          ·
            refine ⟨7062766331868070869602647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9417021775824094492803529 7062766331868070869602647)
            ·
              refine ⟨10594149497802106304403971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062766331868070869602647 10594149497802106304403971)
              ·
                refine ⟨15891224246703159456605957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10594149497802106304403971 15891224246703159456605957)
                ·
                  refine ⟨2979604546256842398113617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15891224246703159456605957 2979604546256842398113617)
                  ·
                    refine ⟨2234703409692631798585213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2979604546256842398113617 2234703409692631798585213)
                    ·
                      refine ⟨838013778634736924469455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2234703409692631798585213 838013778634736924469455)
                      ·
                        rfl

theorem cell23_1632026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_1632026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632026 prefixEnd_1632026 := by exact prefixLift 1632026
  have htrace : WordTrace (prefixWord ++ tailWord_1632026) baseStart_1632026 baseEnd_1632026 := by
    simpa [prefixWord, tailWord_1632026, baseEnd_1632026] using wordTrace_append hprefix tailTrace_1632026
  have hstable : (prefixWord ++ tailWord_1632026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632026).length < 2 ^ (prefixWord ++ tailWord_1632026).sum := by decide
  have hdescent : baseEnd_1632026 < baseStart_1632026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632030 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1632030 : Nat := 118140960795 + 1632030 * 2 ^ 59
def prefixEnd_1632030 : Nat := 4983230072969 + 3 ^ 40 * 1632030 * 2
def baseEnd_1632030 : Nat := 838015832557354908819437

theorem tailTrace_1632030 : CollatzResearch.WordTrace tailWord_1632030 prefixEnd_1632030 838015832557354908819437 := by
  unfold tailWord_1632030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440628034680189172299693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39683349518294342252265029 7440628034680189172299693)
  ·
    refine ⟨2790235513005070939612385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7440628034680189172299693 2790235513005070939612385)
    ·
      refine ⟨2092676634753803204709289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2790235513005070939612385 2092676634753803204709289)
      ·
        refine ⟨1569507476065352403531967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2092676634753803204709289 1569507476065352403531967)
        ·
          refine ⟨2354261214098028605297951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569507476065352403531967 2354261214098028605297951)
          ·
            refine ⟨3531391821147042907946927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354261214098028605297951 3531391821147042907946927)
            ·
              refine ⟨5297087731720564361920391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531391821147042907946927 5297087731720564361920391)
              ·
                refine ⟨7945631597580846542880587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297087731720564361920391 7945631597580846542880587)
                ·
                  refine ⟨11918447396371269814320881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7945631597580846542880587 11918447396371269814320881)
                  ·
                    refine ⟨8938835547278452360740661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11918447396371269814320881 8938835547278452360740661)
                    ·
                      refine ⟨838015832557354908819437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8938835547278452360740661 838015832557354908819437)
                      ·
                        rfl

theorem cell23_1632030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1632030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632030 prefixEnd_1632030 := by exact prefixLift 1632030
  have htrace : WordTrace (prefixWord ++ tailWord_1632030) baseStart_1632030 baseEnd_1632030 := by
    simpa [prefixWord, tailWord_1632030, baseEnd_1632030] using wordTrace_append hprefix tailTrace_1632030
  have hstable : (prefixWord ++ tailWord_1632030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632030).length < 2 ^ (prefixWord ++ tailWord_1632030).sum := by decide
  have hdescent : baseEnd_1632030 < baseStart_1632030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632033 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 3, 4]
def baseStart_1632033 : Nat := 118140960795 + 1632033 * 2 ^ 59
def prefixEnd_1632033 : Nat := 4983230072969 + 3 ^ 40 * 1632033 * 2
def baseEnd_1632033 : Nat := 279339124333106132360641

theorem tailTrace_1632033 : CollatzResearch.WordTrace tailWord_1632033 prefixEnd_1632033 279339124333106132360641 := by
  unfold tailWord_1632033
  simp only [CollatzResearch.WordTrace]
  refine ⟨59525133696430644890756753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39683422464287096593837835 59525133696430644890756753)
  ·
    refine ⟨44643850272322983668067565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59525133696430644890756753 44643850272322983668067565)
    ·
      refine ⟨16741443852121118875525337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44643850272322983668067565 16741443852121118875525337)
      ·
        refine ⟨12556082889090839156644003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16741443852121118875525337 12556082889090839156644003)
        ·
          refine ⟨18834124333636258734966005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12556082889090839156644003 18834124333636258734966005)
          ·
            refine ⟨1765699156278399256403063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18834124333636258734966005 1765699156278399256403063)
            ·
              refine ⟨2648548734417598884604595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765699156278399256403063 2648548734417598884604595)
              ·
                refine ⟨3972823101626398326906893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648548734417598884604595 3972823101626398326906893)
                ·
                  refine ⟨1489808663109899372590085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3972823101626398326906893 1489808663109899372590085)
                  ·
                    refine ⟨279339124333106132360641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1489808663109899372590085 279339124333106132360641)
                    ·
                      rfl

theorem cell23_1632033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_1632033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632033 prefixEnd_1632033 := by exact prefixLift 1632033
  have htrace : WordTrace (prefixWord ++ tailWord_1632033) baseStart_1632033 baseEnd_1632033 := by
    simpa [prefixWord, tailWord_1632033, baseEnd_1632033] using wordTrace_append hprefix tailTrace_1632033
  have hstable : (prefixWord ++ tailWord_1632033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632033).length < 2 ^ (prefixWord ++ tailWord_1632033).sum := by decide
  have hdescent : baseEnd_1632033 < baseStart_1632033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632089 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_1632089 : Nat := 118140960795 + 1632089 * 2 ^ 59
def prefixEnd_1632089 : Nat := 4983230072969 + 3 ^ 40 * 1632089 * 2
def baseEnd_1632089 : Nat := 279348709305323392660555

theorem tailTrace_1632089 : CollatzResearch.WordTrace tailWord_1632089 prefixEnd_1632089 279348709305323392660555 := by
  unfold tailWord_1632089
  simp only [CollatzResearch.WordTrace]
  refine ⟨59527176184227766454795321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39684784122818510969863547 59527176184227766454795321)
  ·
    refine ⟨44645382138170824841096491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59527176184227766454795321 44645382138170824841096491)
    ·
      refine ⟨66968073207256237261644737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44645382138170824841096491 66968073207256237261644737)
      ·
        refine ⟨50226054905442177946233553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66968073207256237261644737 50226054905442177946233553)
        ·
          refine ⟨37669541179081633459675165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50226054905442177946233553 37669541179081633459675165)
          ·
            refine ⟨14126077942155612547378187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37669541179081633459675165 14126077942155612547378187)
            ·
              refine ⟨21189116913233418821067281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14126077942155612547378187 21189116913233418821067281)
              ·
                refine ⟨15891837684925064115800461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21189116913233418821067281 15891837684925064115800461)
                ·
                  refine ⟨5959439131846899043425173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15891837684925064115800461 5959439131846899043425173)
                  ·
                    refine ⟨279348709305323392660555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5959439131846899043425173 279348709305323392660555)
                    ·
                      rfl

theorem cell23_1632089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_1632089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632089 prefixEnd_1632089 := by exact prefixLift 1632089
  have htrace : WordTrace (prefixWord ++ tailWord_1632089) baseStart_1632089 baseEnd_1632089 := by
    simpa [prefixWord, tailWord_1632089, baseEnd_1632089] using wordTrace_append hprefix tailTrace_1632089
  have hstable : (prefixWord ++ tailWord_1632089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632089).length < 2 ^ (prefixWord ++ tailWord_1632089).sum := by decide
  have hdescent : baseEnd_1632089 < baseStart_1632089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632090 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3]
def baseStart_1632090 : Nat := 118140960795 + 1632090 * 2 ^ 59
def prefixEnd_1632090 : Nat := 4983230072969 + 3 ^ 40 * 1632090 * 2
def baseEnd_1632090 : Nat := 838046641396624674069161

theorem tailTrace_1632090 : CollatzResearch.WordTrace tailWord_1632090 prefixEnd_1632090 838046641396624674069161 := by
  unfold tailWord_1632090
  simp only [CollatzResearch.WordTrace]
  refine ⟨14881803164306035906395431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39684808438149429083721149 14881803164306035906395431)
  ·
    refine ⟨22322704746459053859593147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14881803164306035906395431 22322704746459053859593147)
    ·
      refine ⟨33484057119688580789389721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22322704746459053859593147 33484057119688580789389721)
      ·
        refine ⟨25113042839766435592042291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33484057119688580789389721 25113042839766435592042291)
        ·
          refine ⟨37669564259649653388063437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25113042839766435592042291 37669564259649653388063437)
          ·
            refine ⟨14126086597368620020523789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37669564259649653388063437 14126086597368620020523789)
            ·
              refine ⟨5297282474013232507696421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14126086597368620020523789 5297282474013232507696421)
              ·
                refine ⟨993240463877481095193079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5297282474013232507696421 993240463877481095193079)
                ·
                  refine ⟨1489860695816221642789619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993240463877481095193079 1489860695816221642789619)
                  ·
                    refine ⟨2234791043724332464184429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1489860695816221642789619 2234791043724332464184429)
                    ·
                      refine ⟨838046641396624674069161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2234791043724332464184429 838046641396624674069161)
                      ·
                        rfl

theorem cell23_1632090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_1632090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632090 prefixEnd_1632090 := by exact prefixLift 1632090
  have htrace : WordTrace (prefixWord ++ tailWord_1632090) baseStart_1632090 baseEnd_1632090 := by
    simpa [prefixWord, tailWord_1632090, baseEnd_1632090] using wordTrace_append hprefix tailTrace_1632090
  have hstable : (prefixWord ++ tailWord_1632090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632090).length < 2 ^ (prefixWord ++ tailWord_1632090).sum := by decide
  have hdescent : baseEnd_1632090 < baseStart_1632090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632096 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1632096 : Nat := 118140960795 + 1632096 * 2 ^ 59
def prefixEnd_1632096 : Nat := 4983230072969 + 3 ^ 40 * 1632096 * 2
def baseEnd_1632096 : Nat := 838049722280551650594133

theorem tailTrace_1632096 : CollatzResearch.WordTrace tailWord_1632096 prefixEnd_1632096 838049722280551650594133 := by
  unfold tailWord_1632096
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763715747601203325150071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39684954330134937766866761 29763715747601203325150071)
  ·
    refine ⟨44645573621401804987725107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29763715747601203325150071 44645573621401804987725107)
    ·
      refine ⟨66968360432102707481587661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44645573621401804987725107 66968360432102707481587661)
      ·
        refine ⟨25113135162038515305595373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66968360432102707481587661 25113135162038515305595373)
        ·
          refine ⟨9417425685764443239598265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25113135162038515305595373 9417425685764443239598265)
          ·
            refine ⟨7063069264323332429698699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9417425685764443239598265 7063069264323332429698699)
            ·
              refine ⟨10594603896484998644548049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063069264323332429698699 10594603896484998644548049)
              ·
                refine ⟨7945952922363748983411037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10594603896484998644548049 7945952922363748983411037)
                ·
                  refine ⟨2979732345886405868779139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7945952922363748983411037 2979732345886405868779139)
                  ·
                    refine ⟨4469598518829608803168709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2979732345886405868779139 4469598518829608803168709)
                    ·
                      refine ⟨838049722280551650594133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4469598518829608803168709 838049722280551650594133)
                      ·
                        rfl

theorem cell23_1632096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1632096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632096 prefixEnd_1632096 := by exact prefixLift 1632096
  have htrace : WordTrace (prefixWord ++ tailWord_1632096) baseStart_1632096 baseEnd_1632096 := by
    simpa [prefixWord, tailWord_1632096, baseEnd_1632096] using wordTrace_append hprefix tailTrace_1632096
  have hstable : (prefixWord ++ tailWord_1632096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632096).length < 2 ^ (prefixWord ++ tailWord_1632096).sum := by decide
  have hdescent : baseEnd_1632096 < baseStart_1632096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632133 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_1632133 : Nat := 118140960795 + 1632133 * 2 ^ 59
def prefixEnd_1632133 : Nat := 4983230072969 + 3 ^ 40 * 1632133 * 2
def baseEnd_1632133 : Nat := 838068721064768005831463

theorem tailTrace_1632133 : CollatzResearch.WordTrace tailWord_1632133 prefixEnd_1632133 838068721064768005831463 := by
  unfold tailWord_1632133
  simp only [CollatzResearch.WordTrace]
  refine ⟨59528780996068361969397053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39685853997378907979598035 59528780996068361969397053)
  ·
    refine ⟨22323292873525635738523895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59528780996068361969397053 22323292873525635738523895)
    ·
      refine ⟨33484939310288453607785843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22323292873525635738523895 33484939310288453607785843)
      ·
        refine ⟨50227408965432680411678765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33484939310288453607785843 50227408965432680411678765)
        ·
          refine ⟨18835278362037255154379537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50227408965432680411678765 18835278362037255154379537)
          ·
            refine ⟨14126458771527941365784653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18835278362037255154379537 14126458771527941365784653)
            ·
              refine ⟨5297422039322978012169245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14126458771527941365784653 5297422039322978012169245)
              ·
                refine ⟨1986533264746116754563467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5297422039322978012169245 1986533264746116754563467)
                ·
                  refine ⟨2979799897119175131845201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986533264746116754563467 2979799897119175131845201)
                  ·
                    refine ⟨2234849922839381348883901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2979799897119175131845201 2234849922839381348883901)
                    ·
                      refine ⟨838068721064768005831463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2234849922839381348883901 838068721064768005831463)
                      ·
                        rfl

theorem cell23_1632133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_1632133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632133 prefixEnd_1632133 := by exact prefixLift 1632133
  have htrace : WordTrace (prefixWord ++ tailWord_1632133) baseStart_1632133 baseEnd_1632133 := by
    simpa [prefixWord, tailWord_1632133, baseEnd_1632133] using wordTrace_append hprefix tailTrace_1632133
  have hstable : (prefixWord ++ tailWord_1632133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632133).length < 2 ^ (prefixWord ++ tailWord_1632133).sum := by decide
  have hdescent : baseEnd_1632133 < baseStart_1632133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632136 : List Nat := [2, 1, 3, 3, 3, 1, 10]
def baseStart_1632136 : Nat := 118140960795 + 1632136 * 2 ^ 59
def prefixEnd_1632136 : Nat := 4983230072969 + 3 ^ 40 * 1632136 * 2
def baseEnd_1632136 : Nat := 10346546438354709803629

theorem tailTrace_1632136 : CollatzResearch.WordTrace tailWord_1632136 prefixEnd_1632136 10346546438354709803629 := by
  unfold tailWord_1632136
  simp only [CollatzResearch.WordTrace]
  refine ⟨29764445207528746740878131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39685926943371662321170841 29764445207528746740878131)
  ·
    refine ⟨44646667811293120111317197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29764445207528746740878131 44646667811293120111317197)
    ·
      refine ⟨16742500429234920041743949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44646667811293120111317197 16742500429234920041743949)
      ·
        refine ⟨6278437660963095015653981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16742500429234920041743949 6278437660963095015653981)
        ·
          refine ⟨2354414122861160630870243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6278437660963095015653981 2354414122861160630870243)
          ·
            refine ⟨3531621184291740946305365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354414122861160630870243 3531621184291740946305365)
            ·
              refine ⟨10346546438354709803629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3531621184291740946305365 10346546438354709803629)
              ·
                rfl

theorem cell23_1632136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 10].length) (baseStart_1632136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632136 prefixEnd_1632136 := by exact prefixLift 1632136
  have htrace : WordTrace (prefixWord ++ tailWord_1632136) baseStart_1632136 baseEnd_1632136 := by
    simpa [prefixWord, tailWord_1632136, baseEnd_1632136] using wordTrace_append hprefix tailTrace_1632136
  have hstable : (prefixWord ++ tailWord_1632136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632136).length < 2 ^ (prefixWord ++ tailWord_1632136).sum := by decide
  have hdescent : baseEnd_1632136 < baseStart_1632136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632139 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_1632139 : Nat := 118140960795 + 1632139 * 2 ^ 59
def prefixEnd_1632139 : Nat := 4983230072969 + 3 ^ 40 * 1632139 * 2
def baseEnd_1632139 : Nat := 838071801948694982356435

theorem tailTrace_1632139 : CollatzResearch.WordTrace tailWord_1632139 prefixEnd_1632139 838071801948694982356435 := by
  unfold tailWord_1632139
  simp only [CollatzResearch.WordTrace]
  refine ⟨59528999834046624994115471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39685999889364416662743647 59528999834046624994115471)
  ·
    refine ⟨89293499751069937491173207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59528999834046624994115471 89293499751069937491173207)
    ·
      refine ⟨133940249626604906236759811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89293499751069937491173207 133940249626604906236759811)
      ·
        refine ⟨200910374439907359355139717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133940249626604906236759811 200910374439907359355139717)
        ·
          refine ⟨37670695207482629879088697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200910374439907359355139717 37670695207482629879088697)
          ·
            refine ⟨28253021405611972409316523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37670695207482629879088697 28253021405611972409316523)
            ·
              refine ⟨42379532108417958613974785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28253021405611972409316523 42379532108417958613974785)
              ·
                refine ⟨31784649081313468960481089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42379532108417958613974785 31784649081313468960481089)
                ·
                  refine ⟨23838486810985101720360817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31784649081313468960481089 23838486810985101720360817)
                  ·
                    refine ⟨17878865108238826290270613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23838486810985101720360817 17878865108238826290270613)
                    ·
                      refine ⟨838071801948694982356435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17878865108238826290270613 838071801948694982356435)
                      ·
                        rfl

theorem cell23_1632139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_1632139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632139 prefixEnd_1632139 := by exact prefixLift 1632139
  have htrace : WordTrace (prefixWord ++ tailWord_1632139) baseStart_1632139 baseEnd_1632139 := by
    simpa [prefixWord, tailWord_1632139, baseEnd_1632139] using wordTrace_append hprefix tailTrace_1632139
  have hstable : (prefixWord ++ tailWord_1632139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632139).length < 2 ^ (prefixWord ++ tailWord_1632139).sum := by decide
  have hdescent : baseEnd_1632139 < baseStart_1632139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632169 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_1632169 : Nat := 118140960795 + 1632169 * 2 ^ 59
def prefixEnd_1632169 : Nat := 4983230072969 + 3 ^ 40 * 1632169 * 2
def baseEnd_1632169 : Nat := 838087206368329864981297

theorem tailTrace_1632169 : CollatzResearch.WordTrace tailWord_1632169 prefixEnd_1632169 838087206368329864981297 := by
  unfold tailWord_1632169
  simp only [CollatzResearch.WordTrace]
  refine ⟨59530094023937940117707561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39686729349291960078471707 59530094023937940117707561)
  ·
    refine ⟨44647570517953455088280671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59530094023937940117707561 44647570517953455088280671)
    ·
      refine ⟨66971355776930182632421007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44647570517953455088280671 66971355776930182632421007)
      ·
        refine ⟨100457033665395273948631511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66971355776930182632421007 100457033665395273948631511)
        ·
          refine ⟨150685550498092910922947267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100457033665395273948631511 150685550498092910922947267)
          ·
            refine ⟨226028325747139366384420901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150685550498092910922947267 226028325747139366384420901)
            ·
              refine ⟨42380311077588631197078919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226028325747139366384420901 42380311077588631197078919)
              ·
                refine ⟨63570466616382946795618379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42380311077588631197078919 63570466616382946795618379)
                ·
                  refine ⟨95355699924574420193427569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63570466616382946795618379 95355699924574420193427569)
                  ·
                    refine ⟨71516774943430815145070677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95355699924574420193427569 71516774943430815145070677)
                    ·
                      refine ⟨838087206368329864981297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 71516774943430815145070677 838087206368329864981297)
                      ·
                        rfl

theorem cell23_1632169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_1632169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632169 prefixEnd_1632169 := by exact prefixLift 1632169
  have htrace : WordTrace (prefixWord ++ tailWord_1632169) baseStart_1632169 baseEnd_1632169 := by
    simpa [prefixWord, tailWord_1632169, baseEnd_1632169] using wordTrace_append hprefix tailTrace_1632169
  have hstable : (prefixWord ++ tailWord_1632169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632169).length < 2 ^ (prefixWord ++ tailWord_1632169).sum := by decide
  have hdescent : baseEnd_1632169 < baseStart_1632169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632206 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1632206 : Nat := 118140960795 + 1632206 * 2 ^ 59
def prefixEnd_1632206 : Nat := 4983230072969 + 3 ^ 40 * 1632206 * 2
def baseEnd_1632206 : Nat := 838106205152546220218627

theorem tailTrace_1632206 : CollatzResearch.WordTrace tailWord_1632206 prefixEnd_1632206 838106205152546220218627 := by
  unfold tailWord_1632206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441430440600486929600559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39687629016535930291202981 7441430440600486929600559)
  ·
    refine ⟨11162145660900730394400839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7441430440600486929600559 11162145660900730394400839)
    ·
      refine ⟨16743218491351095591601259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11162145660900730394400839 16743218491351095591601259)
      ·
        refine ⟨25114827737026643387401889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16743218491351095591601259 25114827737026643387401889)
        ·
          refine ⟨18836120802769982540551417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25114827737026643387401889 18836120802769982540551417)
          ·
            refine ⟨14127090602077486905413563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18836120802769982540551417 14127090602077486905413563)
            ·
              refine ⟨21190635903116230358120345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14127090602077486905413563 21190635903116230358120345)
              ·
                refine ⟨15892976927337172768590259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21190635903116230358120345 15892976927337172768590259)
                ·
                  refine ⟨23839465391005759152885389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892976927337172768590259 23839465391005759152885389)
                  ·
                    refine ⟨8939799521627159682332021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23839465391005759152885389 8939799521627159682332021)
                    ·
                      refine ⟨838106205152546220218627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8939799521627159682332021 838106205152546220218627)
                      ·
                        rfl

theorem cell23_1632206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1632206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632206 prefixEnd_1632206 := by exact prefixLift 1632206
  have htrace : WordTrace (prefixWord ++ tailWord_1632206) baseStart_1632206 baseEnd_1632206 := by
    simpa [prefixWord, tailWord_1632206, baseEnd_1632206] using wordTrace_append hprefix tailTrace_1632206
  have hstable : (prefixWord ++ tailWord_1632206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632206).length < 2 ^ (prefixWord ++ tailWord_1632206).sum := by decide
  have hdescent : baseEnd_1632206 < baseStart_1632206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632214 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1632214 : Nat := 118140960795 + 1632214 * 2 ^ 59
def prefixEnd_1632214 : Nat := 4983230072969 + 3 ^ 40 * 1632214 * 2
def baseEnd_1632214 : Nat := 838110312997782188918591

theorem tailTrace_1632214 : CollatzResearch.WordTrace tailWord_1632214 prefixEnd_1632214 838110312997782188918591 := by
  unfold tailWord_1632214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720733456798432050193481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39687823539183275202063797 3720733456798432050193481)
  ·
    refine ⟨2790550092598824037645111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3720733456798432050193481 2790550092598824037645111)
    ·
      refine ⟨4185825138898236056467667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790550092598824037645111 4185825138898236056467667)
      ·
        refine ⟨6278737708347354084701501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185825138898236056467667 6278737708347354084701501)
        ·
          refine ⟨2354526640630257781763063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6278737708347354084701501 2354526640630257781763063)
          ·
            refine ⟨3531789960945386672644595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354526640630257781763063 3531789960945386672644595)
            ·
              refine ⟨5297684941418080008966893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531789960945386672644595 5297684941418080008966893)
              ·
                refine ⟨1986631853031780003362585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5297684941418080008966893 1986631853031780003362585)
                ·
                  refine ⟨1489973889773835002521939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1986631853031780003362585 1489973889773835002521939)
                  ·
                    refine ⟨2234960834660752503782909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1489973889773835002521939 2234960834660752503782909)
                    ·
                      refine ⟨838110312997782188918591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2234960834660752503782909 838110312997782188918591)
                      ·
                        rfl

theorem cell23_1632214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1632214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632214 prefixEnd_1632214 := by exact prefixLift 1632214
  have htrace : WordTrace (prefixWord ++ tailWord_1632214) baseStart_1632214 baseEnd_1632214 := by
    simpa [prefixWord, tailWord_1632214, baseEnd_1632214] using wordTrace_append hprefix tailTrace_1632214
  have hstable : (prefixWord ++ tailWord_1632214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632214).length < 2 ^ (prefixWord ++ tailWord_1632214).sum := by decide
  have hdescent : baseEnd_1632214 < baseStart_1632214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632216 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1632216 : Nat := 118140960795 + 1632216 * 2 ^ 59
def prefixEnd_1632216 : Nat := 4983230072969 + 3 ^ 40 * 1632216 * 2
def baseEnd_1632216 : Nat := 838111339959091181093581

theorem tailTrace_1632216 : CollatzResearch.WordTrace tailWord_1632216 prefixEnd_1632216 838111339959091181093581 := by
  unfold tailWord_1632216
  simp only [CollatzResearch.WordTrace]
  refine ⟨29765904127383833572334251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39687872169845111429779001 29765904127383833572334251)
  ·
    refine ⟨44648856191075750358501377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29765904127383833572334251 44648856191075750358501377)
    ·
      refine ⟨33486642143306812768876033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44648856191075750358501377 33486642143306812768876033)
      ·
        refine ⟨25114981607480109576657025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33486642143306812768876033 25114981607480109576657025)
        ·
          refine ⟨18836236205610082182492769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25114981607480109576657025 18836236205610082182492769)
          ·
            refine ⟨14127177154207561636869577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18836236205610082182492769 14127177154207561636869577)
            ·
              refine ⟨10595382865655671227652183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14127177154207561636869577 10595382865655671227652183)
              ·
                refine ⟨15893074298483506841478275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595382865655671227652183 15893074298483506841478275)
                ·
                  refine ⟨23839611447725260262217413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15893074298483506841478275 23839611447725260262217413)
                  ·
                    refine ⟨4469927146448486299165765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23839611447725260262217413 4469927146448486299165765)
                    ·
                      refine ⟨838111339959091181093581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4469927146448486299165765 838111339959091181093581)
                      ·
                        rfl

theorem cell23_1632216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1632216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632216 prefixEnd_1632216 := by exact prefixLift 1632216
  have htrace : WordTrace (prefixWord ++ tailWord_1632216) baseStart_1632216 baseEnd_1632216 := by
    simpa [prefixWord, tailWord_1632216, baseEnd_1632216] using wordTrace_append hprefix tailTrace_1632216
  have hstable : (prefixWord ++ tailWord_1632216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632216).length < 2 ^ (prefixWord ++ tailWord_1632216).sum := by decide
  have hdescent : baseEnd_1632216 < baseStart_1632216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632254 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1632254 : Nat := 118140960795 + 1632254 * 2 ^ 59
def prefixEnd_1632254 : Nat := 4983230072969 + 3 ^ 40 * 1632254 * 2
def baseEnd_1632254 : Nat := 838130852223962032418407

theorem tailTrace_1632254 : CollatzResearch.WordTrace tailWord_1632254 prefixEnd_1632254 838130852223962032418407 := by
  unfold tailWord_1632254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441649278578749954318977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39688796152419999756367877 7441649278578749954318977)
  ·
    refine ⟨5581236958934062465739233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7441649278578749954318977 5581236958934062465739233)
    ·
      refine ⟨4185927719200546849304425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5581236958934062465739233 4185927719200546849304425)
      ·
        refine ⟨3139445789400410136978319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4185927719200546849304425 3139445789400410136978319)
        ·
          refine ⟨4709168684100615205467479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139445789400410136978319 4709168684100615205467479)
          ·
            refine ⟨7063753026150922808201219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709168684100615205467479 7063753026150922808201219)
            ·
              refine ⟨10595629539226384212301829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063753026150922808201219 10595629539226384212301829)
              ·
                refine ⟨1986680538604947039806593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10595629539226384212301829 1986680538604947039806593)
                ·
                  refine ⟨1490010403953710279854945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1986680538604947039806593 1490010403953710279854945)
                  ·
                    refine ⟨1117507802965282709891209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1490010403953710279854945 1117507802965282709891209)
                    ·
                      refine ⟨838130852223962032418407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117507802965282709891209 838130852223962032418407)
                      ·
                        rfl

theorem cell23_1632254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1632254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632254 prefixEnd_1632254 := by exact prefixLift 1632254
  have htrace : WordTrace (prefixWord ++ tailWord_1632254) baseStart_1632254 baseEnd_1632254 := by
    simpa [prefixWord, tailWord_1632254, baseEnd_1632254] using wordTrace_append hprefix tailTrace_1632254
  have hstable : (prefixWord ++ tailWord_1632254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632254).length < 2 ^ (prefixWord ++ tailWord_1632254).sum := by decide
  have hdescent : baseEnd_1632254 < baseStart_1632254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632256 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_1632256 : Nat := 118140960795 + 1632256 * 2 ^ 59
def prefixEnd_1632256 : Nat := 4983230072969 + 3 ^ 40 * 1632256 * 2
def baseEnd_1632256 : Nat := 279377293061757008197799

theorem tailTrace_1632256 : CollatzResearch.WordTrace tailWord_1632256 prefixEnd_1632256 279377293061757008197799 := by
  unfold tailWord_1632256
  simp only [CollatzResearch.WordTrace]
  refine ⟨29766633587311376988062311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39688844783081835984083081 29766633587311376988062311)
  ·
    refine ⟨44649950380967065482093467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29766633587311376988062311 44649950380967065482093467)
    ·
      refine ⟨66974925571450598223140201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44649950380967065482093467 66974925571450598223140201)
      ·
        refine ⟨50231194178587948667355151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66974925571450598223140201 50231194178587948667355151)
        ·
          refine ⟨75346791267881923001032727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50231194178587948667355151 75346791267881923001032727)
          ·
            refine ⟨113020186901822884501549091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75346791267881923001032727 113020186901822884501549091)
            ·
              refine ⟨169530280352734326752323637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113020186901822884501549091 169530280352734326752323637)
              ·
                refine ⟨15893463783068843133030341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169530280352734326752323637 15893463783068843133030341)
                ·
                  refine ⟨2980024459325408087443189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15893463783068843133030341 2980024459325408087443189)
                  ·
                    refine ⟨279377293061757008197799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2980024459325408087443189 279377293061757008197799)
                    ·
                      rfl

theorem cell23_1632256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_1632256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632256 prefixEnd_1632256 := by exact prefixLift 1632256
  have htrace : WordTrace (prefixWord ++ tailWord_1632256) baseStart_1632256 baseEnd_1632256 := by
    simpa [prefixWord, tailWord_1632256, baseEnd_1632256] using wordTrace_append hprefix tailTrace_1632256
  have hstable : (prefixWord ++ tailWord_1632256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632256).length < 2 ^ (prefixWord ++ tailWord_1632256).sum := by decide
  have hdescent : baseEnd_1632256 < baseStart_1632256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632293 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_1632293 : Nat := 118140960795 + 1632293 * 2 ^ 59
def prefixEnd_1632293 : Nat := 4983230072969 + 3 ^ 40 * 1632293 * 2
def baseEnd_1632293 : Nat := 838150877969487379830727

theorem tailTrace_1632293 : CollatzResearch.WordTrace tailWord_1632293 prefixEnd_1632293 838150877969487379830727 := by
  unfold tailWord_1632293
  simp only [CollatzResearch.WordTrace]
  refine ⟨59534616675488709295221533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39689744450325806196814355 59534616675488709295221533)
  ·
    refine ⟨22325481253308265985708075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59534616675488709295221533 22325481253308265985708075)
    ·
      refine ⟨33488221879962398978562113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22325481253308265985708075 33488221879962398978562113)
      ·
        refine ⟨25116166409971799233921585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33488221879962398978562113 25116166409971799233921585)
        ·
          refine ⟨18837124807478849425441189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25116166409971799233921585 18837124807478849425441189)
          ·
            refine ⟨3531960901402284267270223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18837124807478849425441189 3531960901402284267270223)
            ·
              refine ⟨5297941352103426400905335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531960901402284267270223 5297941352103426400905335)
              ·
                refine ⟨7946912028155139601358003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297941352103426400905335 7946912028155139601358003)
                ·
                  refine ⟨11920368042232709402037005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946912028155139601358003 11920368042232709402037005)
                  ·
                    refine ⟨4470138015837266025763877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11920368042232709402037005 4470138015837266025763877)
                    ·
                      refine ⟨838150877969487379830727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4470138015837266025763877 838150877969487379830727)
                      ·
                        rfl

theorem cell23_1632293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_1632293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632293 prefixEnd_1632293 := by exact prefixLift 1632293
  have htrace : WordTrace (prefixWord ++ tailWord_1632293) baseStart_1632293 baseEnd_1632293 := by
    simpa [prefixWord, tailWord_1632293, baseEnd_1632293] using wordTrace_append hprefix tailTrace_1632293
  have hstable : (prefixWord ++ tailWord_1632293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632293).length < 2 ^ (prefixWord ++ tailWord_1632293).sum := by decide
  have hdescent : baseEnd_1632293 < baseStart_1632293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632310 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1632310 : Nat := 118140960795 + 1632310 * 2 ^ 59
def prefixEnd_1632310 : Nat := 4983230072969 + 3 ^ 40 * 1632310 * 2
def baseEnd_1632310 : Nat := 838159607140613813318149

theorem tailTrace_1632310 : CollatzResearch.WordTrace tailWord_1632310 prefixEnd_1632310 838159607140613813318149 := by
  unfold tailWord_1632310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720952294776695074911899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39690157810951414132393589 3720952294776695074911899)
  ·
    refine ⟨5581428442165042612367849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720952294776695074911899 5581428442165042612367849)
    ·
      refine ⟨4186071331623781959275887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5581428442165042612367849 4186071331623781959275887)
      ·
        refine ⟨6279106997435672938913831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186071331623781959275887 6279106997435672938913831)
        ·
          refine ⟨9418660496153509408370747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279106997435672938913831 9418660496153509408370747)
          ·
            refine ⟨14127990744230264112556121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418660496153509408370747 14127990744230264112556121)
            ·
              refine ⟨10595993058172698084417091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14127990744230264112556121 10595993058172698084417091)
              ·
                refine ⟨15893989587259047126625637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595993058172698084417091 15893989587259047126625637)
                ·
                  refine ⟨2980123047611071336242307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15893989587259047126625637 2980123047611071336242307)
                  ·
                    refine ⟨4470184571416607004363461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2980123047611071336242307 4470184571416607004363461)
                    ·
                      refine ⟨838159607140613813318149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4470184571416607004363461 838159607140613813318149)
                      ·
                        rfl

theorem cell23_1632310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1632310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632310 prefixEnd_1632310 := by exact prefixLift 1632310
  have htrace : WordTrace (prefixWord ++ tailWord_1632310) baseStart_1632310 baseEnd_1632310 := by
    simpa [prefixWord, tailWord_1632310, baseEnd_1632310] using wordTrace_append hprefix tailTrace_1632310
  have hstable : (prefixWord ++ tailWord_1632310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632310).length < 2 ^ (prefixWord ++ tailWord_1632310).sum := by decide
  have hdescent : baseEnd_1632310 < baseStart_1632310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632320 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 3, 4]
def baseStart_1632320 : Nat := 118140960795 + 1632320 * 2 ^ 59
def prefixEnd_1632320 : Nat := 4983230072969 + 3 ^ 40 * 1632320 * 2
def baseEnd_1632320 : Nat := 279388247315719591397701

theorem tailTrace_1632320 : CollatzResearch.WordTrace tailWord_1632320 prefixEnd_1632320 279388247315719591397701 := by
  unfold tailWord_1632320
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767800723195446453227207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39690400964260595270969609 29767800723195446453227207)
  ·
    refine ⟨44651701084793169679840811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29767800723195446453227207 44651701084793169679840811)
    ·
      refine ⟨66977551627189754519761217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44651701084793169679840811 66977551627189754519761217)
      ·
        refine ⟨50233163720392315889820913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66977551627189754519761217 50233163720392315889820913)
        ·
          refine ⟨37674872790294236917365685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50233163720392315889820913 37674872790294236917365685)
          ·
            refine ⟨3532019324090084711003033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37674872790294236917365685 3532019324090084711003033)
            ·
              refine ⟨2649014493067563533252275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532019324090084711003033 2649014493067563533252275)
              ·
                refine ⟨3973521739601345299878413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649014493067563533252275 3973521739601345299878413)
                ·
                  refine ⟨1490070652350504487454405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3973521739601345299878413 1490070652350504487454405)
                  ·
                    refine ⟨279388247315719591397701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490070652350504487454405 279388247315719591397701)
                    ·
                      rfl

theorem cell23_1632320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_1632320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632320 prefixEnd_1632320 := by exact prefixLift 1632320
  have htrace : WordTrace (prefixWord ++ tailWord_1632320) baseStart_1632320 baseEnd_1632320 := by
    simpa [prefixWord, tailWord_1632320, baseEnd_1632320] using wordTrace_append hprefix tailTrace_1632320
  have hstable : (prefixWord ++ tailWord_1632320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632320).length < 2 ^ (prefixWord ++ tailWord_1632320).sum := by decide
  have hdescent : baseEnd_1632320 < baseStart_1632320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632377 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 3]
def baseStart_1632377 : Nat := 118140960795 + 1632377 * 2 ^ 59
def prefixEnd_1632377 : Nat := 4983230072969 + 3 ^ 40 * 1632377 * 2
def baseEnd_1632377 : Nat := 838194010344465051180341

theorem tailTrace_1632377 : CollatzResearch.WordTrace tailWord_1632377 prefixEnd_1632377 838194010344465051180341 := by
  unfold tailWord_1632377
  simp only [CollatzResearch.WordTrace]
  refine ⟨59537680407184391641279385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39691786938122927760852923 59537680407184391641279385)
  ·
    refine ⟨44653260305388293730959539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59537680407184391641279385 44653260305388293730959539)
    ·
      refine ⟨66979890458082440596439309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44653260305388293730959539 66979890458082440596439309)
      ·
        refine ⟨25117458921780915223664741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66979890458082440596439309 25117458921780915223664741)
        ·
          refine ⟨4709523547833921604437139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25117458921780915223664741 4709523547833921604437139)
          ·
            refine ⟨7064285321750882406655709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709523547833921604437139 7064285321750882406655709)
            ·
              refine ⟨2649106995656580902495891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7064285321750882406655709 2649106995656580902495891)
              ·
                refine ⟨3973660493484871353743837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649106995656580902495891 3973660493484871353743837)
                ·
                  refine ⟨1490122685056826757653939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3973660493484871353743837 1490122685056826757653939)
                  ·
                    refine ⟨2235184027585240136480909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490122685056826757653939 2235184027585240136480909)
                    ·
                      refine ⟨838194010344465051180341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235184027585240136480909 838194010344465051180341)
                      ·
                        rfl

theorem cell23_1632377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_1632377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632377 prefixEnd_1632377 := by exact prefixLift 1632377
  have htrace : WordTrace (prefixWord ++ tailWord_1632377) baseStart_1632377 baseEnd_1632377 := by
    simpa [prefixWord, tailWord_1632377, baseEnd_1632377] using wordTrace_append hprefix tailTrace_1632377
  have hstable : (prefixWord ++ tailWord_1632377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632377).length < 2 ^ (prefixWord ++ tailWord_1632377).sum := by decide
  have hdescent : baseEnd_1632377 < baseStart_1632377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632393 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_1632393 : Nat := 118140960795 + 1632393 * 2 ^ 59
def prefixEnd_1632393 : Nat := 4983230072969 + 3 ^ 40 * 1632393 * 2
def baseEnd_1632393 : Nat := 279400742011645662860089

theorem tailTrace_1632393 : CollatzResearch.WordTrace tailWord_1632393 prefixEnd_1632393 279400742011645662860089 := by
  unfold tailWord_1632393
  simp only [CollatzResearch.WordTrace]
  refine ⟨59538263975126426373861833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39692175983417617582574555 59538263975126426373861833)
  ·
    refine ⟨44653697981344819780396375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59538263975126426373861833 44653697981344819780396375)
    ·
      refine ⟨66980546972017229670594563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44653697981344819780396375 66980546972017229670594563)
      ·
        refine ⟨100470820458025844505891845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66980546972017229670594563 100470820458025844505891845)
        ·
          refine ⟨18838278835879845844854721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100470820458025844505891845 18838278835879845844854721)
          ·
            refine ⟨14128709126909884383641041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18838278835879845844854721 14128709126909884383641041)
            ·
              refine ⟨10596531845182413287730781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14128709126909884383641041 10596531845182413287730781)
              ·
                refine ⟨3973699441943404982899043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10596531845182413287730781 3973699441943404982899043)
                ·
                  refine ⟨5960549162915107474348565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973699441943404982899043 5960549162915107474348565)
                  ·
                    refine ⟨279400742011645662860089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5960549162915107474348565 279400742011645662860089)
                    ·
                      rfl

theorem cell23_1632393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_1632393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632393 prefixEnd_1632393 := by exact prefixLift 1632393
  have htrace : WordTrace (prefixWord ++ tailWord_1632393) baseStart_1632393 baseEnd_1632393 := by
    simpa [prefixWord, tailWord_1632393, baseEnd_1632393] using wordTrace_append hprefix tailTrace_1632393
  have hstable : (prefixWord ++ tailWord_1632393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632393).length < 2 ^ (prefixWord ++ tailWord_1632393).sum := by decide
  have hdescent : baseEnd_1632393 < baseStart_1632393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632423 : List Nat := [1, 1, 6, 2, 13]
def baseStart_1632423 : Nat := 118140960795 + 1632423 * 2 ^ 59
def prefixEnd_1632423 : Nat := 4983230072969 + 3 ^ 40 * 1632423 * 2
def baseEnd_1632423 : Nat := 1149818423120126023601

theorem tailTrace_1632423 : CollatzResearch.WordTrace tailWord_1632423 prefixEnd_1632423 1149818423120126023601 := by
  unfold tailWord_1632423
  simp only [CollatzResearch.WordTrace]
  refine ⟨59539358165017741497453923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39692905443345160998302615 59539358165017741497453923)
  ·
    refine ⟨89309037247526612246180885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59539358165017741497453923 89309037247526612246180885)
    ·
      refine ⟨4186361120977809949039729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89309037247526612246180885 4186361120977809949039729)
      ·
        refine ⟨3139770840733357461779797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186361120977809949039729 3139770840733357461779797)
        ·
          refine ⟨1149818423120126023601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3139770840733357461779797 1149818423120126023601)
          ·
            rfl

theorem cell23_1632423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 13].length) (baseStart_1632423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632423 prefixEnd_1632423 := by exact prefixLift 1632423
  have htrace : WordTrace (prefixWord ++ tailWord_1632423) baseStart_1632423 baseEnd_1632423 := by
    simpa [prefixWord, tailWord_1632423, baseEnd_1632423] using wordTrace_append hprefix tailTrace_1632423
  have hstable : (prefixWord ++ tailWord_1632423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632423).length < 2 ^ (prefixWord ++ tailWord_1632423).sum := by decide
  have hdescent : baseEnd_1632423 < baseStart_1632423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632463 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_1632463 : Nat := 118140960795 + 1632463 * 2 ^ 59
def prefixEnd_1632463 : Nat := 4983230072969 + 3 ^ 40 * 1632463 * 2
def baseEnd_1632463 : Nat := 838238169680751714704945

theorem tailTrace_1632463 : CollatzResearch.WordTrace tailWord_1632463 prefixEnd_1632463 838238169680751714704945 := by
  unfold tailWord_1632463
  simp only [CollatzResearch.WordTrace]
  refine ⟨59540817084872828328910043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39693878056581885552606695 59540817084872828328910043)
  ·
    refine ⟨89311225627309242493365065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59540817084872828328910043 89311225627309242493365065)
    ·
      refine ⟨66983419220481931870023799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89311225627309242493365065 66983419220481931870023799)
      ·
        refine ⟨100475128830722897805035699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66983419220481931870023799 100475128830722897805035699)
        ·
          refine ⟨150712693246084346707553549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100475128830722897805035699 150712693246084346707553549)
          ·
            refine ⟨56517259967281630015332581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150712693246084346707553549 56517259967281630015332581)
            ·
              refine ⟨10596986243865305627874859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56517259967281630015332581 10596986243865305627874859)
              ·
                refine ⟨15895479365797958441812289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10596986243865305627874859 15895479365797958441812289)
                ·
                  refine ⟨11921609524348468831359217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15895479365797958441812289 11921609524348468831359217)
                  ·
                    refine ⟨8941207143261351623519413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11921609524348468831359217 8941207143261351623519413)
                    ·
                      refine ⟨838238169680751714704945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8941207143261351623519413 838238169680751714704945)
                      ·
                        rfl

theorem cell23_1632463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_1632463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632463 prefixEnd_1632463 := by exact prefixLift 1632463
  have htrace : WordTrace (prefixWord ++ tailWord_1632463) baseStart_1632463 baseEnd_1632463 := by
    simpa [prefixWord, tailWord_1632463, baseEnd_1632463] using wordTrace_append hprefix tailTrace_1632463
  have hstable : (prefixWord ++ tailWord_1632463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632463).length < 2 ^ (prefixWord ++ tailWord_1632463).sum := by decide
  have hdescent : baseEnd_1632463 < baseStart_1632463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632641 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1632641 : Nat := 118140960795 + 1632641 * 2 ^ 59
def prefixEnd_1632641 : Nat := 4983230072969 + 3 ^ 40 * 1632641 * 2
def baseEnd_1632641 : Nat := 279443189745750672759709

theorem tailTrace_1632641 : CollatzResearch.WordTrace tailWord_1632641 prefixEnd_1632641 279443189745750672759709 := by
  unfold tailWord_1632641
  simp only [CollatzResearch.WordTrace]
  refine ⟨59547309278227964728889777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39698206185485309819259851 59547309278227964728889777)
  ·
    refine ⟨44660481958670973546667333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59547309278227964728889777 44660481958670973546667333)
    ·
      refine ⟨8373840367250807540000125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44660481958670973546667333 8373840367250807540000125)
      ·
        refine ⟨3140190137719052827500047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8373840367250807540000125 3140190137719052827500047)
        ·
          refine ⟨4710285206578579241250071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140190137719052827500047 4710285206578579241250071)
          ·
            refine ⟨7065427809867868861875107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710285206578579241250071 7065427809867868861875107)
            ·
              refine ⟨10598141714801803292812661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7065427809867868861875107 10598141714801803292812661)
              ·
                refine ⟨993575785762669058701187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10598141714801803292812661 993575785762669058701187)
                ·
                  refine ⟨1490363678644003588051781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993575785762669058701187 1490363678644003588051781)
                  ·
                    refine ⟨279443189745750672759709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490363678644003588051781 279443189745750672759709)
                    ·
                      rfl

theorem cell23_1632641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1632641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632641 prefixEnd_1632641 := by exact prefixLift 1632641
  have htrace : WordTrace (prefixWord ++ tailWord_1632641) baseStart_1632641 baseEnd_1632641 := by
    simpa [prefixWord, tailWord_1632641, baseEnd_1632641] using wordTrace_append hprefix tailTrace_1632641
  have hstable : (prefixWord ++ tailWord_1632641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632641).length < 2 ^ (prefixWord ++ tailWord_1632641).sum := by decide
  have hdescent : baseEnd_1632641 < baseStart_1632641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632654 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_1632654 : Nat := 118140960795 + 1632654 * 2 ^ 59
def prefixEnd_1632654 : Nat := 4983230072969 + 3 ^ 40 * 1632654 * 2
def baseEnd_1632654 : Nat := 93148471609528940824063

theorem tailTrace_1632654 : CollatzResearch.WordTrace tailWord_1632654 prefixEnd_1632654 93148471609528940824063 := by
  unfold tailWord_1632654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443472928397608493639127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39698522284787245299408677 7443472928397608493639127)
  ·
    refine ⟨11165209392596412740458691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443472928397608493639127 11165209392596412740458691)
    ·
      refine ⟨16747814088894619110688037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11165209392596412740458691 16747814088894619110688037)
      ·
        refine ⟨3140215141667741083254007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16747814088894619110688037 3140215141667741083254007)
        ·
          refine ⟨4710322712501611624881011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140215141667741083254007 4710322712501611624881011)
          ·
            refine ⟨7065484068752417437321517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710322712501611624881011 7065484068752417437321517)
            ·
              refine ⟨2649556525782156538995569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7065484068752417437321517 2649556525782156538995569)
              ·
                refine ⟨1987167394336617404246677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649556525782156538995569 1987167394336617404246677)
                ·
                  refine ⟨93148471609528940824063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1987167394336617404246677 93148471609528940824063)
                  ·
                    rfl

theorem cell23_1632654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_1632654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632654 prefixEnd_1632654 := by exact prefixLift 1632654
  have htrace : WordTrace (prefixWord ++ tailWord_1632654) baseStart_1632654 baseEnd_1632654 := by
    simpa [prefixWord, tailWord_1632654, baseEnd_1632654] using wordTrace_append hprefix tailTrace_1632654
  have hstable : (prefixWord ++ tailWord_1632654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632654).length < 2 ^ (prefixWord ++ tailWord_1632654).sum := by decide
  have hdescent : baseEnd_1632654 < baseStart_1632654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632657 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 5, 5, 2]
def baseStart_1632657 : Nat := 118140960795 + 1632657 * 2 ^ 59
def prefixEnd_1632657 : Nat := 4983230072969 + 3 ^ 40 * 1632657 * 2
def baseEnd_1632657 : Nat := 838337784927723955679053

theorem tailTrace_1632657 : CollatzResearch.WordTrace tailWord_1632657 prefixEnd_1632657 838337784927723955679053 := by
  unfold tailWord_1632657
  simp only [CollatzResearch.WordTrace]
  refine ⟨59547892846169999461472225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39698595230779999640981483 59547892846169999461472225)
  ·
    refine ⟨44660919634627499596104169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59547892846169999461472225 44660919634627499596104169)
    ·
      refine ⟨33495689725970624697078127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44660919634627499596104169 33495689725970624697078127)
      ·
        refine ⟨50243534588955937045617191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33495689725970624697078127 50243534588955937045617191)
        ·
          refine ⟨75365301883433905568425787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50243534588955937045617191 75365301883433905568425787)
          ·
            refine ⟨113047952825150858352638681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75365301883433905568425787 113047952825150858352638681)
            ·
              refine ⟨84785964618863143764479011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113047952825150858352638681 84785964618863143764479011)
              ·
                refine ⟨127178946928294715646718517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84785964618863143764479011 127178946928294715646718517)
                ·
                  refine ⟨11923026274527629591879861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127178946928294715646718517 11923026274527629591879861)
                  ·
                    refine ⟨1117783713236965274238737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11923026274527629591879861 1117783713236965274238737)
                    ·
                      refine ⟨838337784927723955679053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117783713236965274238737 838337784927723955679053)
                      ·
                        rfl

theorem cell23_1632657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_1632657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632657 prefixEnd_1632657 := by exact prefixLift 1632657
  have htrace : WordTrace (prefixWord ++ tailWord_1632657) baseStart_1632657 baseEnd_1632657 := by
    simpa [prefixWord, tailWord_1632657, baseEnd_1632657] using wordTrace_append hprefix tailTrace_1632657
  have hstable : (prefixWord ++ tailWord_1632657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632657).length < 2 ^ (prefixWord ++ tailWord_1632657).sum := by decide
  have hdescent : baseEnd_1632657 < baseStart_1632657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632674 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_1632674 : Nat := 118140960795 + 1632674 * 2 ^ 59
def prefixEnd_1632674 : Nat := 4983230072969 + 3 ^ 40 * 1632674 * 2
def baseEnd_1632674 : Nat := 838346514098850389166475

theorem tailTrace_1632674 : CollatzResearch.WordTrace tailWord_1632674 prefixEnd_1632674 838346514098850389166475 := by
  unfold tailWord_1632674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14887128221777102841210269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39699008591405607576560717 14887128221777102841210269)
  ·
    refine ⟨5582673083166413565453851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14887128221777102841210269 5582673083166413565453851)
    ·
      refine ⟨8374009624749620348180777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582673083166413565453851 8374009624749620348180777)
      ·
        refine ⟨6280507218562215261135583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8374009624749620348180777 6280507218562215261135583)
        ·
          refine ⟨9420760827843322891703375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280507218562215261135583 9420760827843322891703375)
          ·
            refine ⟨14131141241764984337555063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420760827843322891703375 14131141241764984337555063)
            ·
              refine ⟨21196711862647476506332595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14131141241764984337555063 21196711862647476506332595)
              ·
                refine ⟨31795067793971214759498893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21196711862647476506332595 31795067793971214759498893)
                ·
                  refine ⟨11923150422739205534812085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31795067793971214759498893 11923150422739205534812085)
                  ·
                    refine ⟨1117795352131800518888633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11923150422739205534812085 1117795352131800518888633)
                    ·
                      refine ⟨838346514098850389166475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117795352131800518888633 838346514098850389166475)
                      ·
                        rfl

theorem cell23_1632674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_1632674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632674 prefixEnd_1632674 := by exact prefixLift 1632674
  have htrace : WordTrace (prefixWord ++ tailWord_1632674) baseStart_1632674 baseEnd_1632674 := by
    simpa [prefixWord, tailWord_1632674, baseEnd_1632674] using wordTrace_append hprefix tailTrace_1632674
  have hstable : (prefixWord ++ tailWord_1632674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632674).length < 2 ^ (prefixWord ++ tailWord_1632674).sum := by decide
  have hdescent : baseEnd_1632674 < baseStart_1632674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632692 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1632692 : Nat := 118140960795 + 1632692 * 2 ^ 59
def prefixEnd_1632692 : Nat := 4983230072969 + 3 ^ 40 * 1632692 * 2
def baseEnd_1632692 : Nat := 279451918916877106247131

theorem tailTrace_1632692 : CollatzResearch.WordTrace tailWord_1632692 prefixEnd_1632692 279451918916877106247131 := by
  unfold tailWord_1632692
  simp only [CollatzResearch.WordTrace]
  refine ⟨29774584700521600219498165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39699446267362133625997553 29774584700521600219498165)
  ·
    refine ⟨2791367315673900020577953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29774584700521600219498165 2791367315673900020577953)
    ·
      refine ⟨2093525486755425015433465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2791367315673900020577953 2093525486755425015433465)
      ·
        refine ⟨1570144115066568761575099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093525486755425015433465 1570144115066568761575099)
        ·
          refine ⟨2355216172599853142362649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570144115066568761575099 2355216172599853142362649)
          ·
            refine ⟨1766412129449889856771987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355216172599853142362649 1766412129449889856771987)
            ·
              refine ⟨2649618194174834785157981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766412129449889856771987 2649618194174834785157981)
              ·
                refine ⟨993606822815563044434243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2649618194174834785157981 993606822815563044434243)
                ·
                  refine ⟨1490410234223344566651365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993606822815563044434243 1490410234223344566651365)
                  ·
                    refine ⟨279451918916877106247131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490410234223344566651365 279451918916877106247131)
                    ·
                      rfl

theorem cell23_1632692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1632692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632692 prefixEnd_1632692 := by exact prefixLift 1632692
  have htrace : WordTrace (prefixWord ++ tailWord_1632692) baseStart_1632692 baseEnd_1632692 := by
    simpa [prefixWord, tailWord_1632692, baseEnd_1632692] using wordTrace_append hprefix tailTrace_1632692
  have hstable : (prefixWord ++ tailWord_1632692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632692).length < 2 ^ (prefixWord ++ tailWord_1632692).sum := by decide
  have hdescent : baseEnd_1632692 < baseStart_1632692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632707 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1632707 : Nat := 118140960795 + 1632707 * 2 ^ 59
def prefixEnd_1632707 : Nat := 4983230072969 + 3 ^ 40 * 1632707 * 2
def baseEnd_1632707 : Nat := 838363458960448760053823

theorem tailTrace_1632707 : CollatzResearch.WordTrace tailWord_1632707 prefixEnd_1632707 838363458960448760053823 := by
  unfold tailWord_1632707
  simp only [CollatzResearch.WordTrace]
  refine ⟨59549716495988858000792375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39699810997325905333861583 59549716495988858000792375)
  ·
    refine ⟨89324574743983287001188563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59549716495988858000792375 89324574743983287001188563)
    ·
      refine ⟨133986862115974930501782845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89324574743983287001188563 133986862115974930501782845)
      ·
        refine ⟨50245073293490598938168567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133986862115974930501782845 50245073293490598938168567)
        ·
          refine ⟨75367609940235898407252851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50245073293490598938168567 75367609940235898407252851)
          ·
            refine ⟨113051414910353847610879277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75367609940235898407252851 113051414910353847610879277)
            ·
              refine ⟨42394280591382692854079729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113051414910353847610879277 42394280591382692854079729)
              ·
                refine ⟨31795710443537019640559797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42394280591382692854079729 31795710443537019640559797)
                ·
                  refine ⟨2980847854081595591302481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31795710443537019640559797 2980847854081595591302481)
                  ·
                    refine ⟨2235635890561196693476861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980847854081595591302481 2235635890561196693476861)
                    ·
                      refine ⟨838363458960448760053823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235635890561196693476861 838363458960448760053823)
                      ·
                        rfl

theorem cell23_1632707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1632707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632707 prefixEnd_1632707 := by exact prefixLift 1632707
  have htrace : WordTrace (prefixWord ++ tailWord_1632707) baseStart_1632707 baseEnd_1632707 := by
    simpa [prefixWord, tailWord_1632707, baseEnd_1632707] using wordTrace_append hprefix tailTrace_1632707
  have hstable : (prefixWord ++ tailWord_1632707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632707).length < 2 ^ (prefixWord ++ tailWord_1632707).sum := by decide
  have hdescent : baseEnd_1632707 < baseStart_1632707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632708 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1632708 : Nat := 118140960795 + 1632708 * 2 ^ 59
def prefixEnd_1632708 : Nat := 4983230072969 + 3 ^ 40 * 1632708 * 2
def baseEnd_1632708 : Nat := 838363972441103256141319

theorem tailTrace_1632708 : CollatzResearch.WordTrace tailWord_1632708 prefixEnd_1632708 838363972441103256141319 := by
  unfold tailWord_1632708
  simp only [CollatzResearch.WordTrace]
  refine ⟨29774876484492617585789389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39699835312656823447719185 29774876484492617585789389)
  ·
    refine ⟨11165578681684731594671021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29774876484492617585789389 11165578681684731594671021)
    ·
      refine ⟨4187092005631774348001633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11165578681684731594671021 4187092005631774348001633)
      ·
        refine ⟨3140319004223830761001225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4187092005631774348001633 3140319004223830761001225)
        ·
          refine ⟨2355239253167873070750919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140319004223830761001225 2355239253167873070750919)
          ·
            refine ⟨3532858879751809606126379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355239253167873070750919 3532858879751809606126379)
            ·
              refine ⟨5299288319627714409189569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532858879751809606126379 5299288319627714409189569)
              ·
                refine ⟨3974466239720785806892177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299288319627714409189569 3974466239720785806892177)
                ·
                  refine ⟨2980849679790589355169133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3974466239720785806892177 2980849679790589355169133)
                  ·
                    refine ⟨1117818629921471008188425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980849679790589355169133 1117818629921471008188425)
                    ·
                      refine ⟨838363972441103256141319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117818629921471008188425 838363972441103256141319)
                      ·
                        rfl

theorem cell23_1632708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1632708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632708 prefixEnd_1632708 := by exact prefixLift 1632708
  have htrace : WordTrace (prefixWord ++ tailWord_1632708) baseStart_1632708 baseEnd_1632708 := by
    simpa [prefixWord, tailWord_1632708, baseEnd_1632708] using wordTrace_append hprefix tailTrace_1632708
  have hstable : (prefixWord ++ tailWord_1632708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632708).length < 2 ^ (prefixWord ++ tailWord_1632708).sum := by decide
  have hdescent : baseEnd_1632708 < baseStart_1632708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632714 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1632714 : Nat := 118140960795 + 1632714 * 2 ^ 59
def prefixEnd_1632714 : Nat := 4983230072969 + 3 ^ 40 * 1632714 * 2
def baseEnd_1632714 : Nat := 279455684441676744222097

theorem tailTrace_1632714 : CollatzResearch.WordTrace tailWord_1632714 prefixEnd_1632714 279455684441676744222097 := by
  unfold tailWord_1632714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14887492951740874549074299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39699981204642332130864797 14887492951740874549074299)
  ·
    refine ⟨22331239427611311823611449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14887492951740874549074299 22331239427611311823611449)
    ·
      refine ⟨16748429570708483867708587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22331239427611311823611449 16748429570708483867708587)
      ·
        refine ⟨25122644356062725801562881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16748429570708483867708587 25122644356062725801562881)
        ·
          refine ⟨18841983267047044351172161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25122644356062725801562881 18841983267047044351172161)
          ·
            refine ⟨14131487450285283263379121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18841983267047044351172161 14131487450285283263379121)
            ·
              refine ⟨10598615587713962447534341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14131487450285283263379121 10598615587713962447534341)
              ·
                refine ⟨1987240422696367958912689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10598615587713962447534341 1987240422696367958912689)
                ·
                  refine ⟨1490430317022275969184517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987240422696367958912689 1490430317022275969184517)
                  ·
                    refine ⟨279455684441676744222097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490430317022275969184517 279455684441676744222097)
                    ·
                      rfl

theorem cell23_1632714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1632714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632714 prefixEnd_1632714 := by exact prefixLift 1632714
  have htrace : WordTrace (prefixWord ++ tailWord_1632714) baseStart_1632714 baseEnd_1632714 := by
    simpa [prefixWord, tailWord_1632714, baseEnd_1632714] using wordTrace_append hprefix tailTrace_1632714
  have hstable : (prefixWord ++ tailWord_1632714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632714).length < 2 ^ (prefixWord ++ tailWord_1632714).sum := by decide
  have hdescent : baseEnd_1632714 < baseStart_1632714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632720 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1632720 : Nat := 118140960795 + 1632720 * 2 ^ 59
def prefixEnd_1632720 : Nat := 4983230072969 + 3 ^ 40 * 1632720 * 2
def baseEnd_1632720 : Nat := 838370134208957209191263

theorem tailTrace_1632720 : CollatzResearch.WordTrace tailWord_1632720 prefixEnd_1632720 838370134208957209191263 := by
  unfold tailWord_1632720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775095322470880610507807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39700127096627840814010409 29775095322470880610507807)
  ·
    refine ⟨44662642983706320915761711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29775095322470880610507807 44662642983706320915761711)
    ·
      refine ⟨66993964475559481373642567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44662642983706320915761711 66993964475559481373642567)
      ·
        refine ⟨100490946713339222060463851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66993964475559481373642567 100490946713339222060463851)
        ·
          refine ⟨150736420070008833090695777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100490946713339222060463851 150736420070008833090695777)
          ·
            refine ⟨113052315052506624818021833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150736420070008833090695777 113052315052506624818021833)
            ·
              refine ⟨84789236289379968613516375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113052315052506624818021833 84789236289379968613516375)
              ·
                refine ⟨127183854434069952920274563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84789236289379968613516375 127183854434069952920274563)
                ·
                  refine ⟨190775781651104929380411845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127183854434069952920274563 190775781651104929380411845)
                  ·
                    refine ⟨35770459059582174258827221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190775781651104929380411845 35770459059582174258827221)
                    ·
                      refine ⟨838370134208957209191263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35770459059582174258827221 838370134208957209191263)
                      ·
                        rfl

theorem cell23_1632720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1632720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632720 prefixEnd_1632720 := by exact prefixLift 1632720
  have htrace : WordTrace (prefixWord ++ tailWord_1632720) baseStart_1632720 baseEnd_1632720 := by
    simpa [prefixWord, tailWord_1632720, baseEnd_1632720] using wordTrace_append hprefix tailTrace_1632720
  have hstable : (prefixWord ++ tailWord_1632720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632720).length < 2 ^ (prefixWord ++ tailWord_1632720).sum := by decide
  have hdescent : baseEnd_1632720 < baseStart_1632720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632724 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1632724 : Nat := 118140960795 + 1632724 * 2 ^ 59
def prefixEnd_1632724 : Nat := 4983230072969 + 3 ^ 40 * 1632724 * 2
def baseEnd_1632724 : Nat := 838372188131575193541245

theorem tailTrace_1632724 : CollatzResearch.WordTrace tailWord_1632724 prefixEnd_1632724 838372188131575193541245 := by
  unfold tailWord_1632724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775168268463634952080613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39700224357951513269440817 29775168268463634952080613)
  ·
    refine ⟨5582844050336931553515115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29775168268463634952080613 5582844050336931553515115)
    ·
      refine ⟨8374266075505397330272673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582844050336931553515115 8374266075505397330272673)
      ·
        refine ⟨6280699556629047997704505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8374266075505397330272673 6280699556629047997704505)
        ·
          refine ⟨4710524667471785998278379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6280699556629047997704505 4710524667471785998278379)
          ·
            refine ⟨7065787001207678997417569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710524667471785998278379 7065787001207678997417569)
            ·
              refine ⟨5299340250905759248063177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7065787001207678997417569 5299340250905759248063177)
              ·
                refine ⟨3974505188179319436047383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299340250905759248063177 3974505188179319436047383)
                ·
                  refine ⟨5961757782268979154071075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974505188179319436047383 5961757782268979154071075)
                  ·
                    refine ⟨8942636673403468731106613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5961757782268979154071075 8942636673403468731106613)
                    ·
                      refine ⟨838372188131575193541245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8942636673403468731106613 838372188131575193541245)
                      ·
                        rfl

theorem cell23_1632724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1632724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632724 prefixEnd_1632724 := by exact prefixLift 1632724
  have htrace : WordTrace (prefixWord ++ tailWord_1632724) baseStart_1632724 baseEnd_1632724 := by
    simpa [prefixWord, tailWord_1632724, baseEnd_1632724] using wordTrace_append hprefix tailTrace_1632724
  have hstable : (prefixWord ++ tailWord_1632724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632724).length < 2 ^ (prefixWord ++ tailWord_1632724).sum := by decide
  have hdescent : baseEnd_1632724 < baseStart_1632724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632738 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1632738 : Nat := 118140960795 + 1632738 * 2 ^ 59
def prefixEnd_1632738 : Nat := 4983230072969 + 3 ^ 40 * 1632738 * 2
def baseEnd_1632738 : Nat := 838379376860738138766181

theorem tailTrace_1632738 : CollatzResearch.WordTrace tailWord_1632738 prefixEnd_1632738 838379376860738138766181 := by
  unfold tailWord_1632738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14887711789719137573792717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39700564772584366863447245 14887711789719137573792717)
  ·
    refine ⟨5582891921144676590172269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14887711789719137573792717 5582891921144676590172269)
    ·
      refine ⟨2093584470429253721314601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5582891921144676590172269 2093584470429253721314601)
      ·
        refine ⟨1570188352821940290985951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093584470429253721314601 1570188352821940290985951)
        ·
          refine ⟨2355282529232910436478927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570188352821940290985951 2355282529232910436478927)
          ·
            refine ⟨3532923793849365654718391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355282529232910436478927 3532923793849365654718391)
            ·
              refine ⟨5299385690774048482077587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532923793849365654718391 5299385690774048482077587)
              ·
                refine ⟨7949078536161072723116381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299385690774048482077587 7949078536161072723116381)
                ·
                  refine ⟨2980904451060402271168643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7949078536161072723116381 2980904451060402271168643)
                  ·
                    refine ⟨4471356676590603406752965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2980904451060402271168643 4471356676590603406752965)
                    ·
                      refine ⟨838379376860738138766181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4471356676590603406752965 838379376860738138766181)
                      ·
                        rfl

theorem cell23_1632738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1632738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632738 prefixEnd_1632738 := by exact prefixLift 1632738
  have htrace : WordTrace (prefixWord ++ tailWord_1632738) baseStart_1632738 baseEnd_1632738 := by
    simpa [prefixWord, tailWord_1632738, baseEnd_1632738] using wordTrace_append hprefix tailTrace_1632738
  have hstable : (prefixWord ++ tailWord_1632738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632738).length < 2 ^ (prefixWord ++ tailWord_1632738).sum := by decide
  have hdescent : baseEnd_1632738 < baseStart_1632738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632741 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1632741 : Nat := 118140960795 + 1632741 * 2 ^ 59
def prefixEnd_1632741 : Nat := 4983230072969 + 3 ^ 40 * 1632741 * 2
def baseEnd_1632741 : Nat := 838380917302701627028667

theorem tailTrace_1632741 : CollatzResearch.WordTrace tailWord_1632741 prefixEnd_1632741 838380917302701627028667 := by
  unfold tailWord_1632741
  simp only [CollatzResearch.WordTrace]
  refine ⟨59550956577865681807530077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39700637718577121205020051 59550956577865681807530077)
  ·
    refine ⟨22331608716699630677823779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59550956577865681807530077 22331608716699630677823779)
    ·
      refine ⟨33497413075049446016735669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22331608716699630677823779 33497413075049446016735669)
      ·
        refine ⟨3140382475785885564068969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33497413075049446016735669 3140382475785885564068969)
        ·
          refine ⟨2355286856839414173051727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140382475785885564068969 2355286856839414173051727)
          ·
            refine ⟨3532930285259121259577591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355286856839414173051727 3532930285259121259577591)
            ·
              refine ⟨5299395427888681889366387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532930285259121259577591 5299395427888681889366387)
              ·
                refine ⟨7949093141833022834049581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299395427888681889366387 7949093141833022834049581)
                ·
                  refine ⟨2980909928187383562768593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7949093141833022834049581 2980909928187383562768593)
                  ·
                    refine ⟨2235682446140537672076445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980909928187383562768593 2235682446140537672076445)
                    ·
                      refine ⟨838380917302701627028667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235682446140537672076445 838380917302701627028667)
                      ·
                        rfl

theorem cell23_1632741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1632741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632741 prefixEnd_1632741 := by exact prefixLift 1632741
  have htrace : WordTrace (prefixWord ++ tailWord_1632741) baseStart_1632741 baseEnd_1632741 := by
    simpa [prefixWord, tailWord_1632741, baseEnd_1632741] using wordTrace_append hprefix tailTrace_1632741
  have hstable : (prefixWord ++ tailWord_1632741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632741).length < 2 ^ (prefixWord ++ tailWord_1632741).sum := by decide
  have hdescent : baseEnd_1632741 < baseStart_1632741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632758 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1632758 : Nat := 118140960795 + 1632758 * 2 ^ 59
def prefixEnd_1632758 : Nat := 4983230072969 + 3 ^ 40 * 1632758 * 2
def baseEnd_1632758 : Nat := 838389646473828060516089

theorem tailTrace_1632758 : CollatzResearch.WordTrace tailWord_1632758 prefixEnd_1632758 838389646473828060516089 := by
  unfold tailWord_1632758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721973538675255856931183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39701051079202729140599285 3721973538675255856931183)
  ·
    refine ⟨5582960308012883785396775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721973538675255856931183 5582960308012883785396775)
    ·
      refine ⟨8374440462019325678095163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582960308012883785396775 8374440462019325678095163)
      ·
        refine ⟨12561660693028988517142745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8374440462019325678095163 12561660693028988517142745)
        ·
          refine ⟨9421245519771741387857059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12561660693028988517142745 9421245519771741387857059)
          ·
            refine ⟨14131868279657612081785589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421245519771741387857059 14131868279657612081785589)
            ·
              refine ⟨1324862651217901132667399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14131868279657612081785589 1324862651217901132667399)
              ·
                refine ⟨1987293976826851699001099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324862651217901132667399 1987293976826851699001099)
                ·
                  refine ⟨2980940965240277548501649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987293976826851699001099 2980940965240277548501649)
                  ·
                    refine ⟨2235705723930208161376237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980940965240277548501649 2235705723930208161376237)
                    ·
                      refine ⟨838389646473828060516089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235705723930208161376237 838389646473828060516089)
                      ·
                        rfl

theorem cell23_1632758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1632758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632758 prefixEnd_1632758 := by exact prefixLift 1632758
  have htrace : WordTrace (prefixWord ++ tailWord_1632758) baseStart_1632758 baseEnd_1632758 := by
    simpa [prefixWord, tailWord_1632758, baseEnd_1632758] using wordTrace_append hprefix tailTrace_1632758
  have hstable : (prefixWord ++ tailWord_1632758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632758).length < 2 ^ (prefixWord ++ tailWord_1632758).sum := by decide
  have hdescent : baseEnd_1632758 < baseStart_1632758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
