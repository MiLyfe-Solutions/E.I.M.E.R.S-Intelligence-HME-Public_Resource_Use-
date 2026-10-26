import V185TrunkScan21Chunk033

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_412447 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 3]
def baseStart_412447 : Nat := 118140960795 + 412447 * 2 ^ 59
def prefixEnd_412447 : Nat := 4983230072969 + 3 ^ 40 * 412447 * 2
def baseEnd_412447 : Nat := 94126024668912459073643

theorem tailTrace_412447 : CollatzResearch.WordTrace tailWord_412447 prefixEnd_412447 94126024668912459073643 := by
  unfold tailWord_412447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15043177936782434184667595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10028785291188289456445063 15043177936782434184667595)
  ·
    refine ⟨22564766905173651277001393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15043177936782434184667595 22564766905173651277001393)
    ·
      refine ⟨16923575178880238457751045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22564766905173651277001393 16923575178880238457751045)
      ·
        refine ⟨3173170346040044710828321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16923575178880238457751045 3173170346040044710828321)
        ·
          refine ⟨2379877759530033533121241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3173170346040044710828321 2379877759530033533121241)
          ·
            refine ⟨1784908319647525149840931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379877759530033533121241 1784908319647525149840931)
            ·
              refine ⟨2677362479471287724761397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784908319647525149840931 2677362479471287724761397)
              ·
                refine ⟨251002732450433224196381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2677362479471287724761397 251002732450433224196381)
                ·
                  refine ⟨94126024668912459073643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251002732450433224196381 94126024668912459073643)
                  ·
                    rfl

theorem cell21_412447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 3].length) (baseStart_412447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412447 prefixEnd_412447 := by exact prefixLift 412447
  have htrace : WordTrace (prefixWord ++ tailWord_412447) baseStart_412447 baseEnd_412447 := by
    simpa [prefixWord, tailWord_412447, baseEnd_412447] using wordTrace_append hprefix tailTrace_412447
  have hstable : (prefixWord ++ tailWord_412447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412447).length < 2 ^ (prefixWord ++ tailWord_412447).sum := by decide
  have hdescent : baseEnd_412447 < baseStart_412447 := by decide
  rcases family_descends (prefixWord ++ tailWord_412447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412492 : List Nat := [2, 2, 1, 3, 3, 1, 4, 5]
def baseStart_412492 : Nat := 118140960795 + 412492 * 2 ^ 59
def prefixEnd_412492 : Nat := 4983230072969 + 3 ^ 40 * 412492 * 2
def baseEnd_412492 : Nat := 31378764760667460274517

theorem tailTrace_412492 : CollatzResearch.WordTrace tailWord_412492 prefixEnd_412492 31378764760667460274517 := by
  unfold tailWord_412492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522409610809703435027865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10029879481079604580037153 7522409610809703435027865)
  ·
    refine ⟨5641807208107277576270899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7522409610809703435027865 5641807208107277576270899)
    ·
      refine ⟨8462710812160916364406349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5641807208107277576270899 8462710812160916364406349)
      ·
        refine ⟨3173516554560343636652381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8462710812160916364406349 3173516554560343636652381)
        ·
          refine ⟨1190068707960128863744643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3173516554560343636652381 1190068707960128863744643)
          ·
            refine ⟨1785103061940193295616965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190068707960128863744643 1785103061940193295616965)
            ·
              refine ⟨334706824113786242928181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1785103061940193295616965 334706824113786242928181)
              ·
                refine ⟨31378764760667460274517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334706824113786242928181 31378764760667460274517)
                ·
                  rfl

theorem cell21_412492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_412492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412492 prefixEnd_412492 := by exact prefixLift 412492
  have htrace : WordTrace (prefixWord ++ tailWord_412492) baseStart_412492 baseEnd_412492 := by
    simpa [prefixWord, tailWord_412492, baseEnd_412492] using wordTrace_append hprefix tailTrace_412492
  have hstable : (prefixWord ++ tailWord_412492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412492).length < 2 ^ (prefixWord ++ tailWord_412492).sum := by decide
  have hdescent : baseEnd_412492 < baseStart_412492 := by decide
  rcases family_descends (prefixWord ++ tailWord_412492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412537 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 4]
def baseStart_412537 : Nat := 118140960795 + 412537 * 2 ^ 59
def prefixEnd_412537 : Nat := 4983230072969 + 3 ^ 40 * 412537 * 2
def baseEnd_412537 : Nat := 94146563895092302573459

theorem tailTrace_412537 : CollatzResearch.WordTrace tailWord_412537 prefixEnd_412537 94146563895092302573459 := by
  unfold tailWord_412537
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046460506456379555443865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10030973670970919703629243 15046460506456379555443865)
  ·
    refine ⟨11284845379842284666582899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15046460506456379555443865 11284845379842284666582899)
    ·
      refine ⟨16927268069763426999874349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11284845379842284666582899 16927268069763426999874349)
      ·
        refine ⟨6347725526161285124952881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16927268069763426999874349 6347725526161285124952881)
        ·
          refine ⟨4760794144620963843714661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6347725526161285124952881 4760794144620963843714661)
          ·
            refine ⟨892648902116430720696499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4760794144620963843714661 892648902116430720696499)
            ·
              refine ⟨1338973353174646081044749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892648902116430720696499 1338973353174646081044749)
              ·
                refine ⟨502115007440492280391781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338973353174646081044749 502115007440492280391781)
                ·
                  refine ⟨94146563895092302573459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502115007440492280391781 94146563895092302573459)
                  ·
                    rfl

theorem cell21_412537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_412537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412537 prefixEnd_412537 := by exact prefixLift 412537
  have htrace : WordTrace (prefixWord ++ tailWord_412537) baseStart_412537 baseEnd_412537 := by
    simpa [prefixWord, tailWord_412537, baseEnd_412537] using wordTrace_append hprefix tailTrace_412537
  have hstable : (prefixWord ++ tailWord_412537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412537).length < 2 ^ (prefixWord ++ tailWord_412537).sum := by decide
  have hdescent : baseEnd_412537 < baseStart_412537 := by decide
  rcases family_descends (prefixWord ++ tailWord_412537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412551 : List Nat := [1, 1, 4, 2, 3, 1, 2, 7]
def baseStart_412551 : Nat := 118140960795 + 412551 * 2 ^ 59
def prefixEnd_412551 : Nat := 4983230072969 + 3 ^ 40 * 412551 * 2
def baseEnd_412551 : Nat := 31383252961943796446699

theorem tailTrace_412551 : CollatzResearch.WordTrace tailWord_412551 prefixEnd_412551 31383252961943796446699 := by
  unfold tailWord_412551
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046971128405659946453507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10031314085603773297635671 15046971128405659946453507)
  ·
    refine ⟨22570456692608489919680261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15046971128405659946453507 22570456692608489919680261)
    ·
      refine ⟨4231960629864091859940049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22570456692608489919680261 4231960629864091859940049)
      ·
        refine ⟨3173970472398068894955037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4231960629864091859940049 3173970472398068894955037)
        ·
          refine ⟨1190238927149275835608139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3173970472398068894955037 1190238927149275835608139)
          ·
            refine ⟨1785358390723913753412209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190238927149275835608139 1785358390723913753412209)
            ·
              refine ⟨1339018793042935315059157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785358390723913753412209 1339018793042935315059157)
              ·
                refine ⟨31383252961943796446699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1339018793042935315059157 31383252961943796446699)
                ·
                  rfl

theorem cell21_412551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_412551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412551 prefixEnd_412551 := by exact prefixLift 412551
  have htrace : WordTrace (prefixWord ++ tailWord_412551) baseStart_412551 baseEnd_412551 := by
    simpa [prefixWord, tailWord_412551, baseEnd_412551] using wordTrace_append hprefix tailTrace_412551
  have hstable : (prefixWord ++ tailWord_412551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412551).length < 2 ^ (prefixWord ++ tailWord_412551).sum := by decide
  have hdescent : baseEnd_412551 < baseStart_412551 := by decide
  rcases family_descends (prefixWord ++ tailWord_412551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412616 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_412616 : Nat := 118140960795 + 412616 * 2 ^ 59
def prefixEnd_412616 : Nat := 4983230072969 + 3 ^ 40 * 412616 * 2
def baseEnd_412616 : Nat := 94164592771405720756631

theorem tailTrace_412616 : CollatzResearch.WordTrace tailWord_412616 prefixEnd_412616 94164592771405720756631 := by
  unfold tailWord_412616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524670936585088023784851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10032894582113450698379801 7524670936585088023784851)
  ·
    refine ⟨11287006404877632035677277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7524670936585088023784851 11287006404877632035677277)
    ·
      refine ⟨4232627401829112013378979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11287006404877632035677277 4232627401829112013378979)
      ·
        refine ⟨6348941102743668020068469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4232627401829112013378979 6348941102743668020068469)
        ·
          refine ⟨595213228382218876881419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6348941102743668020068469 595213228382218876881419)
          ·
            refine ⟨892819842573328315322129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595213228382218876881419 892819842573328315322129)
            ·
              refine ⟨669614881929996236491597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892819842573328315322129 669614881929996236491597)
              ·
                refine ⟨251105580723748588684349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669614881929996236491597 251105580723748588684349)
                ·
                  refine ⟨94164592771405720756631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251105580723748588684349 94164592771405720756631)
                  ·
                    rfl

theorem cell21_412616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_412616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412616 prefixEnd_412616 := by exact prefixLift 412616
  have htrace : WordTrace (prefixWord ++ tailWord_412616) baseStart_412616 baseEnd_412616 := by
    simpa [prefixWord, tailWord_412616, baseEnd_412616] using wordTrace_append hprefix tailTrace_412616
  have hstable : (prefixWord ++ tailWord_412616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412616).length < 2 ^ (prefixWord ++ tailWord_412616).sum := by decide
  have hdescent : baseEnd_412616 < baseStart_412616 := by decide
  rcases family_descends (prefixWord ++ tailWord_412616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412630 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_412630 : Nat := 118140960795 + 412630 * 2 ^ 59
def prefixEnd_412630 : Nat := 4983230072969 + 3 ^ 40 * 412630 * 2
def baseEnd_412630 : Nat := 94167787762144807523269

theorem tailTrace_412630 : CollatzResearch.WordTrace tailWord_412630 prefixEnd_412630 94167787762144807523269 := by
  unfold tailWord_412630
  simp only [CollatzResearch.WordTrace]
  refine ⟨940615780944966027411209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10033234996746304292386229 940615780944966027411209)
  ·
    refine ⟨705461835708724520558407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 940615780944966027411209 705461835708724520558407)
    ·
      refine ⟨1058192753563086780837611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705461835708724520558407 1058192753563086780837611)
      ·
        refine ⟨1587289130344630171256417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058192753563086780837611 1587289130344630171256417)
        ·
          refine ⟨1190466847758472628442313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587289130344630171256417 1190466847758472628442313)
          ·
            refine ⟨892850135818854471331735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190466847758472628442313 892850135818854471331735)
            ·
              refine ⟨1339275203728281706997603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892850135818854471331735 1339275203728281706997603)
              ·
                refine ⟨2008912805592422560496405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339275203728281706997603 2008912805592422560496405)
                ·
                  refine ⟨94167787762144807523269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2008912805592422560496405 94167787762144807523269)
                  ·
                    rfl

theorem cell21_412630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_412630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412630 prefixEnd_412630 := by exact prefixLift 412630
  have htrace : WordTrace (prefixWord ++ tailWord_412630) baseStart_412630 baseEnd_412630 := by
    simpa [prefixWord, tailWord_412630, baseEnd_412630] using wordTrace_append hprefix tailTrace_412630
  have hstable : (prefixWord ++ tailWord_412630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412630).length < 2 ^ (prefixWord ++ tailWord_412630).sum := by decide
  have hdescent : baseEnd_412630 < baseStart_412630 := by decide
  rcases family_descends (prefixWord ++ tailWord_412630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412661 : List Nat := [1, 3, 5, 2, 1, 1, 1, 7]
def baseStart_412661 : Nat := 118140960795 + 412661 * 2 ^ 59
def prefixEnd_412661 : Nat := 4983230072969 + 3 ^ 40 * 412661 * 2
def baseEnd_412661 : Nat := 31391620794831880835513

theorem tailTrace_412661 : CollatzResearch.WordTrace tailWord_412661 prefixEnd_412661 31391620794831880835513 := by
  unfold tailWord_412661
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050983158007148732957837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10033988772004765821971891 15050983158007148732957837)
  ·
    refine ⟨5644118684252680774859189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15050983158007148732957837 5644118684252680774859189)
    ·
      refine ⟨529136126648688822643049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5644118684252680774859189 529136126648688822643049)
      ·
        refine ⟨396852094986516616982287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529136126648688822643049 396852094986516616982287)
        ·
          refine ⟨595278142479774925473431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396852094986516616982287 595278142479774925473431)
          ·
            refine ⟨892917213719662388210147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595278142479774925473431 892917213719662388210147)
            ·
              refine ⟨1339375820579493582315221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892917213719662388210147 1339375820579493582315221)
              ·
                refine ⟨31391620794831880835513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1339375820579493582315221 31391620794831880835513)
                ·
                  rfl

theorem cell21_412661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 7].length) (baseStart_412661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412661 prefixEnd_412661 := by exact prefixLift 412661
  have htrace : WordTrace (prefixWord ++ tailWord_412661) baseStart_412661 baseEnd_412661 := by
    simpa [prefixWord, tailWord_412661, baseEnd_412661] using wordTrace_append hprefix tailTrace_412661
  have hstable : (prefixWord ++ tailWord_412661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412661).length < 2 ^ (prefixWord ++ tailWord_412661).sum := by decide
  have hdescent : baseEnd_412661 < baseStart_412661 := by decide
  rcases family_descends (prefixWord ++ tailWord_412661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412703 : List Nat := [1, 1, 2, 4, 1, 4, 2, 6]
def baseStart_412703 : Nat := 118140960795 + 412703 * 2 ^ 59
def prefixEnd_412703 : Nat := 4983230072969 + 3 ^ 40 * 412703 * 2
def baseEnd_412703 : Nat := 31394815785570967602151

theorem tailTrace_412703 : CollatzResearch.WordTrace tailWord_412703 prefixEnd_412703 31394815785570967602151 := by
  unfold tailWord_412703
  simp only [CollatzResearch.WordTrace]
  refine ⟨15052515023854989905986763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10035010015903326603991175 15052515023854989905986763)
  ·
    refine ⟨22578772535782484858980145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15052515023854989905986763 22578772535782484858980145)
    ·
      refine ⟨16934079401836863644235109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22578772535782484858980145 16934079401836863644235109)
      ·
        refine ⟨3175139887844411933294083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16934079401836863644235109 3175139887844411933294083)
        ·
          refine ⟨4762709831766617899941125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175139887844411933294083 4762709831766617899941125)
          ·
            refine ⟨893008093456240856238961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4762709831766617899941125 893008093456240856238961)
            ·
              refine ⟨669756070092180642179221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893008093456240856238961 669756070092180642179221)
              ·
                refine ⟨31394815785570967602151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 669756070092180642179221 31394815785570967602151)
                ·
                  rfl

theorem cell21_412703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_412703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412703 prefixEnd_412703 := by exact prefixLift 412703
  have htrace : WordTrace (prefixWord ++ tailWord_412703) baseStart_412703 baseEnd_412703 := by
    simpa [prefixWord, tailWord_412703, baseEnd_412703] using wordTrace_append hprefix tailTrace_412703
  have hstable : (prefixWord ++ tailWord_412703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412703).length < 2 ^ (prefixWord ++ tailWord_412703).sum := by decide
  have hdescent : baseEnd_412703 < baseStart_412703 := by decide
  rcases family_descends (prefixWord ++ tailWord_412703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412706 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_412706 : Nat := 118140960795 + 412706 * 2 ^ 59
def prefixEnd_412706 : Nat := 4983230072969 + 3 ^ 40 * 412706 * 2
def baseEnd_412706 : Nat := 94185131997585564256447

theorem tailTrace_412706 : CollatzResearch.WordTrace tailWord_412706 prefixEnd_412706 94185131997585564256447 := by
  unfold tailWord_412706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763156110711030354586493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10035082961896080945563981 3763156110711030354586493)
  ·
    refine ⟨1411183541516636382969935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3763156110711030354586493 1411183541516636382969935)
    ·
      refine ⟨2116775312274954574454903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411183541516636382969935 2116775312274954574454903)
      ·
        refine ⟨3175162968412431861682355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116775312274954574454903 3175162968412431861682355)
        ·
          refine ⟨4762744452618647792523533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175162968412431861682355 4762744452618647792523533)
          ·
            refine ⟨1786029169731992922196325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4762744452618647792523533 1786029169731992922196325)
            ·
              refine ⟨334880469324748672911811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1786029169731992922196325 334880469324748672911811)
              ·
                refine ⟨502320703987123009367717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334880469324748672911811 502320703987123009367717)
                ·
                  refine ⟨94185131997585564256447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502320703987123009367717 94185131997585564256447)
                  ·
                    rfl

theorem cell21_412706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_412706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412706 prefixEnd_412706 := by exact prefixLift 412706
  have htrace : WordTrace (prefixWord ++ tailWord_412706) baseStart_412706 baseEnd_412706 := by
    simpa [prefixWord, tailWord_412706, baseEnd_412706] using wordTrace_append hprefix tailTrace_412706
  have hstable : (prefixWord ++ tailWord_412706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412706).length < 2 ^ (prefixWord ++ tailWord_412706).sum := by decide
  have hdescent : baseEnd_412706 < baseStart_412706 := by decide
  rcases family_descends (prefixWord ++ tailWord_412706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412762 : List Nat := [3, 1, 1, 2, 1, 1, 2, 10]
def baseStart_412762 : Nat := 118140960795 + 412762 * 2 ^ 59
def prefixEnd_412762 : Nat := 4983230072969 + 3 ^ 40 * 412762 * 2
def baseEnd_412762 : Nat := 31399303986847303774333

theorem tailTrace_412762 : CollatzResearch.WordTrace tailWord_412762 prefixEnd_412762 31399303986847303774333 := by
  unfold tailWord_412762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763666732660310745596135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10036444620427495321589693 3763666732660310745596135)
  ·
    refine ⟨5645500098990466118394203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3763666732660310745596135 5645500098990466118394203)
    ·
      refine ⟨8468250148485699177591305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5645500098990466118394203 8468250148485699177591305)
      ·
        refine ⟨6351187611364274383193479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8468250148485699177591305 6351187611364274383193479)
        ·
          refine ⟨9526781417046411574790219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351187611364274383193479 9526781417046411574790219)
          ·
            refine ⟨14290172125569617362185329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526781417046411574790219 14290172125569617362185329)
            ·
              refine ⟨10717629094177213021638997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14290172125569617362185329 10717629094177213021638997)
              ·
                refine ⟨31399303986847303774333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10717629094177213021638997 31399303986847303774333)
                ·
                  rfl

theorem cell21_412762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_412762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412762 prefixEnd_412762 := by exact prefixLift 412762
  have htrace : WordTrace (prefixWord ++ tailWord_412762) baseStart_412762 baseEnd_412762 := by
    simpa [prefixWord, tailWord_412762, baseEnd_412762] using wordTrace_append hprefix tailTrace_412762
  have hstable : (prefixWord ++ tailWord_412762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412762).length < 2 ^ (prefixWord ++ tailWord_412762).sum := by decide
  have hdescent : baseEnd_412762 < baseStart_412762 := by decide
  rcases family_descends (prefixWord ++ tailWord_412762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412810 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_412810 : Nat := 118140960795 + 412810 * 2 ^ 59
def prefixEnd_412810 : Nat := 4983230072969 + 3 ^ 40 * 412810 * 2
def baseEnd_412810 : Nat := 94208866214504494522901

theorem tailTrace_412810 : CollatzResearch.WordTrace tailWord_412810 prefixEnd_412810 94208866214504494522901 := by
  unfold tailWord_412810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764104408616836795032971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10037611756311564786754589 3764104408616836795032971)
  ·
    refine ⟨5646156612925255192549457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3764104408616836795032971 5646156612925255192549457)
    ·
      refine ⟨4234617459693941394412093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5646156612925255192549457 4234617459693941394412093)
      ·
        refine ⟨1587981547385228022904535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4234617459693941394412093 1587981547385228022904535)
        ·
          refine ⟨2381972321077842034356803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587981547385228022904535 2381972321077842034356803)
          ·
            refine ⟨3572958481616763051535205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381972321077842034356803 3572958481616763051535205)
            ·
              refine ⟨669929715303143072162851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3572958481616763051535205 669929715303143072162851)
              ·
                refine ⟨1004894572954714608244277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669929715303143072162851 1004894572954714608244277)
                ·
                  refine ⟨94208866214504494522901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1004894572954714608244277 94208866214504494522901)
                  ·
                    rfl

theorem cell21_412810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_412810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412810 prefixEnd_412810 := by exact prefixLift 412810
  have htrace : WordTrace (prefixWord ++ tailWord_412810) baseStart_412810 baseEnd_412810 := by
    simpa [prefixWord, tailWord_412810, baseEnd_412810] using wordTrace_append hprefix tailTrace_412810
  have hstable : (prefixWord ++ tailWord_412810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412810).length < 2 ^ (prefixWord ++ tailWord_412810).sum := by decide
  have hdescent : baseEnd_412810 < baseStart_412810 := by decide
  rcases family_descends (prefixWord ++ tailWord_412810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412914 : List Nat := [3, 2, 1, 3, 12]
def baseStart_412914 : Nat := 118140960795 + 412914 * 2 ^ 59
def prefixEnd_412914 : Nat := 4983230072969 + 3 ^ 40 * 412914 * 2
def baseEnd_412914 : Nat := 1163365437424980552955

theorem tailTrace_412914 : CollatzResearch.WordTrace tailWord_412914 prefixEnd_412914 1163365437424980552955 := by
  unfold tailWord_412914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765052706522643235479449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10040140550727048627945197 3765052706522643235479449)
  ·
    refine ⟨2823789529891982426609587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3765052706522643235479449 2823789529891982426609587)
    ·
      refine ⟨4235684294837973639914381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823789529891982426609587 4235684294837973639914381)
      ·
        refine ⟨1588381610564240114967893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4235684294837973639914381 1588381610564240114967893)
        ·
          refine ⟨1163365437424980552955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1588381610564240114967893 1163365437424980552955)
          ·
            rfl

theorem cell21_412914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 12].length) (baseStart_412914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412914 prefixEnd_412914 := by exact prefixLift 412914
  have htrace : WordTrace (prefixWord ++ tailWord_412914) baseStart_412914 baseEnd_412914 := by
    simpa [prefixWord, tailWord_412914, baseEnd_412914] using wordTrace_append hprefix tailTrace_412914
  have hstable : (prefixWord ++ tailWord_412914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412914).length < 2 ^ (prefixWord ++ tailWord_412914).sum := by decide
  have hdescent : baseEnd_412914 < baseStart_412914 := by decide
  rcases family_descends (prefixWord ++ tailWord_412914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412931 : List Nat := [1, 1, 1, 3, 2, 6, 1, 6]
def baseStart_412931 : Nat := 118140960795 + 412931 * 2 ^ 59
def prefixEnd_412931 : Nat := 4983230072969 + 3 ^ 40 * 412931 * 2
def baseEnd_412931 : Nat := 31412160021011724335329

theorem tailTrace_412931 : CollatzResearch.WordTrace tailWord_412931 prefixEnd_412931 31412160021011724335329 := by
  unfold tailWord_412931
  simp only [CollatzResearch.WordTrace]
  refine ⟨15060830867028984845286647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10040553911352656563524431 15060830867028984845286647)
  ·
    refine ⟨22591246300543477267929971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15060830867028984845286647 22591246300543477267929971)
    ·
      refine ⟨33886869450815215901894957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22591246300543477267929971 33886869450815215901894957)
      ·
        refine ⟨12707576044055705963210609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33886869450815215901894957 12707576044055705963210609)
        ·
          refine ⟨9530682033041779472407957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12707576044055705963210609 9530682033041779472407957)
          ·
            refine ⟨446750720298833412769123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9530682033041779472407957 446750720298833412769123)
            ·
              refine ⟨670126080448250119153685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446750720298833412769123 670126080448250119153685)
              ·
                refine ⟨31412160021011724335329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 670126080448250119153685 31412160021011724335329)
                ·
                  rfl

theorem cell21_412931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 6].length) (baseStart_412931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412931 prefixEnd_412931 := by exact prefixLift 412931
  have htrace : WordTrace (prefixWord ++ tailWord_412931) baseStart_412931 baseEnd_412931 := by
    simpa [prefixWord, tailWord_412931, baseEnd_412931] using wordTrace_append hprefix tailTrace_412931
  have hstable : (prefixWord ++ tailWord_412931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412931).length < 2 ^ (prefixWord ++ tailWord_412931).sum := by decide
  have hdescent : baseEnd_412931 < baseStart_412931 := by decide
  rcases family_descends (prefixWord ++ tailWord_412931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412945 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_412945 : Nat := 118140960795 + 412945 * 2 ^ 59
def prefixEnd_412945 : Nat := 4983230072969 + 3 ^ 40 * 412945 * 2
def baseEnd_412945 : Nat := 94239675053774259772625

theorem tailTrace_412945 : CollatzResearch.WordTrace tailWord_412945 prefixEnd_412945 94239675053774259772625 := by
  unfold tailWord_412945
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061341488978265236296289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10040894325985510157530859 15061341488978265236296289)
  ·
    refine ⟨11296006116733698927222217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15061341488978265236296289 11296006116733698927222217)
    ·
      refine ⟨8472004587550274195416663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11296006116733698927222217 8472004587550274195416663)
      ·
        refine ⟨12708006881325411293124995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472004587550274195416663 12708006881325411293124995)
        ·
          refine ⟨19062010321988116939687493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12708006881325411293124995 19062010321988116939687493)
          ·
            refine ⟨3574126935372771926191405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19062010321988116939687493 3574126935372771926191405)
            ·
              refine ⟨1340297600764789472321777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3574126935372771926191405 1340297600764789472321777)
              ·
                refine ⟨1005223200573592104241333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340297600764789472321777 1005223200573592104241333)
                ·
                  refine ⟨94239675053774259772625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005223200573592104241333 94239675053774259772625)
                  ·
                    rfl

theorem cell21_412945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_412945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412945 prefixEnd_412945 := by exact prefixLift 412945
  have htrace : WordTrace (prefixWord ++ tailWord_412945) baseStart_412945 baseEnd_412945 := by
    simpa [prefixWord, tailWord_412945, baseEnd_412945] using wordTrace_append hprefix tailTrace_412945
  have hstable : (prefixWord ++ tailWord_412945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412945).length < 2 ^ (prefixWord ++ tailWord_412945).sum := by decide
  have hdescent : baseEnd_412945 < baseStart_412945 := by decide
  rcases family_descends (prefixWord ++ tailWord_412945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413052 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_413052 : Nat := 118140960795 + 413052 * 2 ^ 59
def prefixEnd_413052 : Nat := 4983230072969 + 3 ^ 40 * 413052 * 2
def baseEnd_413052 : Nat := 94264093911565851489073

theorem tailTrace_413052 : CollatzResearch.WordTrace tailWord_413052 prefixEnd_413052 94264093911565851489073 := by
  unfold tailWord_413052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532622049795311255220705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10043496066393748340294273 7532622049795311255220705)
  ·
    refine ⟨5649466537346483441415529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7532622049795311255220705 5649466537346483441415529)
    ·
      refine ⟨4237099903009862581061647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5649466537346483441415529 4237099903009862581061647)
      ·
        refine ⟨6355649854514793871592471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237099903009862581061647 6355649854514793871592471)
        ·
          refine ⟨9533474781772190807388707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355649854514793871592471 9533474781772190807388707)
          ·
            refine ⟨14300212172658286211083061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533474781772190807388707 14300212172658286211083061)
            ·
              refine ⟨1340644891186714332289037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14300212172658286211083061 1340644891186714332289037)
              ·
                refine ⟨502741834195017874608389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1340644891186714332289037 502741834195017874608389)
                ·
                  refine ⟨94264093911565851489073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502741834195017874608389 94264093911565851489073)
                  ·
                    rfl

theorem cell21_413052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_413052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413052 prefixEnd_413052 := by exact prefixLift 413052
  have htrace : WordTrace (prefixWord ++ tailWord_413052) baseStart_413052 baseEnd_413052 := by
    simpa [prefixWord, tailWord_413052, baseEnd_413052] using wordTrace_append hprefix tailTrace_413052
  have hstable : (prefixWord ++ tailWord_413052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413052).length < 2 ^ (prefixWord ++ tailWord_413052).sum := by decide
  have hdescent : baseEnd_413052 < baseStart_413052 := by decide
  rcases family_descends (prefixWord ++ tailWord_413052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413145 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 4]
def baseStart_413145 : Nat := 118140960795 + 413145 * 2 ^ 59
def prefixEnd_413145 : Nat := 4983230072969 + 3 ^ 40 * 413145 * 2
def baseEnd_413145 : Nat := 94285317778618356438883

theorem tailTrace_413145 : CollatzResearch.WordTrace tailWord_413145 prefixEnd_413145 94285317778618356438883 := by
  unfold tailWord_413145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15068636088253699393576889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10045757392169132929051259 15068636088253699393576889)
  ·
    refine ⟨11301477066190274545182667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15068636088253699393576889 11301477066190274545182667)
    ·
      refine ⟨16952215599285411817774001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11301477066190274545182667 16952215599285411817774001)
      ·
        refine ⟨12714161699464058863330501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16952215599285411817774001 12714161699464058863330501)
        ·
          refine ⟨2383905318649511036874469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12714161699464058863330501 2383905318649511036874469)
          ·
            refine ⟨446982247246783319413963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2383905318649511036874469 446982247246783319413963)
            ·
              refine ⟨670473370870174979120945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446982247246783319413963 670473370870174979120945)
              ·
                refine ⟨502855028152631234340709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670473370870174979120945 502855028152631234340709)
                ·
                  refine ⟨94285317778618356438883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502855028152631234340709 94285317778618356438883)
                  ·
                    rfl

theorem cell21_413145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_413145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413145 prefixEnd_413145 := by exact prefixLift 413145
  have htrace : WordTrace (prefixWord ++ tailWord_413145) baseStart_413145 baseEnd_413145 := by
    simpa [prefixWord, tailWord_413145, baseEnd_413145] using wordTrace_append hprefix tailTrace_413145
  have hstable : (prefixWord ++ tailWord_413145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413145).length < 2 ^ (prefixWord ++ tailWord_413145).sum := by decide
  have hdescent : baseEnd_413145 < baseStart_413145 := by decide
  rcases family_descends (prefixWord ++ tailWord_413145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413162 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_413162 : Nat := 118140960795 + 413162 * 2 ^ 59
def prefixEnd_413162 : Nat := 4983230072969 + 3 ^ 40 * 413162 * 2
def baseEnd_413162 : Nat := 94289197410230104655515

theorem tailTrace_413162 : CollatzResearch.WordTrace tailWord_413162 prefixEnd_413162 94289197410230104655515 := by
  unfold tailWord_413162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767314032298027824236435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10046170752794740864630493 3767314032298027824236435)
  ·
    refine ⟨5650971048447041736354653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3767314032298027824236435 5650971048447041736354653)
    ·
      refine ⟨2119114143167640651132995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5650971048447041736354653 2119114143167640651132995)
      ·
        refine ⟨3178671214751460976699493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119114143167640651132995 3178671214751460976699493)
        ·
          refine ⟨596000852765898933131155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3178671214751460976699493 596000852765898933131155)
          ·
            refine ⟨894001279148848399696733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596000852765898933131155 894001279148848399696733)
            ·
              refine ⟨335250479680818149886275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 894001279148848399696733 335250479680818149886275)
              ·
                refine ⟨502875719521227224829413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335250479680818149886275 502875719521227224829413)
                ·
                  refine ⟨94289197410230104655515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502875719521227224829413 94289197410230104655515)
                  ·
                    rfl

theorem cell21_413162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_413162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413162 prefixEnd_413162 := by exact prefixLift 413162
  have htrace : WordTrace (prefixWord ++ tailWord_413162) baseStart_413162 baseEnd_413162 := by
    simpa [prefixWord, tailWord_413162, baseEnd_413162] using wordTrace_append hprefix tailTrace_413162
  have hstable : (prefixWord ++ tailWord_413162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413162).length < 2 ^ (prefixWord ++ tailWord_413162).sum := by decide
  have hdescent : baseEnd_413162 < baseStart_413162 := by decide
  rcases family_descends (prefixWord ++ tailWord_413162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413182 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_413182 : Nat := 118140960795 + 413182 * 2 ^ 59
def prefixEnd_413182 : Nat := 4983230072969 + 3 ^ 40 * 413182 * 2
def baseEnd_413182 : Nat := 94293761682714514322141

theorem tailTrace_413182 : CollatzResearch.WordTrace tailWord_413182 prefixEnd_413182 94293761682714514322141 := by
  unfold tailWord_413182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883748198639956839084225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10046657059413103141782533 1883748198639956839084225)
  ·
    refine ⟨1412811148979967629313169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1883748198639956839084225 1412811148979967629313169)
    ·
      refine ⟨1059608361734975721984877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1412811148979967629313169 1059608361734975721984877)
      ·
        refine ⟨397353135650615895744329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1059608361734975721984877 397353135650615895744329)
        ·
          refine ⟨298014851737961921808247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397353135650615895744329 298014851737961921808247)
          ·
            refine ⟨447022277606942882712371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298014851737961921808247 447022277606942882712371)
            ·
              refine ⟨670533416410414324068557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447022277606942882712371 670533416410414324068557)
              ·
                refine ⟨251450031153905371525709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670533416410414324068557 251450031153905371525709)
                ·
                  refine ⟨94293761682714514322141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251450031153905371525709 94293761682714514322141)
                  ·
                    rfl

theorem cell21_413182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_413182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413182 prefixEnd_413182 := by exact prefixLift 413182
  have htrace : WordTrace (prefixWord ++ tailWord_413182) baseStart_413182 baseEnd_413182 := by
    simpa [prefixWord, tailWord_413182, baseEnd_413182] using wordTrace_append hprefix tailTrace_413182
  have hstable : (prefixWord ++ tailWord_413182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413182).length < 2 ^ (prefixWord ++ tailWord_413182).sum := by decide
  have hdescent : baseEnd_413182 < baseStart_413182 := by decide
  rcases family_descends (prefixWord ++ tailWord_413182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413218 : List Nat := [3, 3, 1, 1, 1, 1, 3, 8]
def baseStart_413218 : Nat := 118140960795 + 413218 * 2 ^ 59
def prefixEnd_413218 : Nat := 4983230072969 + 3 ^ 40 * 413218 * 2
def baseEnd_413218 : Nat := 31433992457728817240689

theorem tailTrace_413218 : CollatzResearch.WordTrace tailWord_413218 prefixEnd_413218 31433992457728817240689 := by
  unfold tailWord_413218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767824654247308215246077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10047532411326155240656205 3767824654247308215246077)
  ·
    refine ⟨1412934245342740580717279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3767824654247308215246077 1412934245342740580717279)
    ·
      refine ⟨2119401368014110871075919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412934245342740580717279 2119401368014110871075919)
      ·
        refine ⟨3179102052021166306613879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119401368014110871075919 3179102052021166306613879)
        ·
          refine ⟨4768653078031749459920819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179102052021166306613879 4768653078031749459920819)
          ·
            refine ⟨7152979617047624189881229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768653078031749459920819 7152979617047624189881229)
            ·
              refine ⟨2682367356392859071205461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7152979617047624189881229 2682367356392859071205461)
              ·
                refine ⟨31433992457728817240689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2682367356392859071205461 31433992457728817240689)
                ·
                  rfl

theorem cell21_413218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_413218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413218 prefixEnd_413218 := by exact prefixLift 413218
  have htrace : WordTrace (prefixWord ++ tailWord_413218) baseStart_413218 baseEnd_413218 := by
    simpa [prefixWord, tailWord_413218, baseEnd_413218] using wordTrace_append hprefix tailTrace_413218
  have hstable : (prefixWord ++ tailWord_413218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413218).length < 2 ^ (prefixWord ++ tailWord_413218).sum := by decide
  have hdescent : baseEnd_413218 < baseStart_413218 := by decide
  rcases family_descends (prefixWord ++ tailWord_413218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413232 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_413232 : Nat := 118140960795 + 413232 * 2 ^ 59
def prefixEnd_413232 : Nat := 4983230072969 + 3 ^ 40 * 413232 * 2
def baseEnd_413232 : Nat := 94305172363925538488705

theorem tailTrace_413232 : CollatzResearch.WordTrace tailWord_413232 prefixEnd_413232 94305172363925538488705 := by
  unfold tailWord_413232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535904619469256625996975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10047872825959008834662633 7535904619469256625996975)
  ·
    refine ⟨11303856929203884938995463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7535904619469256625996975 11303856929203884938995463)
    ·
      refine ⟨16955785393805827408493195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11303856929203884938995463 16955785393805827408493195)
      ·
        refine ⟨25433678090708741112739793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16955785393805827408493195 25433678090708741112739793)
        ·
          refine ⟨19075258568031555834554845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25433678090708741112739793 19075258568031555834554845)
          ·
            refine ⟨7153221963011833437958067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19075258568031555834554845 7153221963011833437958067)
            ·
              refine ⟨10729832944517750156937101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7153221963011833437958067 10729832944517750156937101)
              ·
                refine ⟨4023687354194156308851413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10729832944517750156937101 4023687354194156308851413)
                ·
                  refine ⟨94305172363925538488705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4023687354194156308851413 94305172363925538488705)
                  ·
                    rfl

theorem cell21_413232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_413232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413232 prefixEnd_413232 := by exact prefixLift 413232
  have htrace : WordTrace (prefixWord ++ tailWord_413232) baseStart_413232 baseEnd_413232 := by
    simpa [prefixWord, tailWord_413232, baseEnd_413232] using wordTrace_append hprefix tailTrace_413232
  have hstable : (prefixWord ++ tailWord_413232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413232).length < 2 ^ (prefixWord ++ tailWord_413232).sum := by decide
  have hdescent : baseEnd_413232 < baseStart_413232 := by decide
  rcases family_descends (prefixWord ++ tailWord_413232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413308 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_413308 : Nat := 118140960795 + 413308 * 2 ^ 59
def prefixEnd_413308 : Nat := 4983230072969 + 3 ^ 40 * 413308 * 2
def baseEnd_413308 : Nat := 94322516599366295221883

theorem tailTrace_413308 : CollatzResearch.WordTrace tailWord_413308 prefixEnd_413308 94322516599366295221883 := by
  unfold tailWord_413308
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537290593331589115880289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10049720791108785487840385 7537290593331589115880289)
  ·
    refine ⟨5652967944998691836910217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7537290593331589115880289 5652967944998691836910217)
    ·
      refine ⟨4239725958749018877682663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5652967944998691836910217 4239725958749018877682663)
      ·
        refine ⟨6359588938123528316523995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239725958749018877682663 6359588938123528316523995)
        ·
          refine ⟨9539383407185292474785993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359588938123528316523995 9539383407185292474785993)
          ·
            refine ⟨7154537555388969356089495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539383407185292474785993 7154537555388969356089495)
            ·
              refine ⟨10731806333083454034134243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154537555388969356089495 10731806333083454034134243)
              ·
                refine ⟨16097709499625181051201365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10731806333083454034134243 16097709499625181051201365)
                ·
                  refine ⟨94322516599366295221883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16097709499625181051201365 94322516599366295221883)
                  ·
                    rfl

theorem cell21_413308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_413308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413308 prefixEnd_413308 := by exact prefixLift 413308
  have htrace : WordTrace (prefixWord ++ tailWord_413308) baseStart_413308 baseEnd_413308 := by
    simpa [prefixWord, tailWord_413308, baseEnd_413308] using wordTrace_append hprefix tailTrace_413308
  have hstable : (prefixWord ++ tailWord_413308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413308).length < 2 ^ (prefixWord ++ tailWord_413308).sum := by decide
  have hdescent : baseEnd_413308 < baseStart_413308 := by decide
  rcases family_descends (prefixWord ++ tailWord_413308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413342 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_413342 : Nat := 118140960795 + 413342 * 2 ^ 59
def prefixEnd_413342 : Nat := 4983230072969 + 3 ^ 40 * 413342 * 2
def baseEnd_413342 : Nat := 94330275862589791655147

theorem tailTrace_413342 : CollatzResearch.WordTrace tailWord_413342 prefixEnd_413342 94330275862589791655147 := by
  unfold tailWord_413342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884477658567500254812285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10050547512360001358998853 1884477658567500254812285)
  ·
    refine ⟨706679121962812595554607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1884477658567500254812285 706679121962812595554607)
    ·
      refine ⟨1060018682944218893331911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706679121962812595554607 1060018682944218893331911)
      ·
        refine ⟨1590028024416328339997867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060018682944218893331911 1590028024416328339997867)
        ·
          refine ⟨2385042036624492509996801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590028024416328339997867 2385042036624492509996801)
          ·
            refine ⟨1788781527468369382497601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385042036624492509996801 1788781527468369382497601)
            ·
              refine ⟨1341586145601277036873201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788781527468369382497601 1341586145601277036873201)
              ·
                refine ⟨1006189609200957777654901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341586145601277036873201 1006189609200957777654901)
                ·
                  refine ⟨94330275862589791655147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1006189609200957777654901 94330275862589791655147)
                  ·
                    rfl

theorem cell21_413342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_413342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413342 prefixEnd_413342 := by exact prefixLift 413342
  have htrace : WordTrace (prefixWord ++ tailWord_413342) baseStart_413342 baseEnd_413342 := by
    simpa [prefixWord, tailWord_413342, baseEnd_413342] using wordTrace_append hprefix tailTrace_413342
  have hstable : (prefixWord ++ tailWord_413342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413342).length < 2 ^ (prefixWord ++ tailWord_413342).sum := by decide
  have hdescent : baseEnd_413342 < baseStart_413342 := by decide
  rcases family_descends (prefixWord ++ tailWord_413342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413370 : List Nat := [3, 1, 1, 1, 2, 6, 7]
def baseStart_413370 : Nat := 118140960795 + 413370 * 2 ^ 59
def prefixEnd_413370 : Nat := 4983230072969 + 3 ^ 40 * 413370 * 2
def baseEnd_413370 : Nat := 10481851760451996132047

theorem tailTrace_413370 : CollatzResearch.WordTrace tailWord_413370 prefixEnd_413370 10481851760451996132047 := by
  unfold tailWord_413370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769210628109640705129391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10051228341625708547011709 3769210628109640705129391)
  ·
    refine ⟨5653815942164461057694087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3769210628109640705129391 5653815942164461057694087)
    ·
      refine ⟨8480723913246691586541131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653815942164461057694087 8480723913246691586541131)
      ·
        refine ⟨12721085869870037379811697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480723913246691586541131 12721085869870037379811697)
        ·
          refine ⟨9540814402402528034858773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12721085869870037379811697 9540814402402528034858773)
          ·
            refine ⟨447225675112618501634005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9540814402402528034858773 447225675112618501634005)
            ·
              refine ⟨10481851760451996132047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 447225675112618501634005 10481851760451996132047)
              ·
                rfl

theorem cell21_413370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 7].length) (baseStart_413370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413370 prefixEnd_413370 := by exact prefixLift 413370
  have htrace : WordTrace (prefixWord ++ tailWord_413370) baseStart_413370 baseEnd_413370 := by
    simpa [prefixWord, tailWord_413370, baseEnd_413370] using wordTrace_append hprefix tailTrace_413370
  have hstable : (prefixWord ++ tailWord_413370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413370).length < 2 ^ (prefixWord ++ tailWord_413370).sum := by decide
  have hdescent : baseEnd_413370 < baseStart_413370 := by decide
  rcases family_descends (prefixWord ++ tailWord_413370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413463 : List Nat := [1, 1, 3, 4, 2, 2, 3, 5]
def baseStart_413463 : Nat := 118140960795 + 413463 * 2 ^ 59
def prefixEnd_413463 : Nat := 4983230072969 + 3 ^ 40 * 413463 * 2
def baseEnd_413463 : Nat := 31452629903706823379411

theorem tailTrace_413463 : CollatzResearch.WordTrace tailWord_413463 prefixEnd_413463 31452629903706823379411 := by
  unfold tailWord_413463
  simp only [CollatzResearch.WordTrace]
  refine ⟨15080234501101639703653043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10053489667401093135768695 15080234501101639703653043)
  ·
    refine ⟨22620351751652459555479565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15080234501101639703653043 22620351751652459555479565)
    ·
      refine ⟨8482631906869672333304837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22620351751652459555479565 8482631906869672333304837)
      ·
        refine ⟨1590493482538063562494657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8482631906869672333304837 1590493482538063562494657)
        ·
          refine ⟨1192870111903547671870993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590493482538063562494657 1192870111903547671870993)
          ·
            refine ⟨894652583927660753903245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192870111903547671870993 894652583927660753903245)
            ·
              refine ⟨335494718972872782713717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 894652583927660753903245 335494718972872782713717)
              ·
                refine ⟨31452629903706823379411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335494718972872782713717 31452629903706823379411)
                ·
                  rfl

theorem cell21_413463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 5].length) (baseStart_413463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413463 prefixEnd_413463 := by exact prefixLift 413463
  have htrace : WordTrace (prefixWord ++ tailWord_413463) baseStart_413463 baseEnd_413463 := by
    simpa [prefixWord, tailWord_413463, baseEnd_413463] using wordTrace_append hprefix tailTrace_413463
  have hstable : (prefixWord ++ tailWord_413463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413463).length < 2 ^ (prefixWord ++ tailWord_413463).sum := by decide
  have hdescent : baseEnd_413463 < baseStart_413463 := by decide
  rcases family_descends (prefixWord ++ tailWord_413463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413494 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_413494 : Nat := 118140960795 + 413494 * 2 ^ 59
def prefixEnd_413494 : Nat := 4983230072969 + 3 ^ 40 * 413494 * 2
def baseEnd_413494 : Nat := 94364964333471305121503

theorem tailTrace_413494 : CollatzResearch.WordTrace tailWord_413494 prefixEnd_413494 94364964333471305121503 := by
  unfold tailWord_413494
  simp only [CollatzResearch.WordTrace]
  refine ⟨942585322749333249876971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10054243442659554665354357 942585322749333249876971)
  ·
    refine ⟨1413877984123999874815457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942585322749333249876971 1413877984123999874815457)
    ·
      refine ⟨1060408488092999906111593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1413877984123999874815457 1060408488092999906111593)
      ·
        refine ⟨795306366069749929583695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1060408488092999906111593 795306366069749929583695)
        ·
          refine ⟨1192959549104624894375543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795306366069749929583695 1192959549104624894375543)
          ·
            refine ⟨1789439323656937341563315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192959549104624894375543 1789439323656937341563315)
            ·
              refine ⟨2684158985485406012344973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789439323656937341563315 2684158985485406012344973)
              ·
                refine ⟨1006559619557027254629365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2684158985485406012344973 1006559619557027254629365)
                ·
                  refine ⟨94364964333471305121503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1006559619557027254629365 94364964333471305121503)
                  ·
                    rfl

theorem cell21_413494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_413494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413494 prefixEnd_413494 := by exact prefixLift 413494
  have htrace : WordTrace (prefixWord ++ tailWord_413494) baseStart_413494 baseEnd_413494 := by
    simpa [prefixWord, tailWord_413494, baseEnd_413494] using wordTrace_append hprefix tailTrace_413494
  have hstable : (prefixWord ++ tailWord_413494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413494).length < 2 ^ (prefixWord ++ tailWord_413494).sum := by decide
  have hdescent : baseEnd_413494 < baseStart_413494 := by decide
  rcases family_descends (prefixWord ++ tailWord_413494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413522 : List Nat := [3, 2, 2, 1, 1, 4, 1, 7]
def baseStart_413522 : Nat := 118140960795 + 413522 * 2 ^ 59
def prefixEnd_413522 : Nat := 4983230072969 + 3 ^ 40 * 413522 * 2
def baseEnd_413522 : Nat := 31457118104983159551593

theorem tailTrace_413522 : CollatzResearch.WordTrace tailWord_413522 prefixEnd_413522 31457118104983159551593 := by
  unfold tailWord_413522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770596601971973195012705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10054924271925261853367213 3770596601971973195012705)
  ·
    refine ⟨2827947451478979896259529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3770596601971973195012705 2827947451478979896259529)
    ·
      refine ⟨2120960588609234922194647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2827947451478979896259529 2120960588609234922194647)
      ·
        refine ⟨3181440882913852383291971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120960588609234922194647 3181440882913852383291971)
        ·
          refine ⟨4772161324370778574937957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181440882913852383291971 4772161324370778574937957)
          ·
            refine ⟨894780248319520982800867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4772161324370778574937957 894780248319520982800867)
            ·
              refine ⟨1342170372479281474201301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894780248319520982800867 1342170372479281474201301)
              ·
                refine ⟨31457118104983159551593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1342170372479281474201301 31457118104983159551593)
                ·
                  rfl

theorem cell21_413522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_413522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413522 prefixEnd_413522 := by exact prefixLift 413522
  have htrace : WordTrace (prefixWord ++ tailWord_413522) baseStart_413522 baseEnd_413522 := by
    simpa [prefixWord, tailWord_413522, baseEnd_413522] using wordTrace_append hprefix tailTrace_413522
  have hstable : (prefixWord ++ tailWord_413522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413522).length < 2 ^ (prefixWord ++ tailWord_413522).sum := by decide
  have hdescent : baseEnd_413522 < baseStart_413522 := by decide
  rcases family_descends (prefixWord ++ tailWord_413522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413539 : List Nat := [1, 1, 1, 5, 5, 1, 7]
def baseStart_413539 : Nat := 118140960795 + 413539 * 2 ^ 59
def prefixEnd_413539 : Nat := 4983230072969 + 3 ^ 40 * 413539 * 2
def baseEnd_413539 : Nat := 10486137105173469652379

theorem tailTrace_413539 : CollatzResearch.WordTrace tailWord_413539 prefixEnd_413539 10486137105173469652379 := by
  unfold tailWord_413539
  simp only [CollatzResearch.WordTrace]
  refine ⟨15083006448826304683419671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10055337632550869788946447 15083006448826304683419671)
  ·
    refine ⟨22624509673239457025129507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15083006448826304683419671 22624509673239457025129507)
    ·
      refine ⟨33936764509859185537694261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22624509673239457025129507 33936764509859185537694261)
      ·
        refine ⟨3181571672799298644158837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33936764509859185537694261 3181571672799298644158837)
        ·
          refine ⟨298272344324934247889891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3181571672799298644158837 298272344324934247889891)
          ·
            refine ⟨447408516487401371834837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298272344324934247889891 447408516487401371834837)
            ·
              refine ⟨10486137105173469652379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 447408516487401371834837 10486137105173469652379)
              ·
                rfl

theorem cell21_413539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 7].length) (baseStart_413539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413539 prefixEnd_413539 := by exact prefixLift 413539
  have htrace : WordTrace (prefixWord ++ tailWord_413539) baseStart_413539 baseEnd_413539 := by
    simpa [prefixWord, tailWord_413539, baseEnd_413539] using wordTrace_append hprefix tailTrace_413539
  have hstable : (prefixWord ++ tailWord_413539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413539).length < 2 ^ (prefixWord ++ tailWord_413539).sum := by decide
  have hdescent : baseEnd_413539 < baseStart_413539 := by decide
  rcases family_descends (prefixWord ++ tailWord_413539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413601 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 4]
def baseStart_413601 : Nat := 118140960795 + 413601 * 2 ^ 59
def prefixEnd_413601 : Nat := 4983230072969 + 3 ^ 40 * 413601 * 2
def baseEnd_413601 : Nat := 94389383191262896837951

theorem tailTrace_413601 : CollatzResearch.WordTrace tailWord_413601 prefixEnd_413601 94389383191262896837951 := by
  unfold tailWord_413601
  simp only [CollatzResearch.WordTrace]
  refine ⟨15085267774601689272176657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10056845183067792848117771 15085267774601689272176657)
  ·
    refine ⟨11313950830951266954132493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15085267774601689272176657 11313950830951266954132493)
    ·
      refine ⟨4242731561606725107799685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11313950830951266954132493 4242731561606725107799685)
      ·
        refine ⟨795512167801260957712441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4242731561606725107799685 795512167801260957712441)
        ·
          refine ⟨596634125850945718284331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795512167801260957712441 596634125850945718284331)
          ·
            refine ⟨894951188776418577426497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596634125850945718284331 894951188776418577426497)
            ·
              refine ⟨671213391582313933069873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894951188776418577426497 671213391582313933069873)
              ·
                refine ⟨503410043686735449802405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671213391582313933069873 503410043686735449802405)
                ·
                  refine ⟨94389383191262896837951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503410043686735449802405 94389383191262896837951)
                  ·
                    rfl

theorem cell21_413601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_413601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413601 prefixEnd_413601 := by exact prefixLift 413601
  have htrace : WordTrace (prefixWord ++ tailWord_413601) baseStart_413601 baseEnd_413601 := by
    simpa [prefixWord, tailWord_413601, baseEnd_413601] using wordTrace_append hprefix tailTrace_413601
  have hstable : (prefixWord ++ tailWord_413601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413601).length < 2 ^ (prefixWord ++ tailWord_413601).sum := by decide
  have hdescent : baseEnd_413601 < baseStart_413601 := by decide
  rcases family_descends (prefixWord ++ tailWord_413601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413629 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 5]
def baseStart_413629 : Nat := 118140960795 + 413629 * 2 ^ 59
def prefixEnd_413629 : Nat := 4983230072969 + 3 ^ 40 * 413629 * 2
def baseEnd_413629 : Nat := 94395773172741070371227

theorem tailTrace_413629 : CollatzResearch.WordTrace tailWord_413629 prefixEnd_413629 94395773172741070371227 := by
  unfold tailWord_413629
  simp only [CollatzResearch.WordTrace]
  refine ⟨15086289018500250054195941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10057526012333500036130627 15086289018500250054195941)
  ·
    refine ⟨2828679190968796885161739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15086289018500250054195941 2828679190968796885161739)
    ·
      refine ⟨4243018786453195327742609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828679190968796885161739 4243018786453195327742609)
      ·
        refine ⟨3182264089839896495806957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4243018786453195327742609 3182264089839896495806957)
        ·
          refine ⟨1193349033689961185927609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3182264089839896495806957 1193349033689961185927609)
          ·
            refine ⟨895011775267470889445707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193349033689961185927609 895011775267470889445707)
            ·
              refine ⟨1342517662901206334168561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895011775267470889445707 1342517662901206334168561)
              ·
                refine ⟨1006888247175904750626421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342517662901206334168561 1006888247175904750626421)
                ·
                  refine ⟨94395773172741070371227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1006888247175904750626421 94395773172741070371227)
                  ·
                    rfl

theorem cell21_413629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_413629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413629 prefixEnd_413629 := by exact prefixLift 413629
  have htrace : WordTrace (prefixWord ++ tailWord_413629) baseStart_413629 baseEnd_413629 := by
    simpa [prefixWord, tailWord_413629, baseEnd_413629] using wordTrace_append hprefix tailTrace_413629
  have hstable : (prefixWord ++ tailWord_413629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413629).length < 2 ^ (prefixWord ++ tailWord_413629).sum := by decide
  have hdescent : baseEnd_413629 < baseStart_413629 := by decide
  rcases family_descends (prefixWord ++ tailWord_413629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413646 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_413646 : Nat := 118140960795 + 413646 * 2 ^ 59
def prefixEnd_413646 : Nat := 4983230072969 + 3 ^ 40 * 413646 * 2
def baseEnd_413646 : Nat := 94399652804352818587859

theorem tailTrace_413646 : CollatzResearch.WordTrace tailWord_413646 prefixEnd_413646 94399652804352818587859 := by
  unfold tailWord_413646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885863632429832744695599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10057939372959107971709861 1885863632429832744695599)
  ·
    refine ⟨2828795448644749117043399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1885863632429832744695599 2828795448644749117043399)
    ·
      refine ⟨4243193172967123675565099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828795448644749117043399 4243193172967123675565099)
      ·
        refine ⟨6364789759450685513347649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243193172967123675565099 6364789759450685513347649)
        ·
          refine ⟨4773592319588014135010737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6364789759450685513347649 4773592319588014135010737)
          ·
            refine ⟨3580194239691010601258053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773592319588014135010737 3580194239691010601258053)
            ·
              refine ⟨671286419942064487735885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3580194239691010601258053 671286419942064487735885)
              ·
                refine ⟨251732407478274182900957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 671286419942064487735885 251732407478274182900957)
                ·
                  refine ⟨94399652804352818587859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251732407478274182900957 94399652804352818587859)
                  ·
                    rfl

theorem cell21_413646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_413646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413646 prefixEnd_413646 := by exact prefixLift 413646
  have htrace : WordTrace (prefixWord ++ tailWord_413646) baseStart_413646 baseEnd_413646 := by
    simpa [prefixWord, tailWord_413646, baseEnd_413646] using wordTrace_append hprefix tailTrace_413646
  have hstable : (prefixWord ++ tailWord_413646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413646).length < 2 ^ (prefixWord ++ tailWord_413646).sum := by decide
  have hdescent : baseEnd_413646 < baseStart_413646 := by decide
  rcases family_descends (prefixWord ++ tailWord_413646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413688 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_413688 : Nat := 118140960795 + 413688 * 2 ^ 59
def prefixEnd_413688 : Nat := 4983230072969 + 3 ^ 40 * 413688 * 2
def baseEnd_413688 : Nat := 94409237776570078887773

theorem tailTrace_413688 : CollatzResearch.WordTrace tailWord_413688 prefixEnd_413688 94409237776570078887773 := by
  unfold tailWord_413688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544220462643251565296859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10058960616857668753729145 7544220462643251565296859)
  ·
    refine ⟨11316330693964877347945289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7544220462643251565296859 11316330693964877347945289)
    ·
      refine ⟨8487248020473658010958967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11316330693964877347945289 8487248020473658010958967)
      ·
        refine ⟨12730872030710487016438451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8487248020473658010958967 12730872030710487016438451)
        ·
          refine ⟨19096308046065730524657677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12730872030710487016438451 19096308046065730524657677)
          ·
            refine ⟨7161115517274648946746629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19096308046065730524657677 7161115517274648946746629)
            ·
              refine ⟨1342709159488996677514993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7161115517274648946746629 1342709159488996677514993)
              ·
                refine ⟨1007031869616747508136245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342709159488996677514993 1007031869616747508136245)
                ·
                  refine ⟨94409237776570078887773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1007031869616747508136245 94409237776570078887773)
                  ·
                    rfl

theorem cell21_413688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_413688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413688 prefixEnd_413688 := by exact prefixLift 413688
  have htrace : WordTrace (prefixWord ++ tailWord_413688) baseStart_413688 baseEnd_413688 := by
    simpa [prefixWord, tailWord_413688, baseEnd_413688] using wordTrace_append hprefix tailTrace_413688
  have hstable : (prefixWord ++ tailWord_413688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413688).length < 2 ^ (prefixWord ++ tailWord_413688).sum := by decide
  have hdescent : baseEnd_413688 < baseStart_413688 := by decide
  rcases family_descends (prefixWord ++ tailWord_413688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413733 : List Nat := [1, 3, 1, 2, 2, 3, 1, 8]
def baseStart_413733 : Nat := 118140960795 + 413733 * 2 ^ 59
def prefixEnd_413733 : Nat := 4983230072969 + 3 ^ 40 * 413733 * 2
def baseEnd_413733 : Nat := 31473169129886666879227

theorem tailTrace_413733 : CollatzResearch.WordTrace tailWord_413733 prefixEnd_413733 31473169129886666879227 := by
  unfold tailWord_413733
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090082210123475815981853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10060054806748983877321235 15090082210123475815981853)
  ·
    refine ⟨5658780828796303430993195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15090082210123475815981853 5658780828796303430993195)
    ·
      refine ⟨8488171243194455146489793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5658780828796303430993195 8488171243194455146489793)
      ·
        refine ⟨6366128432395841359867345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8488171243194455146489793 6366128432395841359867345)
        ·
          refine ⟨4774596324296881019900509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6366128432395841359867345 4774596324296881019900509)
          ·
            refine ⟨1790473621611330382462691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4774596324296881019900509 1790473621611330382462691)
            ·
              refine ⟨2685710432416995573694037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790473621611330382462691 2685710432416995573694037)
              ·
                refine ⟨31473169129886666879227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2685710432416995573694037 31473169129886666879227)
                ·
                  rfl

theorem cell21_413733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_413733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413733 prefixEnd_413733 := by exact prefixLift 413733
  have htrace : WordTrace (prefixWord ++ tailWord_413733) baseStart_413733 baseEnd_413733 := by
    simpa [prefixWord, tailWord_413733, baseEnd_413733] using wordTrace_append hprefix tailTrace_413733
  have hstable : (prefixWord ++ tailWord_413733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413733).length < 2 ^ (prefixWord ++ tailWord_413733).sum := by decide
  have hdescent : baseEnd_413733 < baseStart_413733 := by decide
  rcases family_descends (prefixWord ++ tailWord_413733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413750 : List Nat := [5, 1, 2, 1, 1, 1, 1, 9]
def baseStart_413750 : Nat := 118140960795 + 413750 * 2 ^ 59
def prefixEnd_413750 : Nat := 4983230072969 + 3 ^ 40 * 413750 * 2
def baseEnd_413750 : Nat := 31474462340423916284771

theorem tailTrace_413750 : CollatzResearch.WordTrace tailWord_413750 prefixEnd_413750 31474462340423916284771 := by
  unfold tailWord_413750
  simp only [CollatzResearch.WordTrace]
  refine ⟨943168890691367982459419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10060468167374591812900469 943168890691367982459419)
  ·
    refine ⟨1414753336037051973689129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943168890691367982459419 1414753336037051973689129)
    ·
      refine ⟨1061065002027788980266847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1414753336037051973689129 1061065002027788980266847)
      ·
        refine ⟨1591597503041683470400271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061065002027788980266847 1591597503041683470400271)
        ·
          refine ⟨2387396254562525205600407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591597503041683470400271 2387396254562525205600407)
          ·
            refine ⟨3581094381843787808400611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387396254562525205600407 3581094381843787808400611)
            ·
              refine ⟨5371641572765681712600917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581094381843787808400611 5371641572765681712600917)
              ·
                refine ⟨31474462340423916284771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5371641572765681712600917 31474462340423916284771)
                ·
                  rfl

theorem cell21_413750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_413750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413750 prefixEnd_413750 := by exact prefixLift 413750
  have htrace : WordTrace (prefixWord ++ tailWord_413750) baseStart_413750 baseEnd_413750 := by
    simpa [prefixWord, tailWord_413750, baseEnd_413750] using wordTrace_append hprefix tailTrace_413750
  have hstable : (prefixWord ++ tailWord_413750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413750).length < 2 ^ (prefixWord ++ tailWord_413750).sum := by decide
  have hdescent : baseEnd_413750 < baseStart_413750 := by decide
  rcases family_descends (prefixWord ++ tailWord_413750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413795 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 4]
def baseStart_413795 : Nat := 118140960795 + 413795 * 2 ^ 59
def prefixEnd_413795 : Nat := 4983230072969 + 3 ^ 40 * 413795 * 2
def baseEnd_413795 : Nat := 94433656634361670604221

theorem tailTrace_413795 : CollatzResearch.WordTrace tailWord_413795 prefixEnd_413795 94433656634361670604221 := by
  unfold tailWord_413795
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092343535898860404738839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10061562357265906936492559 15092343535898860404738839)
  ·
    refine ⟨22638515303848290607108259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15092343535898860404738839 22638515303848290607108259)
    ·
      refine ⟨33957772955772435910662389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22638515303848290607108259 33957772955772435910662389)
      ·
        refine ⟨3183541214603665866624599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33957772955772435910662389 3183541214603665866624599)
        ·
          refine ⟨4775311821905498799936899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183541214603665866624599 4775311821905498799936899)
          ·
            refine ⟨7162967732858248199905349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775311821905498799936899 7162967732858248199905349)
            ·
              refine ⟨1343056449910921537482253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7162967732858248199905349 1343056449910921537482253)
              ·
                refine ⟨503646168716595576555845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343056449910921537482253 503646168716595576555845)
                ·
                  refine ⟨94433656634361670604221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503646168716595576555845 94433656634361670604221)
                  ·
                    rfl

theorem cell21_413795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_413795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413795 prefixEnd_413795 := by exact prefixLift 413795
  have htrace : WordTrace (prefixWord ++ tailWord_413795) baseStart_413795 baseEnd_413795 := by
    simpa [prefixWord, tailWord_413795, baseEnd_413795] using wordTrace_append hprefix tailTrace_413795
  have hstable : (prefixWord ++ tailWord_413795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413795).length < 2 ^ (prefixWord ++ tailWord_413795).sum := by decide
  have hdescent : baseEnd_413795 < baseStart_413795 := by decide
  rcases family_descends (prefixWord ++ tailWord_413795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413840 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_413840 : Nat := 118140960795 + 413840 * 2 ^ 59
def prefixEnd_413840 : Nat := 4983230072969 + 3 ^ 40 * 413840 * 2
def baseEnd_413840 : Nat := 94443926247451592354129

theorem tailTrace_413840 : CollatzResearch.WordTrace tailWord_413840 prefixEnd_413840 94443926247451592354129 := by
  unfold tailWord_413840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546992410367916545063487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10062656547157222060084649 7546992410367916545063487)
  ·
    refine ⟨11320488615551874817595231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7546992410367916545063487 11320488615551874817595231)
    ·
      refine ⟨16980732923327812226392847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11320488615551874817595231 16980732923327812226392847)
      ·
        refine ⟨25471099384991718339589271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16980732923327812226392847 25471099384991718339589271)
        ·
          refine ⟨38206649077487577509383907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25471099384991718339589271 38206649077487577509383907)
          ·
            refine ⟨57309973616231366264075861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38206649077487577509383907 57309973616231366264075861)
            ·
              refine ⟨671601253315211323407139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 57309973616231366264075861 671601253315211323407139)
              ·
                refine ⟨1007401879972816985110709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671601253315211323407139 1007401879972816985110709)
                ·
                  refine ⟨94443926247451592354129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1007401879972816985110709 94443926247451592354129)
                  ·
                    rfl

theorem cell21_413840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_413840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413840 prefixEnd_413840 := by exact prefixLift 413840
  have htrace : WordTrace (prefixWord ++ tailWord_413840) baseStart_413840 baseEnd_413840 := by
    simpa [prefixWord, tailWord_413840, baseEnd_413840] using wordTrace_append hprefix tailTrace_413840
  have hstable : (prefixWord ++ tailWord_413840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413840).length < 2 ^ (prefixWord ++ tailWord_413840).sum := by decide
  have hdescent : baseEnd_413840 < baseStart_413840 := by decide
  rcases family_descends (prefixWord ++ tailWord_413840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413860 : List Nat := [2, 3, 1, 2, 5, 1, 2, 5]
def baseStart_413860 : Nat := 118140960795 + 413860 * 2 ^ 59
def prefixEnd_413860 : Nat := 4983230072969 + 3 ^ 40 * 413860 * 2
def baseEnd_413860 : Nat := 31482830173312000673585

theorem tailTrace_413860 : CollatzResearch.WordTrace tailWord_413860 prefixEnd_413860 31482830173312000673585 := by
  unfold tailWord_413860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547357140331688252927517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10063142853775584337236689 7547357140331688252927517)
  ·
    refine ⟨2830258927624383094847819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7547357140331688252927517 2830258927624383094847819)
    ·
      refine ⟨4245388391436574642271729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830258927624383094847819 4245388391436574642271729)
      ·
        refine ⟨3184041293577430981703797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4245388391436574642271729 3184041293577430981703797)
        ·
          refine ⟨298503871272884154534731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3184041293577430981703797 298503871272884154534731)
          ·
            refine ⟨447755806909326231802097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298503871272884154534731 447755806909326231802097)
            ·
              refine ⟨335816855181994673851573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447755806909326231802097 335816855181994673851573)
              ·
                refine ⟨31482830173312000673585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335816855181994673851573 31482830173312000673585)
                ·
                  rfl

theorem cell21_413860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_413860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413860 prefixEnd_413860 := by exact prefixLift 413860
  have htrace : WordTrace (prefixWord ++ tailWord_413860) baseStart_413860 baseEnd_413860 := by
    simpa [prefixWord, tailWord_413860, baseEnd_413860] using wordTrace_append hprefix tailTrace_413860
  have hstable : (prefixWord ++ tailWord_413860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413860).length < 2 ^ (prefixWord ++ tailWord_413860).sum := by decide
  have hdescent : baseEnd_413860 < baseStart_413860 := by decide
  rcases family_descends (prefixWord ++ tailWord_413860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413902 : List Nat := [4, 1, 1, 1, 4, 2, 2, 6]
def baseStart_413902 : Nat := 118140960795 + 413902 * 2 ^ 59
def prefixEnd_413902 : Nat := 4983230072969 + 3 ^ 40 * 413902 * 2
def baseEnd_413902 : Nat := 31486025164051087440223

theorem tailTrace_413902 : CollatzResearch.WordTrace tailWord_413902 prefixEnd_413902 31486025164051087440223 := by
  unfold tailWord_413902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887030768313902209860495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10064164097674145119255973 1887030768313902209860495)
  ·
    refine ⟨2830546152470853314790743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887030768313902209860495 2830546152470853314790743)
    ·
      refine ⟨4245819228706279972186115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830546152470853314790743 4245819228706279972186115)
      ·
        refine ⟨6368728843059419958279173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245819228706279972186115 6368728843059419958279173)
        ·
          refine ⟨1194136658073641242177345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6368728843059419958279173 1194136658073641242177345)
          ·
            refine ⟨895602493555230931633009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194136658073641242177345 895602493555230931633009)
            ·
              refine ⟨671701870166423198724757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895602493555230931633009 671701870166423198724757)
              ·
                refine ⟨31486025164051087440223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 671701870166423198724757 31486025164051087440223)
                ·
                  rfl

theorem cell21_413902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_413902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413902 prefixEnd_413902 := by exact prefixLift 413902
  have htrace : WordTrace (prefixWord ++ tailWord_413902) baseStart_413902 baseEnd_413902 := by
    simpa [prefixWord, tailWord_413902, baseEnd_413902] using wordTrace_append hprefix tailTrace_413902
  have hstable : (prefixWord ++ tailWord_413902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413902).length < 2 ^ (prefixWord ++ tailWord_413902).sum := by decide
  have hdescent : baseEnd_413902 < baseStart_413902 := by decide
  rcases family_descends (prefixWord ++ tailWord_413902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413950 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_413950 : Nat := 118140960795 + 413950 * 2 ^ 59
def prefixEnd_413950 : Nat := 4983230072969 + 3 ^ 40 * 413950 * 2
def baseEnd_413950 : Nat := 94469029746115845520571

theorem tailTrace_413950 : CollatzResearch.WordTrace tailWord_413950 prefixEnd_413950 94469029746115845520571 := by
  unfold tailWord_413950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887249606292165234578913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10065331233558214584420869 1887249606292165234578913)
  ·
    refine ⟨1415437204719123925934185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1887249606292165234578913 1415437204719123925934185)
    ·
      refine ⟨1061577903539342944450639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1415437204719123925934185 1061577903539342944450639)
      ·
        refine ⟨1592366855309014416675959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061577903539342944450639 1592366855309014416675959)
        ·
          refine ⟨2388550282963521625013939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592366855309014416675959 2388550282963521625013939)
          ·
            refine ⟨3582825424445282437520909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388550282963521625013939 3582825424445282437520909)
            ·
              refine ⟨1343559534166980914070341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3582825424445282437520909 1343559534166980914070341)
              ·
                refine ⟨251917412656308921388189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1343559534166980914070341 251917412656308921388189)
                ·
                  refine ⟨94469029746115845520571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251917412656308921388189 94469029746115845520571)
                  ·
                    rfl

theorem cell21_413950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_413950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413950 prefixEnd_413950 := by exact prefixLift 413950
  have htrace : WordTrace (prefixWord ++ tailWord_413950) baseStart_413950 baseEnd_413950 := by
    simpa [prefixWord, tailWord_413950, baseEnd_413950] using wordTrace_append hprefix tailTrace_413950
  have hstable : (prefixWord ++ tailWord_413950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413950).length < 2 ^ (prefixWord ++ tailWord_413950).sum := by decide
  have hdescent : baseEnd_413950 < baseStart_413950 := by decide
  rcases family_descends (prefixWord ++ tailWord_413950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413961 : List Nat := [1, 2, 1, 1, 3, 4, 3, 6]
def baseStart_413961 : Nat := 118140960795 + 413961 * 2 ^ 59
def prefixEnd_413961 : Nat := 4983230072969 + 3 ^ 40 * 413961 * 2
def baseEnd_413961 : Nat := 31490513365327423612405

theorem tailTrace_413961 : CollatzResearch.WordTrace tailWord_413961 prefixEnd_413961 31490513365327423612405 := by
  unfold tailWord_413961
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098398053297470755281737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10065598702198313836854491 15098398053297470755281737)
  ·
    refine ⟨11323798539973103066461303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15098398053297470755281737 11323798539973103066461303)
    ·
      refine ⟨16985697809959654599691955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11323798539973103066461303 16985697809959654599691955)
      ·
        refine ⟨25478546714939481899537933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16985697809959654599691955 25478546714939481899537933)
        ·
          refine ⟨9554455018102305712326725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25478546714939481899537933 9554455018102305712326725)
          ·
            refine ⟨1791460315894182321061261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9554455018102305712326725 1791460315894182321061261)
            ·
              refine ⟨671797618460318370397973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1791460315894182321061261 671797618460318370397973)
              ·
                refine ⟨31490513365327423612405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 671797618460318370397973 31490513365327423612405)
                ·
                  rfl

theorem cell21_413961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 6].length) (baseStart_413961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413961 prefixEnd_413961 := by exact prefixLift 413961
  have htrace : WordTrace (prefixWord ++ tailWord_413961) baseStart_413961 baseEnd_413961 := by
    simpa [prefixWord, tailWord_413961, baseEnd_413961] using wordTrace_append hprefix tailTrace_413961
  have hstable : (prefixWord ++ tailWord_413961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413961).length < 2 ^ (prefixWord ++ tailWord_413961).sum := by decide
  have hdescent : baseEnd_413961 < baseStart_413961 := by decide
  rcases family_descends (prefixWord ++ tailWord_413961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413998 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_413998 : Nat := 118140960795 + 413998 * 2 ^ 59
def prefixEnd_413998 : Nat := 4983230072969 + 3 ^ 40 * 413998 * 2
def baseEnd_413998 : Nat := 94479984000078428720473

theorem tailTrace_413998 : CollatzResearch.WordTrace tailWord_413998 prefixEnd_413998 94479984000078428720473 := by
  unfold tailWord_413998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887468444270428259297331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10066498369442284049585765 1887468444270428259297331)
  ·
    refine ⟨2831202666405642388945997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887468444270428259297331 2831202666405642388945997)
    ·
      refine ⟨1061700999902115895854749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2831202666405642388945997 1061700999902115895854749)
      ·
        refine ⟨398137874963293460945531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1061700999902115895854749 398137874963293460945531)
        ·
          refine ⟨597206812444940191418297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398137874963293460945531 597206812444940191418297)
          ·
            refine ⟨447905109333705143563723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597206812444940191418297 447905109333705143563723)
            ·
              refine ⟨671857664000557715345585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447905109333705143563723 671857664000557715345585)
              ·
                refine ⟨503893248000418286509189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671857664000557715345585 503893248000418286509189)
                ·
                  refine ⟨94479984000078428720473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503893248000418286509189 94479984000078428720473)
                  ·
                    rfl

theorem cell21_413998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_413998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_413998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_413998 prefixEnd_413998 := by exact prefixLift 413998
  have htrace : WordTrace (prefixWord ++ tailWord_413998) baseStart_413998 baseEnd_413998 := by
    simpa [prefixWord, tailWord_413998, baseEnd_413998] using wordTrace_append hprefix tailTrace_413998
  have hstable : (prefixWord ++ tailWord_413998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413998).length < 2 ^ (prefixWord ++ tailWord_413998).sum := by decide
  have hdescent : baseEnd_413998 < baseStart_413998 := by decide
  rcases family_descends (prefixWord ++ tailWord_413998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414009 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 5]
def baseStart_414009 : Nat := 118140960795 + 414009 * 2 ^ 59
def prefixEnd_414009 : Nat := 4983230072969 + 3 ^ 40 * 414009 * 2
def baseEnd_414009 : Nat := 94482494349944854037117

theorem tailTrace_414009 : CollatzResearch.WordTrace tailWord_414009 prefixEnd_414009 94482494349944854037117 := by
  unfold tailWord_414009
  simp only [CollatzResearch.WordTrace]
  refine ⟨15100148757123574953029081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10066765838082383302019387 15100148757123574953029081)
  ·
    refine ⟨11325111567842681214771811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15100148757123574953029081 11325111567842681214771811)
    ·
      refine ⟨16987667351764021822157717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11325111567842681214771811 16987667351764021822157717)
      ·
        refine ⟨796296907113938522913643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16987667351764021822157717 796296907113938522913643)
        ·
          refine ⟨1194445360670907784370465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796296907113938522913643 1194445360670907784370465)
          ·
            refine ⟨895834020503180838277849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194445360670907784370465 895834020503180838277849)
            ·
              refine ⟨671875515377385628708387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895834020503180838277849 671875515377385628708387)
              ·
                refine ⟨1007813273066078443062581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671875515377385628708387 1007813273066078443062581)
                ·
                  refine ⟨94482494349944854037117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1007813273066078443062581 94482494349944854037117)
                  ·
                    rfl

theorem cell21_414009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_414009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414009 prefixEnd_414009 := by exact prefixLift 414009
  have htrace : WordTrace (prefixWord ++ tailWord_414009) baseStart_414009 baseEnd_414009 := by
    simpa [prefixWord, tailWord_414009, baseEnd_414009] using wordTrace_append hprefix tailTrace_414009
  have hstable : (prefixWord ++ tailWord_414009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414009).length < 2 ^ (prefixWord ++ tailWord_414009).sum := by decide
  have hdescent : baseEnd_414009 < baseStart_414009 := by decide
  rcases family_descends (prefixWord ++ tailWord_414009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414046 : List Nat := [4, 4, 2, 1, 2, 1, 7]
def baseStart_414046 : Nat := 118140960795 + 414046 * 2 ^ 59
def prefixEnd_414046 : Nat := 4983230072969 + 3 ^ 40 * 414046 * 2
def baseEnd_414046 : Nat := 10498993139337890213375

theorem tailTrace_414046 : CollatzResearch.WordTrace tailWord_414046 prefixEnd_414046 10498993139337890213375 := by
  unfold tailWord_414046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887687282248691284015749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10067665505326353514750661 1887687282248691284015749)
  ·
    refine ⟨353941365421629615752953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1887687282248691284015749 353941365421629615752953)
    ·
      refine ⟨265456024066222211814715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353941365421629615752953 265456024066222211814715)
      ·
        refine ⟨398184036099333317722073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265456024066222211814715 398184036099333317722073)
        ·
          refine ⟨298638027074499988291555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398184036099333317722073 298638027074499988291555)
          ·
            refine ⟨447957040611749982437333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298638027074499988291555 447957040611749982437333)
            ·
              refine ⟨10498993139337890213375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 447957040611749982437333 10498993139337890213375)
              ·
                rfl

theorem cell21_414046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 7].length) (baseStart_414046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414046 prefixEnd_414046 := by exact prefixLift 414046
  have htrace : WordTrace (prefixWord ++ tailWord_414046) baseStart_414046 baseEnd_414046 := by
    simpa [prefixWord, tailWord_414046, baseEnd_414046] using wordTrace_append hprefix tailTrace_414046
  have hstable : (prefixWord ++ tailWord_414046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414046).length < 2 ^ (prefixWord ++ tailWord_414046).sum := by decide
  have hdescent : baseEnd_414046 < baseStart_414046 := by decide
  rcases family_descends (prefixWord ++ tailWord_414046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414113 : List Nat := [1, 2, 3, 5, 10]
def baseStart_414113 : Nat := 118140960795 + 414113 * 2 ^ 59
def prefixEnd_414113 : Nat := 4983230072969 + 3 ^ 40 * 414113 * 2
def baseEnd_414113 : Nat := 1166743562553873880291

theorem tailTrace_414113 : CollatzResearch.WordTrace tailWord_414113 prefixEnd_414113 1166743562553873880291 := by
  unfold tailWord_414113
  simp only [CollatzResearch.WordTrace]
  refine ⟨15103941948746800714814993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10069294632497867143209995 15103941948746800714814993)
  ·
    refine ⟨11327956461560100536111245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15103941948746800714814993 11327956461560100536111245)
    ·
      refine ⟨4247983673085037701041717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11327956461560100536111245 4247983673085037701041717)
      ·
        refine ⟨398248469351722284472661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4247983673085037701041717 398248469351722284472661)
        ·
          refine ⟨1166743562553873880291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 398248469351722284472661 1166743562553873880291)
          ·
            rfl

theorem cell21_414113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 10].length) (baseStart_414113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414113 prefixEnd_414113 := by exact prefixLift 414113
  have htrace : WordTrace (prefixWord ++ tailWord_414113) baseStart_414113 baseEnd_414113 := by
    simpa [prefixWord, tailWord_414113, baseEnd_414113] using wordTrace_append hprefix tailTrace_414113
  have hstable : (prefixWord ++ tailWord_414113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414113).length < 2 ^ (prefixWord ++ tailWord_414113).sum := by decide
  have hdescent : baseEnd_414113 < baseStart_414113 := by decide
  rcases family_descends (prefixWord ++ tailWord_414113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414119 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 3]
def baseStart_414119 : Nat := 118140960795 + 414119 * 2 ^ 59
def prefixEnd_414119 : Nat := 4983230072969 + 3 ^ 40 * 414119 * 2
def baseEnd_414119 : Nat := 94507597848609107203559

theorem tailTrace_414119 : CollatzResearch.WordTrace tailWord_414119 prefixEnd_414119 94507597848609107203559 := by
  unfold tailWord_414119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104160786725063739533411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10069440524483375826355607 15104160786725063739533411)
  ·
    refine ⟨22656241180087595609300117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15104160786725063739533411 22656241180087595609300117)
    ·
      refine ⟨1062011305316606044185943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22656241180087595609300117 1062011305316606044185943)
      ·
        refine ⟨1593016957974909066278915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062011305316606044185943 1593016957974909066278915)
        ·
          refine ⟨2389525436962363599418373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593016957974909066278915 2389525436962363599418373)
          ·
            refine ⟨448036019430443174890945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2389525436962363599418373 448036019430443174890945)
            ·
              refine ⟨336027014572832381168209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448036019430443174890945 336027014572832381168209)
              ·
                refine ⟨252020260929624285876157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336027014572832381168209 252020260929624285876157)
                ·
                  refine ⟨94507597848609107203559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252020260929624285876157 94507597848609107203559)
                  ·
                    rfl

theorem cell21_414119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 3].length) (baseStart_414119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414119 prefixEnd_414119 := by exact prefixLift 414119
  have htrace : WordTrace (prefixWord ++ tailWord_414119) baseStart_414119 baseEnd_414119 := by
    simpa [prefixWord, tailWord_414119, baseEnd_414119] using wordTrace_append hprefix tailTrace_414119
  have hstable : (prefixWord ++ tailWord_414119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414119).length < 2 ^ (prefixWord ++ tailWord_414119).sum := by decide
  have hdescent : baseEnd_414119 < baseStart_414119 := by decide
  rcases family_descends (prefixWord ++ tailWord_414119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414158 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_414158 : Nat := 118140960795 + 414158 * 2 ^ 59
def prefixEnd_414158 : Nat := 4983230072969 + 3 ^ 40 * 414158 * 2
def baseEnd_414158 : Nat := 94516498179953706053479

theorem tailTrace_414158 : CollatzResearch.WordTrace tailWord_414158 prefixEnd_414158 94516498179953706053479 := by
  unfold tailWord_414158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888197904197971675025391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10070388822389182266802085 1888197904197971675025391)
  ·
    refine ⟨2832296856296957512538087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888197904197971675025391 2832296856296957512538087)
    ·
      refine ⟨4248445284445436268807131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832296856296957512538087 4248445284445436268807131)
      ·
        refine ⟨6372667926668154403210697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248445284445436268807131 6372667926668154403210697)
        ·
          refine ⟨4779500945001115802408023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6372667926668154403210697 4779500945001115802408023)
          ·
            refine ⟨7169251417501673703612035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779500945001115802408023 7169251417501673703612035)
            ·
              refine ⟨10753877126252510555418053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169251417501673703612035 10753877126252510555418053)
              ·
                refine ⟨2016351961172345729140885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10753877126252510555418053 2016351961172345729140885)
                ·
                  refine ⟨94516498179953706053479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2016351961172345729140885 94516498179953706053479)
                  ·
                    rfl

theorem cell21_414158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_414158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414158 prefixEnd_414158 := by exact prefixLift 414158
  have htrace : WordTrace (prefixWord ++ tailWord_414158) baseStart_414158 baseEnd_414158 := by
    simpa [prefixWord, tailWord_414158, baseEnd_414158] using wordTrace_append hprefix tailTrace_414158
  have hstable : (prefixWord ++ tailWord_414158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414158).length < 2 ^ (prefixWord ++ tailWord_414158).sum := by decide
  have hdescent : baseEnd_414158 < baseStart_414158 := by decide
  rcases family_descends (prefixWord ++ tailWord_414158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414175 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 4]
def baseStart_414175 : Nat := 118140960795 + 414175 * 2 ^ 59
def prefixEnd_414175 : Nat := 4983230072969 + 3 ^ 40 * 414175 * 2
def baseEnd_414175 : Nat := 94520377811565454270111

theorem tailTrace_414175 : CollatzResearch.WordTrace tailWord_414175 prefixEnd_414175 94520377811565454270111 := by
  unfold tailWord_414175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106203274522185303571979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10070802183014790202381319 15106203274522185303571979)
  ·
    refine ⟨22659304911783277955357969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15106203274522185303571979 22659304911783277955357969)
    ·
      refine ⟨16994478683837458466518477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22659304911783277955357969 16994478683837458466518477)
      ·
        refine ⟨6372929506439046924944429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16994478683837458466518477 6372929506439046924944429)
        ·
          refine ⟨2389848564914642596854161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6372929506439046924944429 2389848564914642596854161)
          ·
            refine ⟨1792386423685981947640621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2389848564914642596854161 1792386423685981947640621)
            ·
              refine ⟨672144908882243230365233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1792386423685981947640621 672144908882243230365233)
              ·
                refine ⟨504108681661682422773925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672144908882243230365233 504108681661682422773925)
                ·
                  refine ⟨94520377811565454270111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504108681661682422773925 94520377811565454270111)
                  ·
                    rfl

theorem cell21_414175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_414175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414175 prefixEnd_414175 := by exact prefixLift 414175
  have htrace : WordTrace (prefixWord ++ tailWord_414175) baseStart_414175 baseEnd_414175 := by
    simpa [prefixWord, tailWord_414175, baseEnd_414175] using wordTrace_append hprefix tailTrace_414175
  have hstable : (prefixWord ++ tailWord_414175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414175).length < 2 ^ (prefixWord ++ tailWord_414175).sum := by decide
  have hdescent : baseEnd_414175 < baseStart_414175 := by decide
  rcases family_descends (prefixWord ++ tailWord_414175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414234 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_414234 : Nat := 118140960795 + 414234 * 2 ^ 59
def prefixEnd_414234 : Nat := 4983230072969 + 3 ^ 40 * 414234 * 2
def baseEnd_414234 : Nat := 94533842415394462786657

theorem tailTrace_414234 : CollatzResearch.WordTrace tailWord_414234 prefixEnd_414234 94533842415394462786657 := by
  unfold tailWord_414234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777088795327109594992439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10072236787538958919979837 3777088795327109594992439)
  ·
    refine ⟨5665633192990664392488659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3777088795327109594992439 5665633192990664392488659)
    ·
      refine ⟨8498449789485996588732989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5665633192990664392488659 8498449789485996588732989)
      ·
        refine ⟨3186918671057248720774871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8498449789485996588732989 3186918671057248720774871)
        ·
          refine ⟨4780378006585873081162307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186918671057248720774871 4780378006585873081162307)
          ·
            refine ⟨7170567009878809621743461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780378006585873081162307 7170567009878809621743461)
            ·
              refine ⟨1344481314352276804076899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7170567009878809621743461 1344481314352276804076899)
              ·
                refine ⟨2016721971528415206115349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344481314352276804076899 2016721971528415206115349)
                ·
                  refine ⟨94533842415394462786657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2016721971528415206115349 94533842415394462786657)
                  ·
                    rfl

theorem cell21_414234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_414234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414234 prefixEnd_414234 := by exact prefixLift 414234
  have htrace : WordTrace (prefixWord ++ tailWord_414234) baseStart_414234 baseEnd_414234 := by
    simpa [prefixWord, tailWord_414234, baseEnd_414234] using wordTrace_append hprefix tailTrace_414234
  have hstable : (prefixWord ++ tailWord_414234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414234).length < 2 ^ (prefixWord ++ tailWord_414234).sum := by decide
  have hdescent : baseEnd_414234 < baseStart_414234 := by decide
  rcases family_descends (prefixWord ++ tailWord_414234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414237 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 5]
def baseStart_414237 : Nat := 118140960795 + 414237 * 2 ^ 59
def prefixEnd_414237 : Nat := 4983230072969 + 3 ^ 40 * 414237 * 2
def baseEnd_414237 : Nat := 94534527056267124236651

theorem tailTrace_414237 : CollatzResearch.WordTrace tailWord_414237 prefixEnd_414237 94534527056267124236651 := by
  unfold tailWord_414237
  simp only [CollatzResearch.WordTrace]
  refine ⟨15108464600297569892328965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10072309733531713261552643 15108464600297569892328965)
  ·
    refine ⟨2832837112555794354811681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15108464600297569892328965 2832837112555794354811681)
    ·
      refine ⟨2124627834416845766108761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2832837112555794354811681 2124627834416845766108761)
      ·
        refine ⟨1593470875812634324581571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2124627834416845766108761 1593470875812634324581571)
        ·
          refine ⟨2390206313718951486872357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593470875812634324581571 2390206313718951486872357)
          ·
            refine ⟨448163683822303403788567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2390206313718951486872357 448163683822303403788567)
            ·
              refine ⟨672245525733455105682851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448163683822303403788567 672245525733455105682851)
              ·
                refine ⟨1008368288600182658524277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672245525733455105682851 1008368288600182658524277)
                ·
                  refine ⟨94534527056267124236651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1008368288600182658524277 94534527056267124236651)
                  ·
                    rfl

theorem cell21_414237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_414237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414237 prefixEnd_414237 := by exact prefixLift 414237
  have htrace : WordTrace (prefixWord ++ tailWord_414237) baseStart_414237 baseEnd_414237 := by
    simpa [prefixWord, tailWord_414237, baseEnd_414237] using wordTrace_append hprefix tailTrace_414237
  have hstable : (prefixWord ++ tailWord_414237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414237).length < 2 ^ (prefixWord ++ tailWord_414237).sum := by decide
  have hdescent : baseEnd_414237 < baseStart_414237 := by decide
  rcases family_descends (prefixWord ++ tailWord_414237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414400 : List Nat := [2, 1, 1, 2, 4, 2, 9]
def baseStart_414400 : Nat := 118140960795 + 414400 * 2 ^ 59
def prefixEnd_414400 : Nat := 4983230072969 + 3 ^ 40 * 414400 * 2
def baseEnd_414400 : Nat := 10507969541890562557739

theorem tailTrace_414400 : CollatzResearch.WordTrace tailWord_414400 prefixEnd_414400 10507969541890562557739 := by
  unfold tailWord_414400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557204849353524365256327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10076273132471365820341769 7557204849353524365256327)
  ·
    refine ⟨11335807274030286547884491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7557204849353524365256327 11335807274030286547884491)
    ·
      refine ⟨17003710911045429821826737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335807274030286547884491 17003710911045429821826737)
      ·
        refine ⟨12752783183284072366370053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17003710911045429821826737 12752783183284072366370053)
        ·
          refine ⟨2391146846865763568694385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12752783183284072366370053 2391146846865763568694385)
          ·
            refine ⟨1793360135149322676520789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391146846865763568694385 1793360135149322676520789)
            ·
              refine ⟨10507969541890562557739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1793360135149322676520789 10507969541890562557739)
              ·
                rfl

theorem cell21_414400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 9].length) (baseStart_414400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414400 prefixEnd_414400 := by exact prefixLift 414400
  have htrace : WordTrace (prefixWord ++ tailWord_414400) baseStart_414400 baseEnd_414400 := by
    simpa [prefixWord, tailWord_414400, baseEnd_414400] using wordTrace_append hprefix tailTrace_414400
  have hstable : (prefixWord ++ tailWord_414400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414400).length < 2 ^ (prefixWord ++ tailWord_414400).sum := by decide
  have hdescent : baseEnd_414400 < baseStart_414400 := by decide
  rcases family_descends (prefixWord ++ tailWord_414400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414420 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_414420 : Nat := 118140960795 + 414420 * 2 ^ 59
def prefixEnd_414420 : Nat := 4983230072969 + 3 ^ 40 * 414420 * 2
def baseEnd_414420 : Nat := 94576290149499472686277

theorem tailTrace_414420 : CollatzResearch.WordTrace tailWord_414420 prefixEnd_414420 94576290149499472686277 := by
  unfold tailWord_414420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557569579317296073120357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10076759439089728097493809 7557569579317296073120357)
  ·
    refine ⟨1417044296121993013710067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7557569579317296073120357 1417044296121993013710067)
    ·
      refine ⟨2125566444182989520565101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1417044296121993013710067 2125566444182989520565101)
      ·
        refine ⟨797087416568621070211913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2125566444182989520565101 797087416568621070211913)
        ·
          refine ⟨597815562426465802658935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797087416568621070211913 597815562426465802658935)
          ·
            refine ⟨896723343639698703988403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597815562426465802658935 896723343639698703988403)
            ·
              refine ⟨1345085015459548055982605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896723343639698703988403 1345085015459548055982605)
              ·
                refine ⟨504406880797330520993477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1345085015459548055982605 504406880797330520993477)
                ·
                  refine ⟨94576290149499472686277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504406880797330520993477 94576290149499472686277)
                  ·
                    rfl

theorem cell21_414420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_414420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414420 prefixEnd_414420 := by exact prefixLift 414420
  have htrace : WordTrace (prefixWord ++ tailWord_414420) baseStart_414420 baseEnd_414420 := by
    simpa [prefixWord, tailWord_414420, baseEnd_414420] using wordTrace_append hprefix tailTrace_414420
  have hstable : (prefixWord ++ tailWord_414420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414420).length < 2 ^ (prefixWord ++ tailWord_414420).sum := by decide
  have hdescent : baseEnd_414420 < baseStart_414420 := by decide
  rcases family_descends (prefixWord ++ tailWord_414420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414448 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_414448 : Nat := 118140960795 + 414448 * 2 ^ 59
def prefixEnd_414448 : Nat := 4983230072969 + 3 ^ 40 * 414448 * 2
def baseEnd_414448 : Nat := 94582680130977646219553

theorem tailTrace_414448 : CollatzResearch.WordTrace tailWord_414448 prefixEnd_414448 94582680130977646219553 := by
  unfold tailWord_414448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558080201266576464129999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10077440268355435285506665 7558080201266576464129999)
  ·
    refine ⟨11337120301899864696194999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7558080201266576464129999 11337120301899864696194999)
    ·
      refine ⟨17005680452849797044292499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11337120301899864696194999 17005680452849797044292499)
      ·
        refine ⟨25508520679274695566438749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17005680452849797044292499 25508520679274695566438749)
        ·
          refine ⟨9565695254728010837414531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25508520679274695566438749 9565695254728010837414531)
          ·
            refine ⟨14348542882092016256121797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9565695254728010837414531 14348542882092016256121797)
            ·
              refine ⟨2690351790392253048022837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14348542882092016256121797 2690351790392253048022837)
              ·
                refine ⟨252220480349273723252141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2690351790392253048022837 252220480349273723252141)
                ·
                  refine ⟨94582680130977646219553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252220480349273723252141 94582680130977646219553)
                  ·
                    rfl

theorem cell21_414448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_414448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414448 prefixEnd_414448 := by exact prefixLift 414448
  have htrace : WordTrace (prefixWord ++ tailWord_414448) baseStart_414448 baseEnd_414448 := by
    simpa [prefixWord, tailWord_414448, baseEnd_414448] using wordTrace_append hprefix tailTrace_414448
  have hstable : (prefixWord ++ tailWord_414448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414448).length < 2 ^ (prefixWord ++ tailWord_414448).sum := by decide
  have hdescent : baseEnd_414448 < baseStart_414448 := by decide
  rcases family_descends (prefixWord ++ tailWord_414448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414673 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_414673 : Nat := 118140960795 + 414673 * 2 ^ 59
def prefixEnd_414673 : Nat := 4983230072969 + 3 ^ 40 * 414673 * 2
def baseEnd_414673 : Nat := 94634028196427254969093

theorem tailTrace_414673 : CollatzResearch.WordTrace tailWord_414673 prefixEnd_414673 94634028196427254969093 := by
  unfold tailWord_414673
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124366826718016355200673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10082911217812010903467115 15124366826718016355200673)
  ·
    refine ⟨11343275120038512266400505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15124366826718016355200673 11343275120038512266400505)
    ·
      refine ⟨8507456340028884199800379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11343275120038512266400505 8507456340028884199800379)
      ·
        refine ⟨12761184510043326299700569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507456340028884199800379 12761184510043326299700569)
        ·
          refine ⟨9570888382532494724775427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12761184510043326299700569 9570888382532494724775427)
          ·
            refine ⟨14356332573798742087163141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570888382532494724775427 14356332573798742087163141)
            ·
              refine ⟨2691812357587264141343089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14356332573798742087163141 2691812357587264141343089)
              ·
                refine ⟨2018859268190448106007317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2691812357587264141343089 2018859268190448106007317)
                ·
                  refine ⟨94634028196427254969093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2018859268190448106007317 94634028196427254969093)
                  ·
                    rfl

theorem cell21_414673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_414673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414673 prefixEnd_414673 := by exact prefixLift 414673
  have htrace : WordTrace (prefixWord ++ tailWord_414673) baseStart_414673 baseEnd_414673 := by
    simpa [prefixWord, tailWord_414673, baseEnd_414673] using wordTrace_append hprefix tailTrace_414673
  have hstable : (prefixWord ++ tailWord_414673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414673).length < 2 ^ (prefixWord ++ tailWord_414673).sum := by decide
  have hdescent : baseEnd_414673 < baseStart_414673 := by decide
  rcases family_descends (prefixWord ++ tailWord_414673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414693 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 5]
def baseStart_414693 : Nat := 118140960795 + 414693 * 2 ^ 59
def prefixEnd_414693 : Nat := 4983230072969 + 3 ^ 40 * 414693 * 2
def baseEnd_414693 : Nat := 94638592468911664635719

theorem tailTrace_414693 : CollatzResearch.WordTrace tailWord_414693 prefixEnd_414693 94638592468911664635719 := by
  unfold tailWord_414693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125096286645559770928733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10083397524430373180619155 15125096286645559770928733)
  ·
    refine ⟨5671911107492084914098275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15125096286645559770928733 5671911107492084914098275)
    ·
      refine ⟨8507866661238127371147413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5671911107492084914098275 8507866661238127371147413)
      ·
        refine ⟨398806249745537220522535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8507866661238127371147413 398806249745537220522535)
        ·
          refine ⟨598209374618305830783803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398806249745537220522535 598209374618305830783803)
          ·
            refine ⟨897314061927458746175705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598209374618305830783803 897314061927458746175705)
            ·
              refine ⟨672985546445594059631779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897314061927458746175705 672985546445594059631779)
              ·
                refine ⟨1009478319668391089447669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672985546445594059631779 1009478319668391089447669)
                ·
                  refine ⟨94638592468911664635719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1009478319668391089447669 94638592468911664635719)
                  ·
                    rfl

theorem cell21_414693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_414693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414693 prefixEnd_414693 := by exact prefixLift 414693
  have htrace : WordTrace (prefixWord ++ tailWord_414693) baseStart_414693 baseEnd_414693 := by
    simpa [prefixWord, tailWord_414693, baseEnd_414693] using wordTrace_append hprefix tailTrace_414693
  have hstable : (prefixWord ++ tailWord_414693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414693).length < 2 ^ (prefixWord ++ tailWord_414693).sum := by decide
  have hdescent : baseEnd_414693 < baseStart_414693 := by decide
  rcases family_descends (prefixWord ++ tailWord_414693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414721 : List Nat := [1, 2, 4, 1, 2, 2, 4, 5]
def baseStart_414721 : Nat := 118140960795 + 414721 * 2 ^ 59
def prefixEnd_414721 : Nat := 4983230072969 + 3 ^ 40 * 414721 * 2
def baseEnd_414721 : Nat := 31548327483463279389665

theorem tailTrace_414721 : CollatzResearch.WordTrace tailWord_414721 prefixEnd_414721 31548327483463279389665 := by
  unfold tailWord_414721
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126117530544120552948017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10084078353696080368632011 15126117530544120552948017)
  ·
    refine ⟨11344588147908090414711013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15126117530544120552948017 11344588147908090414711013)
    ·
      refine ⟨2127110277732766952758315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11344588147908090414711013 2127110277732766952758315)
      ·
        refine ⟨3190665416599150429137473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127110277732766952758315 3190665416599150429137473)
        ·
          refine ⟨2392999062449362821853105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3190665416599150429137473 2392999062449362821853105)
          ·
            refine ⟨1794749296837022116389829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392999062449362821853105 1794749296837022116389829)
            ·
              refine ⟨336515493156941646823093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1794749296837022116389829 336515493156941646823093)
              ·
                refine ⟨31548327483463279389665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336515493156941646823093 31548327483463279389665)
                ·
                  rfl

theorem cell21_414721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 5].length) (baseStart_414721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414721 prefixEnd_414721 := by exact prefixLift 414721
  have htrace : WordTrace (prefixWord ++ tailWord_414721) baseStart_414721 baseEnd_414721 := by
    simpa [prefixWord, tailWord_414721, baseEnd_414721] using wordTrace_append hprefix tailTrace_414721
  have hstable : (prefixWord ++ tailWord_414721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414721).length < 2 ^ (prefixWord ++ tailWord_414721).sum := by decide
  have hdescent : baseEnd_414721 < baseStart_414721 := by decide
  rcases family_descends (prefixWord ++ tailWord_414721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414780 : List Nat := [2, 2, 2, 2, 2, 2, 2, 7]
def baseStart_414780 : Nat := 118140960795 + 414780 * 2 ^ 59
def prefixEnd_414780 : Nat := 4983230072969 + 3 ^ 40 * 414780 * 2
def baseEnd_414780 : Nat := 31552815684739615561847

theorem tailTrace_414780 : CollatzResearch.WordTrace tailWord_414780 prefixEnd_414780 31552815684739615561847 := by
  unfold tailWord_414780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564134718665186814672897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10085512958220249086230529 7564134718665186814672897)
  ·
    refine ⟨5673101038998890111004673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7564134718665186814672897 5673101038998890111004673)
    ·
      refine ⟨4254825779249167583253505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5673101038998890111004673 4254825779249167583253505)
      ·
        refine ⟨3191119334436875687440129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4254825779249167583253505 3191119334436875687440129)
        ·
          refine ⟨2393339500827656765580097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3191119334436875687440129 2393339500827656765580097)
          ·
            refine ⟨1795004625620742574185073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393339500827656765580097 1795004625620742574185073)
            ·
              refine ⟨1346253469215556930638805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795004625620742574185073 1346253469215556930638805)
              ·
                refine ⟨31552815684739615561847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1346253469215556930638805 31552815684739615561847)
                ·
                  rfl

theorem cell21_414780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_414780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414780 prefixEnd_414780 := by exact prefixLift 414780
  have htrace : WordTrace (prefixWord ++ tailWord_414780) baseStart_414780 baseEnd_414780 := by
    simpa [prefixWord, tailWord_414780, baseEnd_414780] using wordTrace_append hprefix tailTrace_414780
  have hstable : (prefixWord ++ tailWord_414780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414780).length < 2 ^ (prefixWord ++ tailWord_414780).sum := by decide
  have hdescent : baseEnd_414780 < baseStart_414780 := by decide
  rcases family_descends (prefixWord ++ tailWord_414780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414890 : List Nat := [3, 1, 5, 1, 1, 1, 4, 5]
def baseStart_414890 : Nat := 118140960795 + 414890 * 2 ^ 59
def prefixEnd_414890 : Nat := 4983230072969 + 3 ^ 40 * 414890 * 2
def baseEnd_414890 : Nat := 31561183517627699950661

theorem tailTrace_414890 : CollatzResearch.WordTrace tailWord_414890 prefixEnd_414890 31561183517627699950661 := by
  unfold tailWord_414890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3783070366732965603962531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10088187644621241610566749 3783070366732965603962531)
  ·
    refine ⟨5674605550099448405943797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3783070366732965603962531 5674605550099448405943797)
    ·
      refine ⟨531994270321823288057231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5674605550099448405943797 531994270321823288057231)
      ·
        refine ⟨797991405482734932085847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531994270321823288057231 797991405482734932085847)
        ·
          refine ⟨1196987108224102398128771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797991405482734932085847 1196987108224102398128771)
          ·
            refine ⟨1795480662336153597193157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196987108224102398128771 1795480662336153597193157)
            ·
              refine ⟨336652624188028799473717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1795480662336153597193157 336652624188028799473717)
              ·
                refine ⟨31561183517627699950661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336652624188028799473717 31561183517627699950661)
                ·
                  rfl

theorem cell21_414890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_414890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_414890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_414890 prefixEnd_414890 := by exact prefixLift 414890
  have htrace : WordTrace (prefixWord ++ tailWord_414890) baseStart_414890 baseEnd_414890 := by
    simpa [prefixWord, tailWord_414890, baseEnd_414890] using wordTrace_append hprefix tailTrace_414890
  have hstable : (prefixWord ++ tailWord_414890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414890).length < 2 ^ (prefixWord ++ tailWord_414890).sum := by decide
  have hdescent : baseEnd_414890 < baseStart_414890 := by decide
  rcases family_descends (prefixWord ++ tailWord_414890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415039 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 5]
def baseStart_415039 : Nat := 118140960795 + 415039 * 2 ^ 59
def prefixEnd_415039 : Nat := 4983230072969 + 3 ^ 40 * 415039 * 2
def baseEnd_415039 : Nat := 94717554382891951868345

theorem tailTrace_415039 : CollatzResearch.WordTrace tailWord_415039 prefixEnd_415039 94717554382891951868345 := by
  unfold tailWord_415039
  simp only [CollatzResearch.WordTrace]
  refine ⟨15137715943392060863024171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10091810628928040575349447 15137715943392060863024171)
  ·
    refine ⟨22706573915088091294536257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15137715943392060863024171 22706573915088091294536257)
    ·
      refine ⟨17029930436316068470902193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22706573915088091294536257 17029930436316068470902193)
      ·
        refine ⟨12772447827237051353176645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17029930436316068470902193 12772447827237051353176645)
        ·
          refine ⟨2394833967606947128720621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12772447827237051353176645 2394833967606947128720621)
          ·
            refine ⟨898062737852605173270233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2394833967606947128720621 898062737852605173270233)
            ·
              refine ⟨673547053389453879952675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898062737852605173270233 673547053389453879952675)
              ·
                refine ⟨1010320580084180819929013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673547053389453879952675 1010320580084180819929013)
                ·
                  refine ⟨94717554382891951868345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1010320580084180819929013 94717554382891951868345)
                  ·
                    rfl

theorem cell21_415039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_415039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415039 prefixEnd_415039 := by exact prefixLift 415039
  have htrace : WordTrace (prefixWord ++ tailWord_415039) baseStart_415039 baseEnd_415039 := by
    simpa [prefixWord, tailWord_415039, baseEnd_415039] using wordTrace_append hprefix tailTrace_415039
  have hstable : (prefixWord ++ tailWord_415039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415039).length < 2 ^ (prefixWord ++ tailWord_415039).sum := by decide
  have hdescent : baseEnd_415039 < baseStart_415039 := by decide
  rcases family_descends (prefixWord ++ tailWord_415039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415084 : List Nat := [2, 2, 1, 1, 5, 3, 7]
def baseStart_415084 : Nat := 118140960795 + 415084 * 2 ^ 59
def prefixEnd_415084 : Nat := 4983230072969 + 3 ^ 40 * 415084 * 2
def baseEnd_415084 : Nat := 10525313777331319290917

theorem tailTrace_415084 : CollatzResearch.WordTrace tailWord_415084 prefixEnd_415084 10525313777331319290917 := by
  unfold tailWord_415084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569678614114516774206153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10092904818819355698941537 7569678614114516774206153)
  ·
    refine ⟨5677258960585887580654615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7569678614114516774206153 5677258960585887580654615)
    ·
      refine ⟨8515888440878831370981923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5677258960585887580654615 8515888440878831370981923)
      ·
        refine ⟨12773832661318247056472885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8515888440878831370981923 12773832661318247056472885)
        ·
          refine ⟨1197546811998585661544333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12773832661318247056472885 1197546811998585661544333)
          ·
            refine ⟨449080054499469623079125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1197546811998585661544333 449080054499469623079125)
            ·
              refine ⟨10525313777331319290917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 449080054499469623079125 10525313777331319290917)
              ·
                rfl

theorem cell21_415084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 7].length) (baseStart_415084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415084 prefixEnd_415084 := by exact prefixLift 415084
  have htrace : WordTrace (prefixWord ++ tailWord_415084) baseStart_415084 baseEnd_415084 := by
    simpa [prefixWord, tailWord_415084, baseEnd_415084] using wordTrace_append hprefix tailTrace_415084
  have hstable : (prefixWord ++ tailWord_415084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415084).length < 2 ^ (prefixWord ++ tailWord_415084).sum := by decide
  have hdescent : baseEnd_415084 < baseStart_415084 := by decide
  rcases family_descends (prefixWord ++ tailWord_415084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415149 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 3]
def baseStart_415149 : Nat := 118140960795 + 415149 * 2 ^ 59
def prefixEnd_415149 : Nat := 4983230072969 + 3 ^ 40 * 415149 * 2
def baseEnd_415149 : Nat := 94742657881556205034787

theorem tailTrace_415149 : CollatzResearch.WordTrace tailWord_415149 prefixEnd_415149 94742657881556205034787 := by
  unfold tailWord_415149
  simp only [CollatzResearch.WordTrace]
  refine ⟨15141727972993549649528501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10094485315329033099685667 15141727972993549649528501)
  ·
    refine ⟨1419536997468145279643297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15141727972993549649528501 1419536997468145279643297)
    ·
      refine ⟨1064652748101108959732473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1419536997468145279643297 1064652748101108959732473)
      ·
        refine ⟨798489561075831719799355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064652748101108959732473 798489561075831719799355)
        ·
          refine ⟨1197734341613747579699033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798489561075831719799355 1197734341613747579699033)
          ·
            refine ⟨898300756210310684774275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197734341613747579699033 898300756210310684774275)
            ·
              refine ⟨1347451134315466027161413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898300756210310684774275 1347451134315466027161413)
              ·
                refine ⟨252647087684149880092765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1347451134315466027161413 252647087684149880092765)
                ·
                  refine ⟨94742657881556205034787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252647087684149880092765 94742657881556205034787)
                  ·
                    rfl

theorem cell21_415149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_415149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415149 prefixEnd_415149 := by exact prefixLift 415149
  have htrace : WordTrace (prefixWord ++ tailWord_415149) baseStart_415149 baseEnd_415149 := by
    simpa [prefixWord, tailWord_415149, baseEnd_415149] using wordTrace_append hprefix tailTrace_415149
  have hstable : (prefixWord ++ tailWord_415149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415149).length < 2 ^ (prefixWord ++ tailWord_415149).sum := by decide
  have hdescent : baseEnd_415149 < baseStart_415149 := by decide
  rcases family_descends (prefixWord ++ tailWord_415149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415295 : List Nat := [1, 1, 2, 2, 3, 3, 2, 7]
def baseStart_415295 : Nat := 118140960795 + 415295 * 2 ^ 59
def prefixEnd_415295 : Nat := 4983230072969 + 3 ^ 40 * 415295 * 2
def baseEnd_415295 : Nat := 31591992356897465200385

theorem tailTrace_415295 : CollatzResearch.WordTrace tailWord_415295 prefixEnd_415295 31591992356897465200385 := by
  unfold tailWord_415295
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147053030464616584343339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10098035353643077722895559 15147053030464616584343339)
  ·
    refine ⟨22720579545696924876515009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15147053030464616584343339 22720579545696924876515009)
    ·
      refine ⟨17040434659272693657386257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22720579545696924876515009 17040434659272693657386257)
      ·
        refine ⟨12780325994454520243039693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17040434659272693657386257 12780325994454520243039693)
        ·
          refine ⟨4792622247920445091139885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12780325994454520243039693 4792622247920445091139885)
          ·
            refine ⟨1797233342970166909177457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4792622247920445091139885 1797233342970166909177457)
            ·
              refine ⟨1347925007227625181883093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797233342970166909177457 1347925007227625181883093)
              ·
                refine ⟨31591992356897465200385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1347925007227625181883093 31591992356897465200385)
                ·
                  rfl

theorem cell21_415295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_415295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415295 prefixEnd_415295 := by exact prefixLift 415295
  have htrace : WordTrace (prefixWord ++ tailWord_415295) baseStart_415295 baseEnd_415295 := by
    simpa [prefixWord, tailWord_415295, baseEnd_415295] using wordTrace_append hprefix tailTrace_415295
  have hstable : (prefixWord ++ tailWord_415295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415295).length < 2 ^ (prefixWord ++ tailWord_415295).sum := by decide
  have hdescent : baseEnd_415295 < baseStart_415295 := by decide
  rcases family_descends (prefixWord ++ tailWord_415295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415340 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_415340 : Nat := 118140960795 + 415340 * 2 ^ 59
def prefixEnd_415340 : Nat := 4983230072969 + 3 ^ 40 * 415340 * 2
def baseEnd_415340 : Nat := 94786246683782317351063

theorem tailTrace_415340 : CollatzResearch.WordTrace tailWord_415340 prefixEnd_415340 94786246683782317351063 := by
  unfold tailWord_415340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574347157650794634865737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10099129543534392846487649 7574347157650794634865737)
  ·
    refine ⟨5680760368238095976149303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7574347157650794634865737 5680760368238095976149303)
    ·
      refine ⟨8521140552357143964223955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5680760368238095976149303 8521140552357143964223955)
      ·
        refine ⟨12781710828535715946335933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8521140552357143964223955 12781710828535715946335933)
        ·
          refine ⟨4793141560700893479875975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12781710828535715946335933 4793141560700893479875975)
          ·
            refine ⟨7189712341051340219813963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793141560700893479875975 7189712341051340219813963)
            ·
              refine ⟨10784568511577010329720945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189712341051340219813963 10784568511577010329720945)
              ·
                refine ⟨8088426383682757747290709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10784568511577010329720945 8088426383682757747290709)
                ·
                  refine ⟨94786246683782317351063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8088426383682757747290709 94786246683782317351063)
                  ·
                    rfl

theorem cell21_415340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_415340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415340 prefixEnd_415340 := by exact prefixLift 415340
  have htrace : WordTrace (prefixWord ++ tailWord_415340) baseStart_415340 baseEnd_415340 := by
    simpa [prefixWord, tailWord_415340, baseEnd_415340] using wordTrace_append hprefix tailTrace_415340
  have hstable : (prefixWord ++ tailWord_415340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415340).length < 2 ^ (prefixWord ++ tailWord_415340).sum := by decide
  have hdescent : baseEnd_415340 < baseStart_415340 := by decide
  rcases family_descends (prefixWord ++ tailWord_415340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415374 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_415374 : Nat := 118140960795 + 415374 * 2 ^ 59
def prefixEnd_415374 : Nat := 4983230072969 + 3 ^ 40 * 415374 * 2
def baseEnd_415374 : Nat := 94794005947005813784327

theorem tailTrace_415374 : CollatzResearch.WordTrace tailWord_415374 prefixEnd_415374 94794005947005813784327 := by
  unfold tailWord_415374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893741799647301634558647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10099956264785608717646117 1893741799647301634558647)
  ·
    refine ⟨2840612699470952451837971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893741799647301634558647 2840612699470952451837971)
    ·
      refine ⟨4260919049206428677756957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840612699470952451837971 4260919049206428677756957)
      ·
        refine ⟨1597844643452410754158859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4260919049206428677756957 1597844643452410754158859)
        ·
          refine ⟨2396766965178616131238289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597844643452410754158859 2396766965178616131238289)
          ·
            refine ⟨1797575223883962098428717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396766965178616131238289 1797575223883962098428717)
            ·
              refine ⟨674090708956485786910769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797575223883962098428717 674090708956485786910769)
              ·
                refine ⟨505568031717364340183077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674090708956485786910769 505568031717364340183077)
                ·
                  refine ⟨94794005947005813784327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505568031717364340183077 94794005947005813784327)
                  ·
                    rfl

theorem cell21_415374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_415374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415374 prefixEnd_415374 := by exact prefixLift 415374
  have htrace : WordTrace (prefixWord ++ tailWord_415374) baseStart_415374 baseEnd_415374 := by
    simpa [prefixWord, tailWord_415374, baseEnd_415374] using wordTrace_append hprefix tailTrace_415374
  have hstable : (prefixWord ++ tailWord_415374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415374).length < 2 ^ (prefixWord ++ tailWord_415374).sum := by decide
  have hdescent : baseEnd_415374 < baseStart_415374 := by decide
  rcases family_descends (prefixWord ++ tailWord_415374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415436 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_415436 : Nat := 118140960795 + 415436 * 2 ^ 59
def prefixEnd_415436 : Nat := 4983230072969 + 3 ^ 40 * 415436 * 2
def baseEnd_415436 : Nat := 94808155191707483750867

theorem tailTrace_415436 : CollatzResearch.WordTrace tailWord_415436 prefixEnd_415436 94808155191707483750867 := by
  unfold tailWord_415436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7576097861476898832613081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10101463815302531776817441 7576097861476898832613081)
  ·
    refine ⟨5682073396107674124459811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7576097861476898832613081 5682073396107674124459811)
    ·
      refine ⟨8523110094161511186689717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682073396107674124459811 8523110094161511186689717)
      ·
        refine ⟨799041571327641673752161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8523110094161511186689717 799041571327641673752161)
        ·
          refine ⟨599281178495731255314121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799041571327641673752161 599281178495731255314121)
          ·
            refine ⟨449460883871798441485591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599281178495731255314121 449460883871798441485591)
            ·
              refine ⟨674191325807697662228387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449460883871798441485591 674191325807697662228387)
              ·
                refine ⟨1011286988711546493342581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674191325807697662228387 1011286988711546493342581)
                ·
                  refine ⟨94808155191707483750867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1011286988711546493342581 94808155191707483750867)
                  ·
                    rfl

theorem cell21_415436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_415436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415436 prefixEnd_415436 := by exact prefixLift 415436
  have htrace : WordTrace (prefixWord ++ tailWord_415436) baseStart_415436 baseEnd_415436 := by
    simpa [prefixWord, tailWord_415436, baseEnd_415436] using wordTrace_append hprefix tailTrace_415436
  have hstable : (prefixWord ++ tailWord_415436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415436).length < 2 ^ (prefixWord ++ tailWord_415436).sum := by decide
  have hdescent : baseEnd_415436 < baseStart_415436 := by decide
  rcases family_descends (prefixWord ++ tailWord_415436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415447 : List Nat := [1, 1, 3, 2, 1, 3, 4, 6]
def baseStart_415447 : Nat := 118140960795 + 415447 * 2 ^ 59
def prefixEnd_415447 : Nat := 4983230072969 + 3 ^ 40 * 415447 * 2
def baseEnd_415447 : Nat := 31603555180524636355837

theorem tailTrace_415447 : CollatzResearch.WordTrace tailWord_415447 prefixEnd_415447 31603555180524636355837 := by
  unfold tailWord_415447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152596925913946543876595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10101731283942631029251063 15152596925913946543876595)
  ·
    refine ⟨22728895388870919815814893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15152596925913946543876595 22728895388870919815814893)
    ·
      refine ⟨8523335770826594930930585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22728895388870919815814893 8523335770826594930930585)
      ·
        refine ⟨6392501828119946198197939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8523335770826594930930585 6392501828119946198197939)
        ·
          refine ⟨9588752742179919297296909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6392501828119946198197939 9588752742179919297296909)
          ·
            refine ⟨3595782278317469736486341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9588752742179919297296909 3595782278317469736486341)
            ·
              refine ⟨674209177184525575591189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3595782278317469736486341 674209177184525575591189)
              ·
                refine ⟨31603555180524636355837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 674209177184525575591189 31603555180524636355837)
                ·
                  rfl

theorem cell21_415447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_415447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415447 prefixEnd_415447 := by exact prefixLift 415447
  have htrace : WordTrace (prefixWord ++ tailWord_415447) baseStart_415447 baseEnd_415447 := by
    simpa [prefixWord, tailWord_415447, baseEnd_415447] using wordTrace_append hprefix tailTrace_415447
  have hstable : (prefixWord ++ tailWord_415447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415447).length < 2 ^ (prefixWord ++ tailWord_415447).sum := by decide
  have hdescent : baseEnd_415447 < baseStart_415447 := by decide
  rcases family_descends (prefixWord ++ tailWord_415447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415450 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_415450 : Nat := 118140960795 + 415450 * 2 ^ 59
def prefixEnd_415450 : Nat := 4983230072969 + 3 ^ 40 * 415450 * 2
def baseEnd_415450 : Nat := 94811350182446570517505

theorem tailTrace_415450 : CollatzResearch.WordTrace tailWord_415450 prefixEnd_415450 94811350182446570517505 := by
  unfold tailWord_415450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788176586225769514058951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10101804229935385370823869 3788176586225769514058951)
  ·
    refine ⟨5682264879338654271088427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788176586225769514058951 5682264879338654271088427)
    ·
      refine ⟨8523397319007981406632641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682264879338654271088427 8523397319007981406632641)
      ·
        refine ⟨6392547989255986054974481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8523397319007981406632641 6392547989255986054974481)
        ·
          refine ⟨4794410991941989541230861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6392547989255986054974481 4794410991941989541230861)
          ·
            refine ⟨1797904121978246077961573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4794410991941989541230861 1797904121978246077961573)
            ·
              refine ⟨337107022870921139617795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1797904121978246077961573 337107022870921139617795)
              ·
                refine ⟨505660534306381709426693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337107022870921139617795 505660534306381709426693)
                ·
                  refine ⟨94811350182446570517505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505660534306381709426693 94811350182446570517505)
                  ·
                    rfl

theorem cell21_415450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_415450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415450 prefixEnd_415450 := by exact prefixLift 415450
  have htrace : WordTrace (prefixWord ++ tailWord_415450) baseStart_415450 baseEnd_415450 := by
    simpa [prefixWord, tailWord_415450, baseEnd_415450] using wordTrace_append hprefix tailTrace_415450
  have hstable : (prefixWord ++ tailWord_415450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415450).length < 2 ^ (prefixWord ++ tailWord_415450).sum := by decide
  have hdescent : baseEnd_415450 < baseStart_415450 := by decide
  rcases family_descends (prefixWord ++ tailWord_415450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415509 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 4]
def baseStart_415509 : Nat := 118140960795 + 415509 * 2 ^ 59
def prefixEnd_415509 : Nat := 4983230072969 + 3 ^ 40 * 415509 * 2
def baseEnd_415509 : Nat := 94824814786275579034051

theorem tailTrace_415509 : CollatzResearch.WordTrace tailWord_415509 prefixEnd_415509 94824814786275579034051 := by
  unfold tailWord_415509
  simp only [CollatzResearch.WordTrace]
  refine ⟨15154858251689331132633581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10103238834459554088422387 15154858251689331132633581)
  ·
    refine ⟨5683071844383499174737593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15154858251689331132633581 5683071844383499174737593)
    ·
      refine ⟨4262303883287624381053195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5683071844383499174737593 4262303883287624381053195)
      ·
        refine ⟨6393455824931436571579793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4262303883287624381053195 6393455824931436571579793)
        ·
          refine ⟨4795091868698577428684845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6393455824931436571579793 4795091868698577428684845)
          ·
            refine ⟨1798159450761966535756817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4795091868698577428684845 1798159450761966535756817)
            ·
              refine ⟨1348619588071474901817613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798159450761966535756817 1348619588071474901817613)
              ·
                refine ⟨505732345526803088181605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348619588071474901817613 505732345526803088181605)
                ·
                  refine ⟨94824814786275579034051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505732345526803088181605 94824814786275579034051)
                  ·
                    rfl

theorem cell21_415509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_415509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415509 prefixEnd_415509 := by exact prefixLift 415509
  have htrace : WordTrace (prefixWord ++ tailWord_415509) baseStart_415509 baseEnd_415509 := by
    simpa [prefixWord, tailWord_415509, baseEnd_415509] using wordTrace_append hprefix tailTrace_415509
  have hstable : (prefixWord ++ tailWord_415509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415509).length < 2 ^ (prefixWord ++ tailWord_415509).sum := by decide
  have hdescent : baseEnd_415509 < baseStart_415509 := by decide
  rcases family_descends (prefixWord ++ tailWord_415509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415540 : List Nat := [2, 5, 1, 1, 2, 2, 8]
def baseStart_415540 : Nat := 118140960795 + 415540 * 2 ^ 59
def prefixEnd_415540 : Nat := 4983230072969 + 3 ^ 40 * 415540 * 2
def baseEnd_415540 : Nat := 10536876600958490446369

theorem tailTrace_415540 : CollatzResearch.WordTrace tailWord_415540 prefixEnd_415540 10536876600958490446369 := by
  unfold tailWord_415540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577994457288511713506037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10103992609718015618008049 7577994457288511713506037)
  ·
    refine ⟨710436980370797973141191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7577994457288511713506037 710436980370797973141191)
    ·
      refine ⟨1065655470556196959711787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710436980370797973141191 1065655470556196959711787)
      ·
        refine ⟨1598483205834295439567681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065655470556196959711787 1598483205834295439567681)
        ·
          refine ⟨1198862404375721579675761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598483205834295439567681 1198862404375721579675761)
          ·
            refine ⟨899146803281791184756821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198862404375721579675761 899146803281791184756821)
            ·
              refine ⟨10536876600958490446369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 899146803281791184756821 10536876600958490446369)
              ·
                rfl

theorem cell21_415540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 8].length) (baseStart_415540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415540 prefixEnd_415540 := by exact prefixLift 415540
  have htrace : WordTrace (prefixWord ++ tailWord_415540) baseStart_415540 baseEnd_415540 := by
    simpa [prefixWord, tailWord_415540, baseEnd_415540] using wordTrace_append hprefix tailTrace_415540
  have hstable : (prefixWord ++ tailWord_415540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415540).length < 2 ^ (prefixWord ++ tailWord_415540).sum := by decide
  have hdescent : baseEnd_415540 < baseStart_415540 := by decide
  rcases family_descends (prefixWord ++ tailWord_415540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415658 : List Nat := [3, 1, 17]
def baseStart_415658 : Nat := 118140960795 + 415658 * 2 ^ 59
def prefixEnd_415658 : Nat := 4983230072969 + 3 ^ 40 * 415658 * 2
def baseEnd_415658 : Nat := 130121836236329809397

theorem tailTrace_415658 : CollatzResearch.WordTrace tailWord_415658 prefixEnd_415658 130121836236329809397 := by
  unfold tailWord_415658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3790073182037382394951907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10106861818766353053205085 3790073182037382394951907)
  ·
    refine ⟨5685109773056073592427861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3790073182037382394951907 5685109773056073592427861)
    ·
      refine ⟨130121836236329809397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 5685109773056073592427861 130121836236329809397)
      ·
        rfl

theorem cell21_415658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 17].length) (baseStart_415658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415658 prefixEnd_415658 := by exact prefixLift 415658
  have htrace : WordTrace (prefixWord ++ tailWord_415658) baseStart_415658 baseEnd_415658 := by
    simpa [prefixWord, tailWord_415658, baseEnd_415658] using wordTrace_append hprefix tailTrace_415658
  have hstable : (prefixWord ++ tailWord_415658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415658).length < 2 ^ (prefixWord ++ tailWord_415658).sum := by decide
  have hdescent : baseEnd_415658 < baseStart_415658 := by decide
  rcases family_descends (prefixWord ++ tailWord_415658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415689 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_415689 : Nat := 118140960795 + 415689 * 2 ^ 59
def prefixEnd_415689 : Nat := 4983230072969 + 3 ^ 40 * 415689 * 2
def baseEnd_415689 : Nat := 94865893238635266033683

theorem tailTrace_415689 : CollatzResearch.WordTrace tailWord_415689 prefixEnd_415689 94865893238635266033683 := by
  unfold tailWord_415689
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161423391037221874186121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10107615594024814582790747 15161423391037221874186121)
  ·
    refine ⟨11371067543277916405639591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15161423391037221874186121 11371067543277916405639591)
    ·
      refine ⟨17056601314916874608459387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11371067543277916405639591 17056601314916874608459387)
      ·
        refine ⟨25584901972375311912689081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17056601314916874608459387 25584901972375311912689081)
        ·
          refine ⟨19188676479281483934516811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25584901972375311912689081 19188676479281483934516811)
          ·
            refine ⟨28783014718922225901775217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19188676479281483934516811 28783014718922225901775217)
            ·
              refine ⟨21587261039191669426331413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28783014718922225901775217 21587261039191669426331413)
              ·
                refine ⟨1011902861212109504359285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21587261039191669426331413 1011902861212109504359285)
                ·
                  refine ⟨94865893238635266033683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1011902861212109504359285 94865893238635266033683)
                  ·
                    rfl

theorem cell21_415689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_415689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415689 prefixEnd_415689 := by exact prefixLift 415689
  have htrace : WordTrace (prefixWord ++ tailWord_415689) baseStart_415689 baseEnd_415689 := by
    simpa [prefixWord, tailWord_415689, baseEnd_415689] using wordTrace_append hprefix tailTrace_415689
  have hstable : (prefixWord ++ tailWord_415689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415689).length < 2 ^ (prefixWord ++ tailWord_415689).sum := by decide
  have hdescent : baseEnd_415689 < baseStart_415689 := by decide
  rcases family_descends (prefixWord ++ tailWord_415689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415692 : List Nat := [2, 2, 1, 4, 1, 3, 3, 5]
def baseStart_415692 : Nat := 118140960795 + 415692 * 2 ^ 59
def prefixEnd_415692 : Nat := 4983230072969 + 3 ^ 40 * 415692 * 2
def baseEnd_415692 : Nat := 31622192626502642494559

theorem tailTrace_415692 : CollatzResearch.WordTrace tailWord_415692 prefixEnd_415692 31622192626502642494559 := by
  unfold tailWord_415692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580766405013176693272665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10107688540017568924363553 7580766405013176693272665)
  ·
    refine ⟨5685574803759882519954499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7580766405013176693272665 5685574803759882519954499)
    ·
      refine ⟨8528362205639823779931749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5685574803759882519954499 8528362205639823779931749)
      ·
        refine ⟨1599067913557466958737203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8528362205639823779931749 1599067913557466958737203)
        ·
          refine ⟨2398601870336200438105805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599067913557466958737203 2398601870336200438105805)
          ·
            refine ⟨899475701376075164289677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2398601870336200438105805 899475701376075164289677)
            ·
              refine ⟨337303388016028186608629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899475701376075164289677 337303388016028186608629)
              ·
                refine ⟨31622192626502642494559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337303388016028186608629 31622192626502642494559)
                ·
                  rfl

theorem cell21_415692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_415692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415692 prefixEnd_415692 := by exact prefixLift 415692
  have htrace : WordTrace (prefixWord ++ tailWord_415692) baseStart_415692 baseEnd_415692 := by
    simpa [prefixWord, tailWord_415692, baseEnd_415692] using wordTrace_append hprefix tailTrace_415692
  have hstable : (prefixWord ++ tailWord_415692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415692).length < 2 ^ (prefixWord ++ tailWord_415692).sum := by decide
  have hdescent : baseEnd_415692 < baseStart_415692 := by decide
  rcases family_descends (prefixWord ++ tailWord_415692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415751 : List Nat := [1, 1, 4, 3, 1, 3, 1, 7]
def baseStart_415751 : Nat := 118140960795 + 415751 * 2 ^ 59
def prefixEnd_415751 : Nat := 4983230072969 + 3 ^ 40 * 415751 * 2
def baseEnd_415751 : Nat := 31626680827778978666741

theorem tailTrace_415751 : CollatzResearch.WordTrace tailWord_415751 prefixEnd_415751 31626680827778978666741 := by
  unfold tailWord_415751
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163684716812606462943107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10109123144541737641962071 15163684716812606462943107)
  ·
    refine ⟨22745527075218909694414661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15163684716812606462943107 22745527075218909694414661)
    ·
      refine ⟨4264786326603545567702749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22745527075218909694414661 4264786326603545567702749)
      ·
        refine ⟨1599294872476329587888531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4264786326603545567702749 1599294872476329587888531)
        ·
          refine ⟨2398942308714494381832797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599294872476329587888531 2398942308714494381832797)
          ·
            refine ⟨899603365767935393187299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2398942308714494381832797 899603365767935393187299)
            ·
              refine ⟨1349405048651903089780949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899603365767935393187299 1349405048651903089780949)
              ·
                refine ⟨31626680827778978666741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1349405048651903089780949 31626680827778978666741)
                ·
                  rfl

theorem cell21_415751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_415751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415751 prefixEnd_415751 := by exact prefixLift 415751
  have htrace : WordTrace (prefixWord ++ tailWord_415751) baseStart_415751 baseEnd_415751 := by
    simpa [prefixWord, tailWord_415751, baseEnd_415751] using wordTrace_append hprefix tailTrace_415751
  have hstable : (prefixWord ++ tailWord_415751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415751).length < 2 ^ (prefixWord ++ tailWord_415751).sum := by decide
  have hdescent : baseEnd_415751 < baseStart_415751 := by decide
  rcases family_descends (prefixWord ++ tailWord_415751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415841 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_415841 : Nat := 118140960795 + 415841 * 2 ^ 59
def prefixEnd_415841 : Nat := 4983230072969 + 3 ^ 40 * 415841 * 2
def baseEnd_415841 : Nat := 94900581709516779500039

theorem tailTrace_415841 : CollatzResearch.WordTrace tailWord_415841 prefixEnd_415841 94900581709516779500039 := by
  unfold tailWord_415841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166967286486551833719377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10111311524324367889146251 15166967286486551833719377)
  ·
    refine ⟨11375225464864913875289533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15166967286486551833719377 11375225464864913875289533)
    ·
      refine ⟨4265709549324342703233575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11375225464864913875289533 4265709549324342703233575)
      ·
        refine ⟨6398564323986514054850363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265709549324342703233575 6398564323986514054850363)
        ·
          refine ⟨9597846485979771082275545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398564323986514054850363 9597846485979771082275545)
          ·
            refine ⟨7198384864484828311706659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9597846485979771082275545 7198384864484828311706659)
            ·
              refine ⟨10797577296727242467559989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198384864484828311706659 10797577296727242467559989)
              ·
                refine ⟨1012272871568178981333749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10797577296727242467559989 1012272871568178981333749)
                ·
                  refine ⟨94900581709516779500039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012272871568178981333749 94900581709516779500039)
                  ·
                    rfl

theorem cell21_415841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_415841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415841 prefixEnd_415841 := by exact prefixLift 415841
  have htrace : WordTrace (prefixWord ++ tailWord_415841) baseStart_415841 baseEnd_415841 := by
    simpa [prefixWord, tailWord_415841, baseEnd_415841] using wordTrace_append hprefix tailTrace_415841
  have hstable : (prefixWord ++ tailWord_415841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415841).length < 2 ^ (prefixWord ++ tailWord_415841).sum := by decide
  have hdescent : baseEnd_415841 < baseStart_415841 := by decide
  rcases family_descends (prefixWord ++ tailWord_415841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415858 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_415858 : Nat := 118140960795 + 415858 * 2 ^ 59
def prefixEnd_415858 : Nat := 4983230072969 + 3 ^ 40 * 415858 * 2
def baseEnd_415858 : Nat := 94904461341128527716671

theorem tailTrace_415858 : CollatzResearch.WordTrace tailWord_415858 prefixEnd_415858 94904461341128527716671 := by
  unfold tailWord_415858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791896831856240934272057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10111724884949975824725485 3791896831856240934272057)
  ·
    refine ⟨2843922623892180700704043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3791896831856240934272057 2843922623892180700704043)
    ·
      refine ⟨4265883935838271051056065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843922623892180700704043 4265883935838271051056065)
      ·
        refine ⟨3199412951878703288292049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265883935838271051056065 3199412951878703288292049)
        ·
          refine ⟨2399559713909027466219037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3199412951878703288292049 2399559713909027466219037)
          ·
            refine ⟨899834892715885299832139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2399559713909027466219037 899834892715885299832139)
            ·
              refine ⟨1349752339073827949748209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899834892715885299832139 1349752339073827949748209)
              ·
                refine ⟨1012314254305370962311157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349752339073827949748209 1012314254305370962311157)
                ·
                  refine ⟨94904461341128527716671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012314254305370962311157 94904461341128527716671)
                  ·
                    rfl

theorem cell21_415858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_415858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415858 prefixEnd_415858 := by exact prefixLift 415858
  have htrace : WordTrace (prefixWord ++ tailWord_415858) baseStart_415858 baseEnd_415858 := by
    simpa [prefixWord, tailWord_415858, baseEnd_415858] using wordTrace_append hprefix tailTrace_415858
  have hstable : (prefixWord ++ tailWord_415858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415858).length < 2 ^ (prefixWord ++ tailWord_415858).sum := by decide
  have hdescent : baseEnd_415858 < baseStart_415858 := by decide
  rcases family_descends (prefixWord ++ tailWord_415858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415875 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 3]
def baseStart_415875 : Nat := 118140960795 + 415875 * 2 ^ 59
def prefixEnd_415875 : Nat := 4983230072969 + 3 ^ 40 * 415875 * 2
def baseEnd_415875 : Nat := 94908340972740275933303

theorem tailTrace_415875 : CollatzResearch.WordTrace tailWord_415875 prefixEnd_415875 94908340972740275933303 := by
  unfold tailWord_415875
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168207368363375640457079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10112138245575583760304719 15168207368363375640457079)
  ·
    refine ⟨22752311052545063460685619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15168207368363375640457079 22752311052545063460685619)
    ·
      refine ⟨34128466578817595191028429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22752311052545063460685619 34128466578817595191028429)
      ·
        refine ⟨12798174967056598196635661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34128466578817595191028429 12798174967056598196635661)
        ·
          refine ⟨4799315612646224323738373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12798174967056598196635661 4799315612646224323738373)
          ·
            refine ⟨899871677371167060700945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4799315612646224323738373 899871677371167060700945)
            ·
              refine ⟨674903758028375295525709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899871677371167060700945 674903758028375295525709)
              ·
                refine ⟨253088909260640735822141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674903758028375295525709 253088909260640735822141)
                ·
                  refine ⟨94908340972740275933303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253088909260640735822141 94908340972740275933303)
                  ·
                    rfl

theorem cell21_415875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 3].length) (baseStart_415875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415875 prefixEnd_415875 := by exact prefixLift 415875
  have htrace : WordTrace (prefixWord ++ tailWord_415875) baseStart_415875 baseEnd_415875 := by
    simpa [prefixWord, tailWord_415875, baseEnd_415875] using wordTrace_append hprefix tailTrace_415875
  have hstable : (prefixWord ++ tailWord_415875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415875).length < 2 ^ (prefixWord ++ tailWord_415875).sum := by decide
  have hdescent : baseEnd_415875 < baseStart_415875 := by decide
  rcases family_descends (prefixWord ++ tailWord_415875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415892 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_415892 : Nat := 118140960795 + 415892 * 2 ^ 59
def prefixEnd_415892 : Nat := 4983230072969 + 3 ^ 40 * 415892 * 2
def baseEnd_415892 : Nat := 94912220604352024149935

theorem tailTrace_415892 : CollatzResearch.WordTrace tailWord_415892 prefixEnd_415892 94912220604352024149935 := by
  unfold tailWord_415892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584413704650893771912965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10112551606201191695883953 7584413704650893771912965)
  ·
    refine ⟨1422077569622042582233681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7584413704650893771912965 1422077569622042582233681)
    ·
      refine ⟨1066558177216531936675261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1422077569622042582233681 1066558177216531936675261)
      ·
        refine ⟨399959316456199476253223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1066558177216531936675261 399959316456199476253223)
        ·
          refine ⟨599938974684299214379835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399959316456199476253223 599938974684299214379835)
          ·
            refine ⟨899908462026448821569753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599938974684299214379835 899908462026448821569753)
            ·
              refine ⟨674931346519836616177315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899908462026448821569753 674931346519836616177315)
              ·
                refine ⟨1012397019779754924265973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674931346519836616177315 1012397019779754924265973)
                ·
                  refine ⟨94912220604352024149935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012397019779754924265973 94912220604352024149935)
                  ·
                    rfl

theorem cell21_415892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_415892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415892 prefixEnd_415892 := by exact prefixLift 415892
  have htrace : WordTrace (prefixWord ++ tailWord_415892) baseStart_415892 baseEnd_415892 := by
    simpa [prefixWord, tailWord_415892, baseEnd_415892] using wordTrace_append hprefix tailTrace_415892
  have hstable : (prefixWord ++ tailWord_415892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415892).length < 2 ^ (prefixWord ++ tailWord_415892).sum := by decide
  have hdescent : baseEnd_415892 < baseStart_415892 := by decide
  rcases family_descends (prefixWord ++ tailWord_415892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415931 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_415931 : Nat := 118140960795 + 415931 * 2 ^ 59
def prefixEnd_415931 : Nat := 4983230072969 + 3 ^ 40 * 415931 * 2
def baseEnd_415931 : Nat := 94921120935696622999855

theorem tailTrace_415931 : CollatzResearch.WordTrace tailWord_415931 prefixEnd_415931 94921120935696622999855 := by
  unfold tailWord_415931
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170249856160497204495647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10113499904106998136330431 15170249856160497204495647)
  ·
    refine ⟨22755374784240745806743471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15170249856160497204495647 22755374784240745806743471)
    ·
      refine ⟨34133062176361118710115207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22755374784240745806743471 34133062176361118710115207)
      ·
        refine ⟨51199593264541678065172811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34133062176361118710115207 51199593264541678065172811)
        ·
          refine ⟨76799389896812517097759217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51199593264541678065172811 76799389896812517097759217)
          ·
            refine ⟨57599542422609387823319413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76799389896812517097759217 57599542422609387823319413)
            ·
              refine ⟨5399957102119630108436195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57599542422609387823319413 5399957102119630108436195)
              ·
                refine ⟨8099935653179445162654293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399957102119630108436195 8099935653179445162654293)
                ·
                  refine ⟨94921120935696622999855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8099935653179445162654293 94921120935696622999855)
                  ·
                    rfl

theorem cell21_415931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_415931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415931 prefixEnd_415931 := by exact prefixLift 415931
  have htrace : WordTrace (prefixWord ++ tailWord_415931) baseStart_415931 baseEnd_415931 := by
    simpa [prefixWord, tailWord_415931, baseEnd_415931] using wordTrace_append hprefix tailTrace_415931
  have hstable : (prefixWord ++ tailWord_415931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415931).length < 2 ^ (prefixWord ++ tailWord_415931).sum := by decide
  have hdescent : baseEnd_415931 < baseStart_415931 := by decide
  rcases family_descends (prefixWord ++ tailWord_415931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415937 : List Nat := [1, 2, 6, 1, 3, 1, 7]
def baseStart_415937 : Nat := 118140960795 + 415937 * 2 ^ 59
def prefixEnd_415937 : Nat := 4983230072969 + 3 ^ 40 * 415937 * 2
def baseEnd_415937 : Nat := 10546943357493549544427

theorem tailTrace_415937 : CollatzResearch.WordTrace tailWord_415937 prefixEnd_415937 10546943357493549544427 := by
  unfold tailWord_415937
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170468694138760229214065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10113645796092506819476043 15170468694138760229214065)
  ·
    refine ⟨11377851520604070171910549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15170468694138760229214065 11377851520604070171910549)
    ·
      refine ⟨533336790028315789308307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11377851520604070171910549 533336790028315789308307)
      ·
        refine ⟨800005185042473683962461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533336790028315789308307 800005185042473683962461)
        ·
          refine ⟨300001944390927631485923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 800005185042473683962461 300001944390927631485923)
          ·
            refine ⟨450002916586391447228885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300001944390927631485923 450002916586391447228885)
            ·
              refine ⟨10546943357493549544427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 450002916586391447228885 10546943357493549544427)
              ·
                rfl

theorem cell21_415937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 7].length) (baseStart_415937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415937 prefixEnd_415937 := by exact prefixLift 415937
  have htrace : WordTrace (prefixWord ++ tailWord_415937) baseStart_415937 baseEnd_415937 := by
    simpa [prefixWord, tailWord_415937, baseEnd_415937] using wordTrace_append hprefix tailTrace_415937
  have hstable : (prefixWord ++ tailWord_415937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415937).length < 2 ^ (prefixWord ++ tailWord_415937).sum := by decide
  have hdescent : baseEnd_415937 < baseStart_415937 := by decide
  rcases family_descends (prefixWord ++ tailWord_415937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415951 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 3]
def baseStart_415951 : Nat := 118140960795 + 415951 * 2 ^ 59
def prefixEnd_415951 : Nat := 4983230072969 + 3 ^ 40 * 415951 * 2
def baseEnd_415951 : Nat := 94925685208181032666481

theorem tailTrace_415951 : CollatzResearch.WordTrace tailWord_415951 prefixEnd_415951 94925685208181032666481 := by
  unfold tailWord_415951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170979316088040620223707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10113986210725360413482471 15170979316088040620223707)
  ·
    refine ⟨22756468974132060930335561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15170979316088040620223707 22756468974132060930335561)
    ·
      refine ⟨17067351730599045697751671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22756468974132060930335561 17067351730599045697751671)
      ·
        refine ⟨25601027595898568546627507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17067351730599045697751671 25601027595898568546627507)
        ·
          refine ⟨38401541393847852819941261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25601027595898568546627507 38401541393847852819941261)
          ·
            refine ⟨14400578022692944807477973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38401541393847852819941261 14400578022692944807477973)
            ·
              refine ⟨337513547406865893925265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14400578022692944807477973 337513547406865893925265)
              ·
                refine ⟨253135160555149420443949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337513547406865893925265 253135160555149420443949)
                ·
                  refine ⟨94925685208181032666481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253135160555149420443949 94925685208181032666481)
                  ·
                    rfl

theorem cell21_415951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 3].length) (baseStart_415951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415951 prefixEnd_415951 := by exact prefixLift 415951
  have htrace : WordTrace (prefixWord ++ tailWord_415951) baseStart_415951 baseEnd_415951 := by
    simpa [prefixWord, tailWord_415951, baseEnd_415951] using wordTrace_append hprefix tailTrace_415951
  have hstable : (prefixWord ++ tailWord_415951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415951).length < 2 ^ (prefixWord ++ tailWord_415951).sum := by decide
  have hdescent : baseEnd_415951 < baseStart_415951 := by decide
  rcases family_descends (prefixWord ++ tailWord_415951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415962 : List Nat := [3, 1, 1, 2, 2, 1, 3, 8]
def baseStart_415962 : Nat := 118140960795 + 415962 * 2 ^ 59
def prefixEnd_415962 : Nat := 4983230072969 + 3 ^ 40 * 415962 * 2
def baseEnd_415962 : Nat := 31642731852682485994375

theorem tailTrace_415962 : CollatzResearch.WordTrace tailWord_415962 prefixEnd_415962 31642731852682485994375 := by
  unfold tailWord_415962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792845129762047374718535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10114253679365459665916093 3792845129762047374718535)
  ·
    refine ⟨5689267694643071062077803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3792845129762047374718535 5689267694643071062077803)
    ·
      refine ⟨8533901541964606593116705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689267694643071062077803 8533901541964606593116705)
      ·
        refine ⟨6400426156473454944837529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8533901541964606593116705 6400426156473454944837529)
        ·
          refine ⟨4800319617355091208628147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6400426156473454944837529 4800319617355091208628147)
          ·
            refine ⟨7200479426032636812942221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800319617355091208628147 7200479426032636812942221)
            ·
              refine ⟨2700179784762238804853333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7200479426032636812942221 2700179784762238804853333)
              ·
                refine ⟨31642731852682485994375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2700179784762238804853333 31642731852682485994375)
                ·
                  rfl

theorem cell21_415962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_415962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_415962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_415962 prefixEnd_415962 := by exact prefixLift 415962
  have htrace : WordTrace (prefixWord ++ tailWord_415962) baseStart_415962 baseEnd_415962 := by
    simpa [prefixWord, tailWord_415962, baseEnd_415962] using wordTrace_append hprefix tailTrace_415962
  have hstable : (prefixWord ++ tailWord_415962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415962).length < 2 ^ (prefixWord ++ tailWord_415962).sum := by decide
  have hdescent : baseEnd_415962 < baseStart_415962 := by decide
  rcases family_descends (prefixWord ++ tailWord_415962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416024 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_416024 : Nat := 118140960795 + 416024 * 2 ^ 59
def prefixEnd_416024 : Nat := 4983230072969 + 3 ^ 40 * 416024 * 2
def baseEnd_416024 : Nat := 94942344802749127949665

theorem tailTrace_416024 : CollatzResearch.WordTrace tailWord_416024 prefixEnd_416024 94942344802749127949665 := by
  unfold tailWord_416024
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586820922411787043815563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10115761229882382725087417 7586820922411787043815563)
  ·
    refine ⟨11380231383617680565723345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7586820922411787043815563 11380231383617680565723345)
    ·
      refine ⟨8535173537713260424292509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11380231383617680565723345 8535173537713260424292509)
      ·
        refine ⟨3200690076642472659109691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8535173537713260424292509 3200690076642472659109691)
        ·
          refine ⟨4801035114963708988664537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200690076642472659109691 4801035114963708988664537)
          ·
            refine ⟨3600776336222781741498403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4801035114963708988664537 3600776336222781741498403)
            ·
              refine ⟨5401164504334172612247605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600776336222781741498403 5401164504334172612247605)
              ·
                refine ⟨506359172281328682398213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5401164504334172612247605 506359172281328682398213)
                ·
                  refine ⟨94942344802749127949665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506359172281328682398213 94942344802749127949665)
                  ·
                    rfl

theorem cell21_416024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_416024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416024 prefixEnd_416024 := by exact prefixLift 416024
  have htrace : WordTrace (prefixWord ++ tailWord_416024) baseStart_416024 baseEnd_416024 := by
    simpa [prefixWord, tailWord_416024, baseEnd_416024] using wordTrace_append hprefix tailTrace_416024
  have hstable : (prefixWord ++ tailWord_416024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416024).length < 2 ^ (prefixWord ++ tailWord_416024).sum := by decide
  have hdescent : baseEnd_416024 < baseStart_416024 := by decide
  rcases family_descends (prefixWord ++ tailWord_416024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416103 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 3]
def baseStart_416103 : Nat := 118140960795 + 416103 * 2 ^ 59
def prefixEnd_416103 : Nat := 4983230072969 + 3 ^ 40 * 416103 * 2
def baseEnd_416103 : Nat := 94960373679062546132837

theorem tailTrace_416103 : CollatzResearch.WordTrace tailWord_416103 prefixEnd_416103 94960373679062546132837 := by
  unfold tailWord_416103
  simp only [CollatzResearch.WordTrace]
  refine ⟨15176523211537370579756963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10117682141024913719837975 15176523211537370579756963)
  ·
    refine ⟨22764784817306055869635445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15176523211537370579756963 22764784817306055869635445)
    ·
      refine ⟨2134198576622442737778323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22764784817306055869635445 2134198576622442737778323)
      ·
        refine ⟨3201297864933664106667485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134198576622442737778323 3201297864933664106667485)
        ·
          refine ⟨1200486699350124040000307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3201297864933664106667485 1200486699350124040000307)
          ·
            refine ⟨1800730049025186060000461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200486699350124040000307 1800730049025186060000461)
            ·
              refine ⟨675273768384444772500173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1800730049025186060000461 675273768384444772500173)
              ·
                refine ⟨253227663144166789687565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675273768384444772500173 253227663144166789687565)
                ·
                  refine ⟨94960373679062546132837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253227663144166789687565 94960373679062546132837)
                  ·
                    rfl

theorem cell21_416103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 3].length) (baseStart_416103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416103 prefixEnd_416103 := by exact prefixLift 416103
  have htrace : WordTrace (prefixWord ++ tailWord_416103) baseStart_416103 baseEnd_416103 := by
    simpa [prefixWord, tailWord_416103, baseEnd_416103] using wordTrace_append hprefix tailTrace_416103
  have hstable : (prefixWord ++ tailWord_416103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416103).length < 2 ^ (prefixWord ++ tailWord_416103).sum := by decide
  have hdescent : baseEnd_416103 < baseStart_416103 := by decide
  rcases family_descends (prefixWord ++ tailWord_416103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416114 : List Nat := [3, 2, 1, 2, 1, 3, 9]
def baseStart_416114 : Nat := 118140960795 + 416114 * 2 ^ 59
def prefixEnd_416114 : Nat := 4983230072969 + 3 ^ 40 * 416114 * 2
def baseEnd_416114 : Nat := 10551431558769885716609

theorem tailTrace_416114 : CollatzResearch.WordTrace tailWord_416114 prefixEnd_416114 10551431558769885716609 := by
  unfold tailWord_416114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794231103624379864601849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10117949609665012972271597 3794231103624379864601849)
  ·
    refine ⟨2845673327718284898451387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3794231103624379864601849 2845673327718284898451387)
    ·
      refine ⟨4268509991577427347677081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845673327718284898451387 4268509991577427347677081)
      ·
        refine ⟨3201382493683070510757811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4268509991577427347677081 3201382493683070510757811)
        ·
          refine ⟨4802073740524605766136717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201382493683070510757811 4802073740524605766136717)
          ·
            refine ⟨1800777652696727162301269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4802073740524605766136717 1800777652696727162301269)
            ·
              refine ⟨10551431558769885716609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1800777652696727162301269 10551431558769885716609)
              ·
                rfl

theorem cell21_416114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 9].length) (baseStart_416114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416114 prefixEnd_416114 := by exact prefixLift 416114
  have htrace : WordTrace (prefixWord ++ tailWord_416114) baseStart_416114 baseEnd_416114 := by
    simpa [prefixWord, tailWord_416114, baseEnd_416114] using wordTrace_append hprefix tailTrace_416114
  have hstable : (prefixWord ++ tailWord_416114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416114).length < 2 ^ (prefixWord ++ tailWord_416114).sum := by decide
  have hdescent : baseEnd_416114 < baseStart_416114 := by decide
  rcases family_descends (prefixWord ++ tailWord_416114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416131 : List Nat := [1, 1, 1, 3, 6, 1, 2, 6]
def baseStart_416131 : Nat := 118140960795 + 416131 * 2 ^ 59
def prefixEnd_416131 : Nat := 4983230072969 + 3 ^ 40 * 416131 * 2
def baseEnd_416131 : Nat := 31655587886846906555371

theorem tailTrace_416131 : CollatzResearch.WordTrace tailWord_416131 prefixEnd_416131 31655587886846906555371 := by
  unfold tailWord_416131
  simp only [CollatzResearch.WordTrace]
  refine ⟨15177544455435931361776247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10118362970290620907850831 15177544455435931361776247)
  ·
    refine ⟨22766316683153897042664371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15177544455435931361776247 22766316683153897042664371)
    ·
      refine ⟨34149475024730845563996557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22766316683153897042664371 34149475024730845563996557)
      ·
        refine ⟨12806053134274067086498709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34149475024730845563996557 12806053134274067086498709)
        ·
          refine ⟨600283740669096894679627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12806053134274067086498709 600283740669096894679627)
          ·
            refine ⟨900425611003645342019441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600283740669096894679627 900425611003645342019441)
            ·
              refine ⟨675319208252734006514581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900425611003645342019441 675319208252734006514581)
              ·
                refine ⟨31655587886846906555371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 675319208252734006514581 31655587886846906555371)
                ·
                  rfl

theorem cell21_416131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_416131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416131 prefixEnd_416131 := by exact prefixLift 416131
  have htrace : WordTrace (prefixWord ++ tailWord_416131) baseStart_416131 baseEnd_416131 := by
    simpa [prefixWord, tailWord_416131, baseEnd_416131] using wordTrace_append hprefix tailTrace_416131
  have hstable : (prefixWord ++ tailWord_416131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416131).length < 2 ^ (prefixWord ++ tailWord_416131).sum := by decide
  have hdescent : baseEnd_416131 < baseStart_416131 := by decide
  rcases family_descends (prefixWord ++ tailWord_416131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416221 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_416221 : Nat := 118140960795 + 416221 * 2 ^ 59
def prefixEnd_416221 : Nat := 4983230072969 + 3 ^ 40 * 416221 * 2
def baseEnd_416221 : Nat := 94987302886720563165929

theorem tailTrace_416221 : CollatzResearch.WordTrace tailWord_416221 prefixEnd_416221 94987302886720563165929 := by
  unfold tailWord_416221
  simp only [CollatzResearch.WordTrace]
  refine ⟨15180827025109876732552517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10120551350073251155035011 15180827025109876732552517)
  ·
    refine ⟨2846405067208101887353597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15180827025109876732552517 2846405067208101887353597)
    ·
      refine ⟨1067401900203038207757599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2846405067208101887353597 1067401900203038207757599)
      ·
        refine ⟨1601102850304557311636399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067401900203038207757599 1601102850304557311636399)
        ·
          refine ⟨2401654275456835967454599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601102850304557311636399 2401654275456835967454599)
          ·
            refine ⟨3602481413185253951181899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401654275456835967454599 3602481413185253951181899)
            ·
              refine ⟨5403722119777880926772849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602481413185253951181899 5403722119777880926772849)
              ·
                refine ⟨4052791589833410695079637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403722119777880926772849 4052791589833410695079637)
                ·
                  refine ⟨94987302886720563165929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4052791589833410695079637 94987302886720563165929)
                  ·
                    rfl

theorem cell21_416221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_416221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416221 prefixEnd_416221 := by exact prefixLift 416221
  have htrace : WordTrace (prefixWord ++ tailWord_416221) baseStart_416221 baseEnd_416221 := by
    simpa [prefixWord, tailWord_416221, baseEnd_416221] using wordTrace_append hprefix tailTrace_416221
  have hstable : (prefixWord ++ tailWord_416221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416221).length < 2 ^ (prefixWord ++ tailWord_416221).sum := by decide
  have hdescent : baseEnd_416221 < baseStart_416221 := by decide
  rcases family_descends (prefixWord ++ tailWord_416221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416235 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_416235 : Nat := 118140960795 + 416235 * 2 ^ 59
def prefixEnd_416235 : Nat := 4983230072969 + 3 ^ 40 * 416235 * 2
def baseEnd_416235 : Nat := 94990497877459649932567

theorem tailTrace_416235 : CollatzResearch.WordTrace tailWord_416235 prefixEnd_416235 94990497877459649932567 := by
  unfold tailWord_416235
  simp only [CollatzResearch.WordTrace]
  refine ⟨15181337647059157123562159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10120891764706104749041439 15181337647059157123562159)
  ·
    refine ⟨22772006470588735685343239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15181337647059157123562159 22772006470588735685343239)
    ·
      refine ⟨34158009705883103528014859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22772006470588735685343239 34158009705883103528014859)
      ·
        refine ⟨51237014558824655292022289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34158009705883103528014859 51237014558824655292022289)
        ·
          refine ⟨38427760919118491469016717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51237014558824655292022289 38427760919118491469016717)
          ·
            refine ⟨14410410344669434300881269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38427760919118491469016717 14410410344669434300881269)
            ·
              refine ⟨1350975969812759465707619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14410410344669434300881269 1350975969812759465707619)
              ·
                refine ⟨2026463954719139198561429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350975969812759465707619 2026463954719139198561429)
                ·
                  refine ⟨94990497877459649932567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2026463954719139198561429 94990497877459649932567)
                  ·
                    rfl

theorem cell21_416235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_416235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416235 prefixEnd_416235 := by exact prefixLift 416235
  have htrace : WordTrace (prefixWord ++ tailWord_416235) baseStart_416235 baseEnd_416235 := by
    simpa [prefixWord, tailWord_416235, baseEnd_416235] using wordTrace_append hprefix tailTrace_416235
  have hstable : (prefixWord ++ tailWord_416235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416235).length < 2 ^ (prefixWord ++ tailWord_416235).sum := by decide
  have hdescent : baseEnd_416235 < baseStart_416235 := by decide
  rcases family_descends (prefixWord ++ tailWord_416235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416238 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_416238 : Nat := 118140960795 + 416238 * 2 ^ 59
def prefixEnd_416238 : Nat := 4983230072969 + 3 ^ 40 * 416238 * 2
def baseEnd_416238 : Nat := 94991182518332311382561

theorem tailTrace_416238 : CollatzResearch.WordTrace tailWord_416238 prefixEnd_416238 94991182518332311382561 := by
  unfold tailWord_416238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897680883256036079490171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10120964710698859090614245 1897680883256036079490171)
  ·
    refine ⟨2846521324884054119235257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1897680883256036079490171 2846521324884054119235257)
    ·
      refine ⟨2134890993663040589426443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2846521324884054119235257 2134890993663040589426443)
      ·
        refine ⟨3202336490494560884139665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134890993663040589426443 3202336490494560884139665)
        ·
          refine ⟨2401752367870920663104749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202336490494560884139665 2401752367870920663104749)
          ·
            refine ⟨900657137951595248664281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2401752367870920663104749 900657137951595248664281)
            ·
              refine ⟨675492853463696436498211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900657137951595248664281 675492853463696436498211)
              ·
                refine ⟨1013239280195544654747317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675492853463696436498211 1013239280195544654747317)
                ·
                  refine ⟨94991182518332311382561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1013239280195544654747317 94991182518332311382561)
                  ·
                    rfl

theorem cell21_416238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_416238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416238 prefixEnd_416238 := by exact prefixLift 416238
  have htrace : WordTrace (prefixWord ++ tailWord_416238) baseStart_416238 baseEnd_416238 := by
    simpa [prefixWord, tailWord_416238, baseEnd_416238] using wordTrace_append hprefix tailTrace_416238
  have hstable : (prefixWord ++ tailWord_416238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416238).length < 2 ^ (prefixWord ++ tailWord_416238).sum := by decide
  have hdescent : baseEnd_416238 < baseStart_416238 := by decide
  rcases family_descends (prefixWord ++ tailWord_416238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416258 : List Nat := [3, 4, 1, 2, 3, 1, 2, 5]
def baseStart_416258 : Nat := 118140960795 + 416258 * 2 ^ 59
def prefixEnd_416258 : Nat := 4983230072969 + 3 ^ 40 * 416258 * 2
def baseEnd_416258 : Nat := 31665248930272240349729

theorem tailTrace_416258 : CollatzResearch.WordTrace tailWord_416258 prefixEnd_416258 31665248930272240349729 := by
  unfold tailWord_416258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795544131493958012912357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10121451017317221367766285 3795544131493958012912357)
  ·
    refine ⟨711664524655117127421067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3795544131493958012912357 711664524655117127421067)
    ·
      refine ⟨1067496786982675691131601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711664524655117127421067 1067496786982675691131601)
      ·
        refine ⟨800622590237006768348701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1067496786982675691131601 800622590237006768348701)
        ·
          refine ⟨300233471338877538130763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 800622590237006768348701 300233471338877538130763)
          ·
            refine ⟨450350207008316307196145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300233471338877538130763 450350207008316307196145)
            ·
              refine ⟨337762655256237230397109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450350207008316307196145 337762655256237230397109)
              ·
                refine ⟨31665248930272240349729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337762655256237230397109 31665248930272240349729)
                ·
                  rfl

theorem cell21_416258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_416258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416258 prefixEnd_416258 := by exact prefixLift 416258
  have htrace : WordTrace (prefixWord ++ tailWord_416258) baseStart_416258 baseEnd_416258 := by
    simpa [prefixWord, tailWord_416258, baseEnd_416258] using wordTrace_append hprefix tailTrace_416258
  have hstable : (prefixWord ++ tailWord_416258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416258).length < 2 ^ (prefixWord ++ tailWord_416258).sum := by decide
  have hdescent : baseEnd_416258 < baseStart_416258 := by decide
  rcases family_descends (prefixWord ++ tailWord_416258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416266 : List Nat := [3, 1, 2, 2, 2, 1, 3, 7]
def baseStart_416266 : Nat := 118140960795 + 416266 * 2 ^ 59
def prefixEnd_416266 : Nat := 4983230072969 + 3 ^ 40 * 416266 * 2
def baseEnd_416266 : Nat := 31665857499936828305279

theorem tailTrace_416266 : CollatzResearch.WordTrace tailWord_416266 prefixEnd_416266 31665857499936828305279 := by
  unfold tailWord_416266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795617077486712354485163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10121645539964566278627101 3795617077486712354485163)
  ·
    refine ⟨5693425616230068531727745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3795617077486712354485163 5693425616230068531727745)
    ·
      refine ⟨4270069212172551398795809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5693425616230068531727745 4270069212172551398795809)
      ·
        refine ⟨3202551909129413549096857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4270069212172551398795809 3202551909129413549096857)
        ·
          refine ⟨2401913931847060161822643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202551909129413549096857 2401913931847060161822643)
          ·
            refine ⟨3602870897770590242733965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401913931847060161822643 3602870897770590242733965)
            ·
              refine ⟨1351076586663971341025237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602870897770590242733965 1351076586663971341025237)
              ·
                refine ⟨31665857499936828305279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1351076586663971341025237 31665857499936828305279)
                ·
                  rfl

theorem cell21_416266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_416266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416266 prefixEnd_416266 := by exact prefixLift 416266
  have htrace : WordTrace (prefixWord ++ tailWord_416266) baseStart_416266 baseEnd_416266 := by
    simpa [prefixWord, tailWord_416266, baseEnd_416266] using wordTrace_append hprefix tailTrace_416266
  have hstable : (prefixWord ++ tailWord_416266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416266).length < 2 ^ (prefixWord ++ tailWord_416266).sum := by decide
  have hdescent : baseEnd_416266 < baseStart_416266 := by decide
  rcases family_descends (prefixWord ++ tailWord_416266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416435 : List Nat := [1, 1, 1, 2, 3, 6, 2, 5]
def baseStart_416435 : Nat := 118140960795 + 416435 * 2 ^ 59
def prefixEnd_416435 : Nat := 4983230072969 + 3 ^ 40 * 416435 * 2
def baseEnd_416435 : Nat := 31678713534101248866275

theorem tailTrace_416435 : CollatzResearch.WordTrace tailWord_416435 prefixEnd_416435 31678713534101248866275 := by
  unfold tailWord_416435
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188632246334591280842759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10125754830889727520561839 15188632246334591280842759)
  ·
    refine ⟨22782948369501886921264139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15188632246334591280842759 22782948369501886921264139)
    ·
      refine ⟨34174422554252830381896209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22782948369501886921264139 34174422554252830381896209)
      ·
        refine ⟨25630816915689622786422157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34174422554252830381896209 25630816915689622786422157)
        ·
          refine ⟨9611556343383608544908309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25630816915689622786422157 9611556343383608544908309)
          ·
            refine ⟨450541703596106650542577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9611556343383608544908309 450541703596106650542577)
            ·
              refine ⟨337906277697079987906933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450541703596106650542577 337906277697079987906933)
              ·
                refine ⟨31678713534101248866275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337906277697079987906933 31678713534101248866275)
                ·
                  rfl

theorem cell21_416435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 5].length) (baseStart_416435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416435 prefixEnd_416435 := by exact prefixLift 416435
  have htrace : WordTrace (prefixWord ++ tailWord_416435) baseStart_416435 baseEnd_416435 := by
    simpa [prefixWord, tailWord_416435, baseEnd_416435] using wordTrace_append hprefix tailTrace_416435
  have hstable : (prefixWord ++ tailWord_416435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416435).length < 2 ^ (prefixWord ++ tailWord_416435).sum := by decide
  have hdescent : baseEnd_416435 < baseStart_416435 := by decide
  rcases family_descends (prefixWord ++ tailWord_416435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416494 : List Nat := [4, 1, 2, 1, 1, 3, 2, 7]
def baseStart_416494 : Nat := 118140960795 + 416494 * 2 ^ 59
def prefixEnd_416494 : Nat := 4983230072969 + 3 ^ 40 * 416494 * 2
def baseEnd_416494 : Nat := 31683201735377585038457

theorem tailTrace_416494 : CollatzResearch.WordTrace tailWord_416494 prefixEnd_416494 31683201735377585038457 := by
  unfold tailWord_416494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898848019140105544655067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10127189435413896238160357 1898848019140105544655067)
  ·
    refine ⟨2848272028710158316982601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1898848019140105544655067 2848272028710158316982601)
    ·
      refine ⟨2136204021532618737736951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2848272028710158316982601 2136204021532618737736951)
      ·
        refine ⟨3204306032298928106605427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136204021532618737736951 3204306032298928106605427)
        ·
          refine ⟨4806459048448392159908141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204306032298928106605427 4806459048448392159908141)
          ·
            refine ⟨1802422143168147059965553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4806459048448392159908141 1802422143168147059965553)
            ·
              refine ⟨1351816607376110294974165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1802422143168147059965553 1351816607376110294974165)
              ·
                refine ⟨31683201735377585038457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1351816607376110294974165 31683201735377585038457)
                ·
                  rfl

theorem cell21_416494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_416494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416494 prefixEnd_416494 := by exact prefixLift 416494
  have htrace : WordTrace (prefixWord ++ tailWord_416494) baseStart_416494 baseEnd_416494 := by
    simpa [prefixWord, tailWord_416494, baseEnd_416494] using wordTrace_append hprefix tailTrace_416494
  have hstable : (prefixWord ++ tailWord_416494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416494).length < 2 ^ (prefixWord ++ tailWord_416494).sum := by decide
  have hdescent : baseEnd_416494 < baseStart_416494 := by decide
  rcases family_descends (prefixWord ++ tailWord_416494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416570 : List Nat := [3, 1, 1, 1, 6, 1, 8]
def baseStart_416570 : Nat := 118140960795 + 416570 * 2 ^ 59
def prefixEnd_416570 : Nat := 4983230072969 + 3 ^ 40 * 416570 * 2
def baseEnd_416570 : Nat := 10562994382397056872061

theorem tailTrace_416570 : CollatzResearch.WordTrace tailWord_416570 prefixEnd_416570 10562994382397056872061 := by
  unfold tailWord_416570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798389025211377334251791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10129037400563672891338109 3798389025211377334251791)
  ·
    refine ⟨5697583537817066001377687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3798389025211377334251791 5697583537817066001377687)
    ·
      refine ⟨8546375306725599002066531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5697583537817066001377687 8546375306725599002066531)
      ·
        refine ⟨12819562960088398503099797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8546375306725599002066531 12819562960088398503099797)
        ·
          refine ⟨600917013754143679832803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12819562960088398503099797 600917013754143679832803)
          ·
            refine ⟨901375520631215519749205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600917013754143679832803 901375520631215519749205)
            ·
              refine ⟨10562994382397056872061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 901375520631215519749205 10562994382397056872061)
              ·
                rfl

theorem cell21_416570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 8].length) (baseStart_416570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416570 prefixEnd_416570 := by exact prefixLift 416570
  have htrace : WordTrace (prefixWord ++ tailWord_416570) baseStart_416570 baseEnd_416570 := by
    simpa [prefixWord, tailWord_416570, baseEnd_416570] using wordTrace_append hprefix tailTrace_416570
  have hstable : (prefixWord ++ tailWord_416570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416570).length < 2 ^ (prefixWord ++ tailWord_416570).sum := by decide
  have hdescent : baseEnd_416570 < baseStart_416570 := by decide
  rcases family_descends (prefixWord ++ tailWord_416570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416604 : List Nat := [2, 2, 4, 2, 1, 3, 2, 5]
def baseStart_416604 : Nat := 118140960795 + 416604 * 2 ^ 59
def prefixEnd_416604 : Nat := 4983230072969 + 3 ^ 40 * 416604 * 2
def baseEnd_416604 : Nat := 31691569568265669427271

theorem tailTrace_416604 : CollatzResearch.WordTrace tailWord_416604 prefixEnd_416604 31691569568265669427271 := by
  unfold tailWord_416604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597398091361166571872433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10129864121814888762496577 7597398091361166571872433)
  ·
    refine ⟨5698048568520874928904325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7597398091361166571872433 5698048568520874928904325)
    ·
      refine ⟨1068384106597664049169561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5698048568520874928904325 1068384106597664049169561)
      ·
        refine ⟨801288079948248036877171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1068384106597664049169561 801288079948248036877171)
        ·
          refine ⟨1201932119922372055315757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801288079948248036877171 1201932119922372055315757)
          ·
            refine ⟨450724544970889520743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1201932119922372055315757 450724544970889520743409)
            ·
              refine ⟨338043408728167140557557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450724544970889520743409 338043408728167140557557)
              ·
                refine ⟨31691569568265669427271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338043408728167140557557 31691569568265669427271)
                ·
                  rfl

theorem cell21_416604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_416604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416604 prefixEnd_416604 := by exact prefixLift 416604
  have htrace : WordTrace (prefixWord ++ tailWord_416604) baseStart_416604 baseEnd_416604 := by
    simpa [prefixWord, tailWord_416604, baseEnd_416604] using wordTrace_append hprefix tailTrace_416604
  have hstable : (prefixWord ++ tailWord_416604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416604).length < 2 ^ (prefixWord ++ tailWord_416604).sum := by decide
  have hdescent : baseEnd_416604 < baseStart_416604 := by decide
  rcases family_descends (prefixWord ++ tailWord_416604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416615 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_416615 : Nat := 118140960795 + 416615 * 2 ^ 59
def prefixEnd_416615 : Nat := 4983230072969 + 3 ^ 40 * 416615 * 2
def baseEnd_416615 : Nat := 95077219054663433598457

theorem tailTrace_416615 : CollatzResearch.WordTrace tailWord_416615 prefixEnd_416615 95077219054663433598457 := by
  unfold tailWord_416615
  simp only [CollatzResearch.WordTrace]
  refine ⟨15195197385682482022395299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10130131590454988014930199 15195197385682482022395299)
  ·
    refine ⟨22792796078523723033592949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15195197385682482022395299 22792796078523723033592949)
    ·
      refine ⟨2136824632361599034399339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22792796078523723033592949 2136824632361599034399339)
      ·
        refine ⟨3205236948542398551599009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136824632361599034399339 3205236948542398551599009)
        ·
          refine ⟨2403927711406798913699257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3205236948542398551599009 2403927711406798913699257)
          ·
            refine ⟨1802945783555099185274443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2403927711406798913699257 1802945783555099185274443)
            ·
              refine ⟨2704418675332648777911665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802945783555099185274443 2704418675332648777911665)
              ·
                refine ⟨2028314006499486583433749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704418675332648777911665 2028314006499486583433749)
                ·
                  refine ⟨95077219054663433598457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2028314006499486583433749 95077219054663433598457)
                  ·
                    rfl

theorem cell21_416615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_416615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416615 prefixEnd_416615 := by exact prefixLift 416615
  have htrace : WordTrace (prefixWord ++ tailWord_416615) baseStart_416615 baseEnd_416615 := by
    simpa [prefixWord, tailWord_416615, baseEnd_416615] using wordTrace_append hprefix tailTrace_416615
  have hstable : (prefixWord ++ tailWord_416615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416615).length < 2 ^ (prefixWord ++ tailWord_416615).sum := by decide
  have hdescent : baseEnd_416615 < baseStart_416615 := by decide
  rcases family_descends (prefixWord ++ tailWord_416615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416649 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 4]
def baseStart_416649 : Nat := 118140960795 + 416649 * 2 ^ 59
def prefixEnd_416649 : Nat := 4983230072969 + 3 ^ 40 * 416649 * 2
def baseEnd_416649 : Nat := 95084978317886930031721

theorem tailTrace_416649 : CollatzResearch.WordTrace tailWord_416649 prefixEnd_416649 95084978317886930031721 := by
  unfold tailWord_416649
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196437467559305829133001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10130958311706203886088667 15196437467559305829133001)
  ·
    refine ⟨11397328100669479371849751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15196437467559305829133001 11397328100669479371849751)
    ·
      refine ⟨17095992151004219057774627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11397328100669479371849751 17095992151004219057774627)
      ·
        refine ⟨25643988226506328586661941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17095992151004219057774627 25643988226506328586661941)
        ·
          refine ⟨2404123896234968304999557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25643988226506328586661941 2404123896234968304999557)
          ·
            refine ⟨450773230544056557187417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2404123896234968304999557 450773230544056557187417)
            ·
              refine ⟨338079922908042417890563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450773230544056557187417 338079922908042417890563)
              ·
                refine ⟨507119884362063626835845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338079922908042417890563 507119884362063626835845)
                ·
                  refine ⟨95084978317886930031721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507119884362063626835845 95084978317886930031721)
                  ·
                    rfl

theorem cell21_416649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_416649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416649 prefixEnd_416649 := by exact prefixLift 416649
  have htrace : WordTrace (prefixWord ++ tailWord_416649) baseStart_416649 baseEnd_416649 := by
    simpa [prefixWord, tailWord_416649, baseEnd_416649] using wordTrace_append hprefix tailTrace_416649
  have hstable : (prefixWord ++ tailWord_416649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416649).length < 2 ^ (prefixWord ++ tailWord_416649).sum := by decide
  have hdescent : baseEnd_416649 < baseStart_416649 := by decide
  rcases family_descends (prefixWord ++ tailWord_416649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416753 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 5]
def baseStart_416753 : Nat := 118140960795 + 416753 * 2 ^ 59
def prefixEnd_416753 : Nat := 4983230072969 + 3 ^ 40 * 416753 * 2
def baseEnd_416753 : Nat := 95108712534805860298175

theorem tailTrace_416753 : CollatzResearch.WordTrace tailWord_416753 prefixEnd_416753 95108712534805860298175 := by
  unfold tailWord_416753
  simp only [CollatzResearch.WordTrace]
  refine ⟨15200230659182531590918913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10133487106121687727279275 15200230659182531590918913)
  ·
    refine ⟨11400172994386898693189185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15200230659182531590918913 11400172994386898693189185)
    ·
      refine ⟨8550129745790174019891889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11400172994386898693189185 8550129745790174019891889)
      ·
        refine ⟨6412597309342630514918917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8550129745790174019891889 6412597309342630514918917)
        ·
          refine ⟨1202361995501743221547297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6412597309342630514918917 1202361995501743221547297)
          ·
            refine ⟨901771496626307416160473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202361995501743221547297 901771496626307416160473)
            ·
              refine ⟨676328622469730562120355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901771496626307416160473 676328622469730562120355)
              ·
                refine ⟨1014492933704595843180533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676328622469730562120355 1014492933704595843180533)
                ·
                  refine ⟨95108712534805860298175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1014492933704595843180533 95108712534805860298175)
                  ·
                    rfl

theorem cell21_416753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_416753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416753 prefixEnd_416753 := by exact prefixLift 416753
  have htrace : WordTrace (prefixWord ++ tailWord_416753) baseStart_416753 baseEnd_416753 := by
    simpa [prefixWord, tailWord_416753, baseEnd_416753] using wordTrace_append hprefix tailTrace_416753
  have hstable : (prefixWord ++ tailWord_416753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416753).length < 2 ^ (prefixWord ++ tailWord_416753).sum := by decide
  have hdescent : baseEnd_416753 < baseStart_416753 := by decide
  rcases family_descends (prefixWord ++ tailWord_416753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416860 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_416860 : Nat := 118140960795 + 416860 * 2 ^ 59
def prefixEnd_416860 : Nat := 4983230072969 + 3 ^ 40 * 416860 * 2
def baseEnd_416860 : Nat := 95133131392597452014623

theorem tailTrace_416860 : CollatzResearch.WordTrace tailWord_416860 prefixEnd_416860 95133131392597452014623 := by
  unfold tailWord_416860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602066634897444432532017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10136088846529925910042689 7602066634897444432532017)
  ·
    refine ⟨5701549976173083324399013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7602066634897444432532017 5701549976173083324399013)
    ·
      refine ⟨1069040620532453123324815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5701549976173083324399013 1069040620532453123324815)
      ·
        refine ⟨1603560930798679684987223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069040620532453123324815 1603560930798679684987223)
        ·
          refine ⟨2405341396198019527480835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603560930798679684987223 2405341396198019527480835)
          ·
            refine ⟨3608012094297029291221253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405341396198019527480835 3608012094297029291221253)
            ·
              refine ⟨676502267680692992103985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3608012094297029291221253 676502267680692992103985)
              ·
                refine ⟨507376700760519744077989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676502267680692992103985 507376700760519744077989)
                ·
                  refine ⟨95133131392597452014623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507376700760519744077989 95133131392597452014623)
                  ·
                    rfl

theorem cell21_416860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_416860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416860 prefixEnd_416860 := by exact prefixLift 416860
  have htrace : WordTrace (prefixWord ++ tailWord_416860) baseStart_416860 baseEnd_416860 := by
    simpa [prefixWord, tailWord_416860, baseEnd_416860] using wordTrace_append hprefix tailTrace_416860
  have hstable : (prefixWord ++ tailWord_416860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416860).length < 2 ^ (prefixWord ++ tailWord_416860).sum := by decide
  have hdescent : baseEnd_416860 < baseStart_416860 := by decide
  rcases family_descends (prefixWord ++ tailWord_416860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416874 : List Nat := [3, 1, 3, 2, 2, 1, 3, 6]
def baseStart_416874 : Nat := 118140960795 + 416874 * 2 ^ 59
def prefixEnd_416874 : Nat := 4983230072969 + 3 ^ 40 * 416874 * 2
def baseEnd_416874 : Nat := 31712108794445512927087

theorem tailTrace_416874 : CollatzResearch.WordTrace tailWord_416874 prefixEnd_416874 31712108794445512927087 := by
  unfold tailWord_416874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3801160972936042314018419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10136429261162779504049117 3801160972936042314018419)
  ·
    refine ⟨5701741459404063471027629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3801160972936042314018419 5701741459404063471027629)
    ·
      refine ⟨2138153047276523801635361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5701741459404063471027629 2138153047276523801635361)
      ·
        refine ⟨1603614785457392851226521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138153047276523801635361 1603614785457392851226521)
        ·
          refine ⟨1202711089093044638419891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603614785457392851226521 1202711089093044638419891)
          ·
            refine ⟨1804066633639566957629837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202711089093044638419891 1804066633639566957629837)
            ·
              refine ⟨676524987614837609111189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804066633639566957629837 676524987614837609111189)
              ·
                refine ⟨31712108794445512927087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 676524987614837609111189 31712108794445512927087)
                ·
                  rfl

theorem cell21_416874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_416874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416874 prefixEnd_416874 := by exact prefixLift 416874
  have htrace : WordTrace (prefixWord ++ tailWord_416874) baseStart_416874 baseEnd_416874 := by
    simpa [prefixWord, tailWord_416874, baseEnd_416874] using wordTrace_append hprefix tailTrace_416874
  have hstable : (prefixWord ++ tailWord_416874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416874).length < 2 ^ (prefixWord ++ tailWord_416874).sum := by decide
  have hdescent : baseEnd_416874 < baseStart_416874 := by decide
  rcases family_descends (prefixWord ++ tailWord_416874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416905 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 3]
def baseStart_416905 : Nat := 118140960795 + 416905 * 2 ^ 59
def prefixEnd_416905 : Nat := 4983230072969 + 3 ^ 40 * 416905 * 2
def baseEnd_416905 : Nat := 95143401005687373764531

theorem tailTrace_416905 : CollatzResearch.WordTrace tailWord_416905 prefixEnd_416905 95143401005687373764531 := by
  unfold tailWord_416905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205774554631861550452169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10137183036421241033634779 15205774554631861550452169)
  ·
    refine ⟨11404330915973896162839127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15205774554631861550452169 11404330915973896162839127)
    ·
      refine ⟨17106496373960844244258691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11404330915973896162839127 17106496373960844244258691)
      ·
        refine ⟨25659744560941266366388037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17106496373960844244258691 25659744560941266366388037)
        ·
          refine ⟨4811202105176487443697757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25659744560941266366388037 4811202105176487443697757)
          ·
            refine ⟨1804200789441182791386659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4811202105176487443697757 1804200789441182791386659)
            ·
              refine ⟨2706301184161774187079989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804200789441182791386659 2706301184161774187079989)
              ·
                refine ⟨253715736015166330038749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2706301184161774187079989 253715736015166330038749)
                ·
                  refine ⟨95143401005687373764531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253715736015166330038749 95143401005687373764531)
                  ·
                    rfl

theorem cell21_416905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_416905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416905 prefixEnd_416905 := by exact prefixLift 416905
  have htrace : WordTrace (prefixWord ++ tailWord_416905) baseStart_416905 baseEnd_416905 := by
    simpa [prefixWord, tailWord_416905, baseEnd_416905] using wordTrace_append hprefix tailTrace_416905
  have hstable : (prefixWord ++ tailWord_416905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416905).length < 2 ^ (prefixWord ++ tailWord_416905).sum := by decide
  have hdescent : baseEnd_416905 < baseStart_416905 := by decide
  rcases family_descends (prefixWord ++ tailWord_416905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416919 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 6]
def baseStart_416919 : Nat := 118140960795 + 416919 * 2 ^ 59
def prefixEnd_416919 : Nat := 4983230072969 + 3 ^ 40 * 416919 * 2
def baseEnd_416919 : Nat := 95146595996426460531169

theorem tailTrace_416919 : CollatzResearch.WordTrace tailWord_416919 prefixEnd_416919 95146595996426460531169 := by
  unfold tailWord_416919
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206285176581141941461811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10137523451054094627641207 15206285176581141941461811)
  ·
    refine ⟨22809427764871712912192717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15206285176581141941461811 22809427764871712912192717)
    ·
      refine ⟨8553535411826892342072269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22809427764871712912192717 8553535411826892342072269)
      ·
        refine ⟨3207575779435084628277101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8553535411826892342072269 3207575779435084628277101)
        ·
          refine ⟨1202840917288156735603913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3207575779435084628277101 1202840917288156735603913)
          ·
            refine ⟨902130687966117551702935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202840917288156735603913 902130687966117551702935)
            ·
              refine ⟨1353196031949176327554403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902130687966117551702935 1353196031949176327554403)
              ·
                refine ⟨2029794047923764491331605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353196031949176327554403 2029794047923764491331605)
                ·
                  refine ⟨95146595996426460531169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2029794047923764491331605 95146595996426460531169)
                  ·
                    rfl

theorem cell21_416919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_416919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416919 prefixEnd_416919 := by exact prefixLift 416919
  have htrace : WordTrace (prefixWord ++ tailWord_416919) baseStart_416919 baseEnd_416919 := by
    simpa [prefixWord, tailWord_416919, baseEnd_416919] using wordTrace_append hprefix tailTrace_416919
  have hstable : (prefixWord ++ tailWord_416919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416919).length < 2 ^ (prefixWord ++ tailWord_416919).sum := by decide
  have hdescent : baseEnd_416919 < baseStart_416919 := by decide
  rcases family_descends (prefixWord ++ tailWord_416919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416922 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_416922 : Nat := 118140960795 + 416922 * 2 ^ 59
def prefixEnd_416922 : Nat := 4983230072969 + 3 ^ 40 * 416922 * 2
def baseEnd_416922 : Nat := 95147280637299121981163

theorem tailTrace_416922 : CollatzResearch.WordTrace tailWord_416922 prefixEnd_416922 95147280637299121981163 := by
  unfold tailWord_416922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3801598648892568363455255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10137596397046848969214013 3801598648892568363455255)
  ·
    refine ⟨5702397973338852545182883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3801598648892568363455255 5702397973338852545182883)
    ·
      refine ⟨8553596960008278817774325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5702397973338852545182883 8553596960008278817774325)
      ·
        refine ⟨801899715000776139166343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8553596960008278817774325 801899715000776139166343)
        ·
          refine ⟨1202849572501164208749515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801899715000776139166343 1202849572501164208749515)
          ·
            refine ⟨1804274358751746313124273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202849572501164208749515 1804274358751746313124273)
            ·
              refine ⟨1353205769063809734843205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804274358751746313124273 1353205769063809734843205)
              ·
                refine ⟨253726081699464325283101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1353205769063809734843205 253726081699464325283101)
                ·
                  refine ⟨95147280637299121981163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253726081699464325283101 95147280637299121981163)
                  ·
                    rfl

theorem cell21_416922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_416922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416922 prefixEnd_416922 := by exact prefixLift 416922
  have htrace : WordTrace (prefixWord ++ tailWord_416922) baseStart_416922 baseEnd_416922 := by
    simpa [prefixWord, tailWord_416922, baseEnd_416922] using wordTrace_append hprefix tailTrace_416922
  have hstable : (prefixWord ++ tailWord_416922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416922).length < 2 ^ (prefixWord ++ tailWord_416922).sum := by decide
  have hdescent : baseEnd_416922 < baseStart_416922 := by decide
  rcases family_descends (prefixWord ++ tailWord_416922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416973 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 3]
def baseStart_416973 : Nat := 118140960795 + 416973 * 2 ^ 59
def prefixEnd_416973 : Nat := 4983230072969 + 3 ^ 40 * 416973 * 2
def baseEnd_416973 : Nat := 95158919532134366631059

theorem tailTrace_416973 : CollatzResearch.WordTrace tailWord_416973 prefixEnd_416973 95158919532134366631059 := by
  unfold tailWord_416973
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208254718385509163927573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10138836478923672775951715 15208254718385509163927573)
  ·
    refine ⟨712886939924320742059105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15208254718385509163927573 712886939924320742059105)
    ·
      refine ⟨534665204943240556544329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 712886939924320742059105 534665204943240556544329)
      ·
        refine ⟨400998903707430417408247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534665204943240556544329 400998903707430417408247)
        ·
          refine ⟨601498355561145626112371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400998903707430417408247 601498355561145626112371)
          ·
            refine ⟨902247533341718439168557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601498355561145626112371 902247533341718439168557)
            ·
              refine ⟨338342825003144414688209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 902247533341718439168557 338342825003144414688209)
              ·
                refine ⟨253757118752358311016157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338342825003144414688209 253757118752358311016157)
                ·
                  refine ⟨95158919532134366631059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253757118752358311016157 95158919532134366631059)
                  ·
                    rfl

theorem cell21_416973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_416973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416973 prefixEnd_416973 := by exact prefixLift 416973
  have htrace : WordTrace (prefixWord ++ tailWord_416973) baseStart_416973 baseEnd_416973 := by
    simpa [prefixWord, tailWord_416973, baseEnd_416973] using wordTrace_append hprefix tailTrace_416973
  have hstable : (prefixWord ++ tailWord_416973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416973).length < 2 ^ (prefixWord ++ tailWord_416973).sum := by decide
  have hdescent : baseEnd_416973 < baseStart_416973 := by decide
  rcases family_descends (prefixWord ++ tailWord_416973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416981 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 5]
def baseStart_416981 : Nat := 118140960795 + 416981 * 2 ^ 59
def prefixEnd_416981 : Nat := 4983230072969 + 3 ^ 40 * 416981 * 2
def baseEnd_416981 : Nat := 95160745241128130497709

theorem tailTrace_416981 : CollatzResearch.WordTrace tailWord_416981 prefixEnd_416981 95160745241128130497709 := by
  unfold tailWord_416981
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208546502356526530218797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10139031001571017686812531 15208546502356526530218797)
  ·
    refine ⟨5703204938383697448832049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15208546502356526530218797 5703204938383697448832049)
    ·
      refine ⟨4277403703787773086624037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5703204938383697448832049 4277403703787773086624037)
      ·
        refine ⟨802013194460207453742007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4277403703787773086624037 802013194460207453742007)
        ·
          refine ⟨1203019791690311180613011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802013194460207453742007 1203019791690311180613011)
          ·
            refine ⟨1804529687535466770919517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203019791690311180613011 1804529687535466770919517)
            ·
              refine ⟨676698632825800039094819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804529687535466770919517 676698632825800039094819)
              ·
                refine ⟨1015047949238700058642229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676698632825800039094819 1015047949238700058642229)
                ·
                  refine ⟨95160745241128130497709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015047949238700058642229 95160745241128130497709)
                  ·
                    rfl

theorem cell21_416981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_416981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_416981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_416981 prefixEnd_416981 := by exact prefixLift 416981
  have htrace : WordTrace (prefixWord ++ tailWord_416981) baseStart_416981 baseEnd_416981 := by
    simpa [prefixWord, tailWord_416981, baseEnd_416981] using wordTrace_append hprefix tailTrace_416981
  have hstable : (prefixWord ++ tailWord_416981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416981).length < 2 ^ (prefixWord ++ tailWord_416981).sum := by decide
  have hdescent : baseEnd_416981 < baseStart_416981 := by decide
  rcases family_descends (prefixWord ++ tailWord_416981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417026 : List Nat := [3, 4, 1, 1, 3, 9]
def baseStart_417026 : Nat := 118140960795 + 417026 * 2 ^ 59
def prefixEnd_417026 : Nat := 4983230072969 + 3 ^ 40 * 417026 * 2
def baseEnd_417026 : Nat := 3524852402008076009171

theorem tailTrace_417026 : CollatzResearch.WordTrace tailWord_417026 prefixEnd_417026 3524852402008076009171 := by
  unfold tailWord_417026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802546946798374803901733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10140125191462332810404621 3802546946798374803901733)
  ·
    refine ⟨712977552524695275731575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3802546946798374803901733 712977552524695275731575)
    ·
      refine ⟨1069466328787042913597363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 712977552524695275731575 1069466328787042913597363)
      ·
        refine ⟨1604199493180564370396045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069466328787042913597363 1604199493180564370396045)
        ·
          refine ⟨601574809942711638898517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1604199493180564370396045 601574809942711638898517)
          ·
            refine ⟨3524852402008076009171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 601574809942711638898517 3524852402008076009171)
            ·
              rfl

theorem cell21_417026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 9].length) (baseStart_417026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417026 prefixEnd_417026 := by exact prefixLift 417026
  have htrace : WordTrace (prefixWord ++ tailWord_417026) baseStart_417026 baseEnd_417026 := by
    simpa [prefixWord, tailWord_417026, baseEnd_417026] using wordTrace_append hprefix tailTrace_417026
  have hstable : (prefixWord ++ tailWord_417026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417026).length < 2 ^ (prefixWord ++ tailWord_417026).sum := by decide
  have hdescent : baseEnd_417026 < baseStart_417026 := by decide
  rcases family_descends (prefixWord ++ tailWord_417026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417032 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_417032 : Nat := 118140960795 + 417032 * 2 ^ 59
def prefixEnd_417032 : Nat := 4983230072969 + 3 ^ 40 * 417032 * 2
def baseEnd_417032 : Nat := 95172384135963375147605

theorem tailTrace_417032 : CollatzResearch.WordTrace tailWord_417032 prefixEnd_417032 95172384135963375147605 := by
  unfold tailWord_417032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605203312585881120162675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10140271083447841493550233 7605203312585881120162675)
  ·
    refine ⟨11407804968878821680244013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7605203312585881120162675 11407804968878821680244013)
    ·
      refine ⟨4277926863329558130091505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11407804968878821680244013 4277926863329558130091505)
      ·
        refine ⟨3208445147497168597568629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277926863329558130091505 3208445147497168597568629)
        ·
          refine ⟨300791732577859556022059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3208445147497168597568629 300791732577859556022059)
          ·
            refine ⟨451187598866789334033089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300791732577859556022059 451187598866789334033089)
            ·
              refine ⟨338390699150092000524817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451187598866789334033089 338390699150092000524817)
              ·
                refine ⟨253793024362569000393613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338390699150092000524817 253793024362569000393613)
                ·
                  refine ⟨95172384135963375147605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253793024362569000393613 95172384135963375147605)
                  ·
                    rfl

theorem cell21_417032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_417032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417032 prefixEnd_417032 := by exact prefixLift 417032
  have htrace : WordTrace (prefixWord ++ tailWord_417032) baseStart_417032 baseEnd_417032 := by
    simpa [prefixWord, tailWord_417032, baseEnd_417032] using wordTrace_append hprefix tailTrace_417032
  have hstable : (prefixWord ++ tailWord_417032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417032).length < 2 ^ (prefixWord ++ tailWord_417032).sum := by decide
  have hdescent : baseEnd_417032 < baseStart_417032 := by decide
  rcases family_descends (prefixWord ++ tailWord_417032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417074 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_417074 : Nat := 118140960795 + 417074 * 2 ^ 59
def prefixEnd_417074 : Nat := 4983230072969 + 3 ^ 40 * 417074 * 2
def baseEnd_417074 : Nat := 95181969108180635447519

theorem tailTrace_417074 : CollatzResearch.WordTrace tailWord_417074 prefixEnd_417074 95181969108180635447519 := by
  unfold tailWord_417074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802984622754900853338569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10141292327346402275569517 3802984622754900853338569)
  ·
    refine ⟨2852238467066175640003927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3802984622754900853338569 2852238467066175640003927)
    ·
      refine ⟨4278357700599263460005891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852238467066175640003927 4278357700599263460005891)
      ·
        refine ⟨6417536550898895190008837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4278357700599263460005891 6417536550898895190008837)
        ·
          refine ⟨1203288103293542848126657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6417536550898895190008837 1203288103293542848126657)
          ·
            refine ⟨902466077470157136094993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203288103293542848126657 902466077470157136094993)
            ·
              refine ⟨676849558102617852071245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902466077470157136094993 676849558102617852071245)
              ·
                refine ⟨253818584288481694526717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676849558102617852071245 253818584288481694526717)
                ·
                  refine ⟨95181969108180635447519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253818584288481694526717 95181969108180635447519)
                  ·
                    rfl

theorem cell21_417074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_417074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417074 prefixEnd_417074 := by exact prefixLift 417074
  have htrace : WordTrace (prefixWord ++ tailWord_417074) baseStart_417074 baseEnd_417074 := by
    simpa [prefixWord, tailWord_417074, baseEnd_417074] using wordTrace_append hprefix tailTrace_417074
  have hstable : (prefixWord ++ tailWord_417074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417074).length < 2 ^ (prefixWord ++ tailWord_417074).sum := by decide
  have hdescent : baseEnd_417074 < baseStart_417074 := by decide
  rcases family_descends (prefixWord ++ tailWord_417074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417175 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_417175 : Nat := 118140960795 + 417175 * 2 ^ 59
def prefixEnd_417175 : Nat := 4983230072969 + 3 ^ 40 * 417175 * 2
def baseEnd_417175 : Nat := 95205018684226904263979

theorem tailTrace_417175 : CollatzResearch.WordTrace tailWord_417175 prefixEnd_417175 95205018684226904263979 := by
  unfold tailWord_417175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15215622263653697662780979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10143748175769131775187319 15215622263653697662780979)
  ·
    refine ⟨22823433395480546494171469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15215622263653697662780979 22823433395480546494171469)
    ·
      refine ⟨8558787523305204935314301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22823433395480546494171469 8558787523305204935314301)
      ·
        refine ⟨3209545321239451850742863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8558787523305204935314301 3209545321239451850742863)
        ·
          refine ⟨4814317981859177776114295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209545321239451850742863 4814317981859177776114295)
          ·
            refine ⟨7221476972788766664171443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814317981859177776114295 7221476972788766664171443)
            ·
              refine ⟨10832215459183149996257165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221476972788766664171443 10832215459183149996257165)
              ·
                refine ⟨4062080797193681248596437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10832215459183149996257165 4062080797193681248596437)
                ·
                  refine ⟨95205018684226904263979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4062080797193681248596437 95205018684226904263979)
                  ·
                    rfl

theorem cell21_417175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_417175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417175 prefixEnd_417175 := by exact prefixLift 417175
  have htrace : WordTrace (prefixWord ++ tailWord_417175) baseStart_417175 baseEnd_417175 := by
    simpa [prefixWord, tailWord_417175, baseEnd_417175] using wordTrace_append hprefix tailTrace_417175
  have hstable : (prefixWord ++ tailWord_417175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417175).length < 2 ^ (prefixWord ++ tailWord_417175).sum := by decide
  have hdescent : baseEnd_417175 < baseStart_417175 := by decide
  rcases family_descends (prefixWord ++ tailWord_417175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417313 : List Nat := [1, 2, 3, 2, 2, 4, 7]
def baseStart_417313 : Nat := 118140960795 + 417313 * 2 ^ 59
def prefixEnd_417313 : Nat := 4983230072969 + 3 ^ 40 * 417313 * 2
def baseEnd_417313 : Nat := 10581834684929925662633

theorem tailTrace_417313 : CollatzResearch.WordTrace tailWord_417313 prefixEnd_417313 10581834684929925662633 := by
  unfold tailWord_417313
  simp only [CollatzResearch.WordTrace]
  refine ⟨15220655537153747231304593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10147103691435831487536395 15220655537153747231304593)
  ·
    refine ⟨11415491652865310423478445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15220655537153747231304593 11415491652865310423478445)
    ·
      refine ⟨4280809369824491408804417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11415491652865310423478445 4280809369824491408804417)
      ·
        refine ⟨3210607027368368556603313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4280809369824491408804417 3210607027368368556603313)
        ·
          refine ⟨2407955270526276417452485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210607027368368556603313 2407955270526276417452485)
          ·
            refine ⟨451491613223676828272341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2407955270526276417452485 451491613223676828272341)
            ·
              refine ⟨10581834684929925662633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 451491613223676828272341 10581834684929925662633)
              ·
                rfl

theorem cell21_417313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 7].length) (baseStart_417313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417313 prefixEnd_417313 := by exact prefixLift 417313
  have htrace : WordTrace (prefixWord ++ tailWord_417313) baseStart_417313 baseEnd_417313 := by
    simpa [prefixWord, tailWord_417313, baseEnd_417313] using wordTrace_append hprefix tailTrace_417313
  have hstable : (prefixWord ++ tailWord_417313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417313).length < 2 ^ (prefixWord ++ tailWord_417313).sum := by decide
  have hdescent : baseEnd_417313 < baseStart_417313 := by decide
  rcases family_descends (prefixWord ++ tailWord_417313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417403 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_417403 : Nat := 118140960795 + 417403 * 2 ^ 59
def prefixEnd_417403 : Nat := 4983230072969 + 3 ^ 40 * 417403 * 2
def baseEnd_417403 : Nat := 95257051390549174463513

theorem tailTrace_417403 : CollatzResearch.WordTrace tailWord_417403 prefixEnd_417403 95257051390549174463513 := by
  unfold tailWord_417403
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223938106827692602080863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10149292071218461734720575 15223938106827692602080863)
  ·
    refine ⟨22835907160241538903121295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15223938106827692602080863 22835907160241538903121295)
    ·
      refine ⟨34253860740362308354681943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22835907160241538903121295 34253860740362308354681943)
      ·
        refine ⟨51380791110543462532022915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34253860740362308354681943 51380791110543462532022915)
        ·
          refine ⟨77071186665815193798034373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51380791110543462532022915 77071186665815193798034373)
          ·
            refine ⟨14450847499840348837131445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77071186665815193798034373 14450847499840348837131445)
            ·
              refine ⟨1354766953110032703481073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14450847499840348837131445 1354766953110032703481073)
              ·
                refine ⟨1016075214832524527610805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354766953110032703481073 1016075214832524527610805)
                ·
                  refine ⟨95257051390549174463513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016075214832524527610805 95257051390549174463513)
                  ·
                    rfl

theorem cell21_417403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_417403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417403 prefixEnd_417403 := by exact prefixLift 417403
  have htrace : WordTrace (prefixWord ++ tailWord_417403) baseStart_417403 baseEnd_417403 := by
    simpa [prefixWord, tailWord_417403, baseEnd_417403] using wordTrace_append hprefix tailTrace_417403
  have hstable : (prefixWord ++ tailWord_417403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417403).length < 2 ^ (prefixWord ++ tailWord_417403).sum := by decide
  have hdescent : baseEnd_417403 < baseStart_417403 := by decide
  rcases family_descends (prefixWord ++ tailWord_417403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417465 : List Nat := [1, 2, 1, 4, 1, 1, 6, 5]
def baseStart_417465 : Nat := 118140960795 + 417465 * 2 ^ 59
def prefixEnd_417465 : Nat := 4983230072969 + 3 ^ 40 * 417465 * 2
def baseEnd_417465 : Nat := 31757066878416948143351

theorem tailTrace_417465 : CollatzResearch.WordTrace tailWord_417465 prefixEnd_417465 31757066878416948143351 := by
  unfold tailWord_417465
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226199432603077190837849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10150799621735384793891899 15226199432603077190837849)
  ·
    refine ⟨11419649574452307893128387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15226199432603077190837849 11419649574452307893128387)
    ·
      refine ⟨17129474361678461839692581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11419649574452307893128387 17129474361678461839692581)
      ·
        refine ⟨3211776442814711594942359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17129474361678461839692581 3211776442814711594942359)
        ·
          refine ⟨4817664664222067392413539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211776442814711594942359 4817664664222067392413539)
          ·
            refine ⟨7226496996333101088620309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817664664222067392413539 7226496996333101088620309)
            ·
              refine ⟨338742046703114113529077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7226496996333101088620309 338742046703114113529077)
              ·
                refine ⟨31757066878416948143351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338742046703114113529077 31757066878416948143351)
                ·
                  rfl

theorem cell21_417465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 5].length) (baseStart_417465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417465 prefixEnd_417465 := by exact prefixLift 417465
  have htrace : WordTrace (prefixWord ++ tailWord_417465) baseStart_417465 baseEnd_417465 := by
    simpa [prefixWord, tailWord_417465, baseEnd_417465] using wordTrace_append hprefix tailTrace_417465
  have hstable : (prefixWord ++ tailWord_417465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417465).length < 2 ^ (prefixWord ++ tailWord_417465).sum := by decide
  have hdescent : baseEnd_417465 < baseStart_417465 := by decide
  rcases family_descends (prefixWord ++ tailWord_417465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417482 : List Nat := [3, 1, 2, 1, 6, 1, 7]
def baseStart_417482 : Nat := 118140960795 + 417482 * 2 ^ 59
def prefixEnd_417482 : Nat := 4983230072969 + 3 ^ 40 * 417482 * 2
def baseEnd_417482 : Nat := 10586120029651399182965

theorem tailTrace_417482 : CollatzResearch.WordTrace tailWord_417482 prefixEnd_417482 10586120029651399182965 := by
  unfold tailWord_417482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806704868385372273551675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10151212982360992729471133 3806704868385372273551675)
  ·
    refine ⟨5710057302578058410327513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3806704868385372273551675 5710057302578058410327513)
    ·
      refine ⟨4282542976933543807745635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5710057302578058410327513 4282542976933543807745635)
      ·
        refine ⟨6423814465400315711618453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4282542976933543807745635 6423814465400315711618453)
        ·
          refine ⟨301116303065639798982115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6423814465400315711618453 301116303065639798982115)
          ·
            refine ⟨451674454598459698473173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301116303065639798982115 451674454598459698473173)
            ·
              refine ⟨10586120029651399182965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 451674454598459698473173 10586120029651399182965)
              ·
                rfl

theorem cell21_417482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 7].length) (baseStart_417482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417482 prefixEnd_417482 := by exact prefixLift 417482
  have htrace : WordTrace (prefixWord ++ tailWord_417482) baseStart_417482 baseEnd_417482 := by
    simpa [prefixWord, tailWord_417482, baseEnd_417482] using wordTrace_append hprefix tailTrace_417482
  have hstable : (prefixWord ++ tailWord_417482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417482).length < 2 ^ (prefixWord ++ tailWord_417482).sum := by decide
  have hdescent : baseEnd_417482 < baseStart_417482 := by decide
  rcases family_descends (prefixWord ++ tailWord_417482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417572 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_417572 : Nat := 118140960795 + 417572 * 2 ^ 59
def prefixEnd_417572 : Nat := 4983230072969 + 3 ^ 40 * 417572 * 2
def baseEnd_417572 : Nat := 95295619493042436146501

theorem tailTrace_417572 : CollatzResearch.WordTrace tailWord_417572 prefixEnd_417572 95295619493042436146501 := by
  unfold tailWord_417572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615051021607717232491485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10153401362143622976655313 7615051021607717232491485)
  ·
    refine ⟨2855644133102893962184307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7615051021607717232491485 2855644133102893962184307)
    ·
      refine ⟨4283466199654340943276461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855644133102893962184307 4283466199654340943276461)
      ·
        refine ⟨1606299824870377853728673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4283466199654340943276461 1606299824870377853728673)
        ·
          refine ⟨1204724868652783390296505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1606299824870377853728673 1204724868652783390296505)
          ·
            refine ⟨903543651489587542722379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204724868652783390296505 903543651489587542722379)
            ·
              refine ⟨1355315477234381314083569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903543651489587542722379 1355315477234381314083569)
              ·
                refine ⟨1016486607925785985562677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355315477234381314083569 1016486607925785985562677)
                ·
                  refine ⟨95295619493042436146501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016486607925785985562677 95295619493042436146501)
                  ·
                    rfl

theorem cell21_417572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_417572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417572 prefixEnd_417572 := by exact prefixLift 417572
  have htrace : WordTrace (prefixWord ++ tailWord_417572) baseStart_417572 baseEnd_417572 := by
    simpa [prefixWord, tailWord_417572, baseEnd_417572] using wordTrace_append hprefix tailTrace_417572
  have hstable : (prefixWord ++ tailWord_417572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417572).length < 2 ^ (prefixWord ++ tailWord_417572).sum := by decide
  have hdescent : baseEnd_417572 < baseStart_417572 := by decide
  rcases family_descends (prefixWord ++ tailWord_417572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417603 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 4]
def baseStart_417603 : Nat := 118140960795 + 417603 * 2 ^ 59
def prefixEnd_417603 : Nat := 4983230072969 + 3 ^ 40 * 417603 * 2
def baseEnd_417603 : Nat := 95302694115393271129771

theorem tailTrace_417603 : CollatzResearch.WordTrace tailWord_417603 prefixEnd_417603 95302694115393271129771 := by
  unfold tailWord_417603
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231232706103126759361463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10154155137402084506240975 15231232706103126759361463)
  ·
    refine ⟨22846849059154690139042195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15231232706103126759361463 22846849059154690139042195)
    ·
      refine ⟨34270273588732035208563293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22846849059154690139042195 34270273588732035208563293)
      ·
        refine ⟨12851352595774513203211235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34270273588732035208563293 12851352595774513203211235)
        ·
          refine ⟨19277028893661769804816853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12851352595774513203211235 19277028893661769804816853)
          ·
            refine ⟨451805364695197729800395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19277028893661769804816853 451805364695197729800395)
            ·
              refine ⟨677708047042796594700593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451805364695197729800395 677708047042796594700593)
              ·
                refine ⟨508281035282097446025445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677708047042796594700593 508281035282097446025445)
                ·
                  refine ⟨95302694115393271129771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508281035282097446025445 95302694115393271129771)
                  ·
                    rfl

theorem cell21_417603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].length) (baseStart_417603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417603 prefixEnd_417603 := by exact prefixLift 417603
  have htrace : WordTrace (prefixWord ++ tailWord_417603) baseStart_417603 baseEnd_417603 := by
    simpa [prefixWord, tailWord_417603, baseEnd_417603] using wordTrace_append hprefix tailTrace_417603
  have hstable : (prefixWord ++ tailWord_417603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417603).length < 2 ^ (prefixWord ++ tailWord_417603).sum := by decide
  have hdescent : baseEnd_417603 < baseStart_417603 := by decide
  rcases family_descends (prefixWord ++ tailWord_417603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417606 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_417606 : Nat := 118140960795 + 417606 * 2 ^ 59
def prefixEnd_417606 : Nat := 4983230072969 + 3 ^ 40 * 417606 * 2
def baseEnd_417606 : Nat := 95303378756265932579765

theorem tailTrace_417606 : CollatzResearch.WordTrace tailWord_417606 prefixEnd_417606 95303378756265932579765 := by
  unfold tailWord_417606
  simp only [CollatzResearch.WordTrace]
  refine ⟨475979441409133070991271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10154228083394838847813781 475979441409133070991271)
  ·
    refine ⟨713969162113699606486907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 475979441409133070991271 713969162113699606486907)
    ·
      refine ⟨1070953743170549409730361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 713969162113699606486907 1070953743170549409730361)
      ·
        refine ⟨803215307377912057297771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070953743170549409730361 803215307377912057297771)
        ·
          refine ⟨1204822961066868085946657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803215307377912057297771 1204822961066868085946657)
          ·
            refine ⟨903617220800151064459993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204822961066868085946657 903617220800151064459993)
            ·
              refine ⟨677712915600113298344995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903617220800151064459993 677712915600113298344995)
              ·
                refine ⟨1016569373400169947517493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677712915600113298344995 1016569373400169947517493)
                ·
                  refine ⟨95303378756265932579765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016569373400169947517493 95303378756265932579765)
                  ·
                    rfl

theorem cell21_417606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_417606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417606 prefixEnd_417606 := by exact prefixLift 417606
  have htrace : WordTrace (prefixWord ++ tailWord_417606) baseStart_417606 baseEnd_417606 := by
    simpa [prefixWord, tailWord_417606, baseEnd_417606] using wordTrace_append hprefix tailTrace_417606
  have hstable : (prefixWord ++ tailWord_417606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417606).length < 2 ^ (prefixWord ++ tailWord_417606).sum := by decide
  have hdescent : baseEnd_417606 < baseStart_417606 := by decide
  rcases family_descends (prefixWord ++ tailWord_417606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417620 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_417620 : Nat := 118140960795 + 417620 * 2 ^ 59
def prefixEnd_417620 : Nat := 4983230072969 + 3 ^ 40 * 417620 * 2
def baseEnd_417620 : Nat := 95306573747005019346403

theorem tailTrace_417620 : CollatzResearch.WordTrace tailWord_417620 prefixEnd_417620 95306573747005019346403 := by
  unfold tailWord_417620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615926373520769331365157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10154568498027692441820209 7615926373520769331365157)
  ·
    refine ⟨1427986195035144249630967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7615926373520769331365157 1427986195035144249630967)
    ·
      refine ⟨2141979292552716374446451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1427986195035144249630967 2141979292552716374446451)
      ·
        refine ⟨3212968938829074561669677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141979292552716374446451 3212968938829074561669677)
        ·
          refine ⟨1204863352060902960626129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3212968938829074561669677 1204863352060902960626129)
          ·
            refine ⟨903647514045677220469597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204863352060902960626129 903647514045677220469597)
            ·
              refine ⟨338867817767128957676099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 903647514045677220469597 338867817767128957676099)
              ·
                refine ⟨508301726650693436514149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338867817767128957676099 508301726650693436514149)
                ·
                  refine ⟨95306573747005019346403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508301726650693436514149 95306573747005019346403)
                  ·
                    rfl

theorem cell21_417620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_417620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417620 prefixEnd_417620 := by exact prefixLift 417620
  have htrace : WordTrace (prefixWord ++ tailWord_417620) baseStart_417620 baseEnd_417620 := by
    simpa [prefixWord, tailWord_417620, baseEnd_417620] using wordTrace_append hprefix tailTrace_417620
  have hstable : (prefixWord ++ tailWord_417620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417620).length < 2 ^ (prefixWord ++ tailWord_417620).sum := by decide
  have hdescent : baseEnd_417620 < baseStart_417620 := by decide
  rcases family_descends (prefixWord ++ tailWord_417620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417631 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_417631 : Nat := 118140960795 + 417631 * 2 ^ 59
def prefixEnd_417631 : Nat := 4983230072969 + 3 ^ 40 * 417631 * 2
def baseEnd_417631 : Nat := 95309084096871444663047

theorem tailTrace_417631 : CollatzResearch.WordTrace tailWord_417631 prefixEnd_417631 95309084096871444663047 := by
  unfold tailWord_417631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232253950001687541380747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10154835966667791694253831 15232253950001687541380747)
  ·
    refine ⟨22848380925002531312071121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15232253950001687541380747 22848380925002531312071121)
    ·
      refine ⟨17136285693751898484053341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22848380925002531312071121 17136285693751898484053341)
      ·
        refine ⟨6426107135156961931520003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17136285693751898484053341 6426107135156961931520003)
        ·
          refine ⟨9639160702735442897280005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426107135156961931520003 9639160702735442897280005)
          ·
            refine ⟨1807342631762895543240001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9639160702735442897280005 1807342631762895543240001)
            ·
              refine ⟨1355506973822171657430001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807342631762895543240001 1355506973822171657430001)
              ·
                refine ⟨1016630230366628743072501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355506973822171657430001 1016630230366628743072501)
                ·
                  refine ⟨95309084096871444663047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016630230366628743072501 95309084096871444663047)
                  ·
                    rfl

theorem cell21_417631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_417631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417631 prefixEnd_417631 := by exact prefixLift 417631
  have htrace : WordTrace (prefixWord ++ tailWord_417631) baseStart_417631 baseEnd_417631 := by
    simpa [prefixWord, tailWord_417631, baseEnd_417631] using wordTrace_append hprefix tailTrace_417631
  have hstable : (prefixWord ++ tailWord_417631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417631).length < 2 ^ (prefixWord ++ tailWord_417631).sum := by decide
  have hdescent : baseEnd_417631 < baseStart_417631 := by decide
  rcases family_descends (prefixWord ++ tailWord_417631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417634 : List Nat := [3, 3, 2, 1, 2, 1, 4, 5]
def baseStart_417634 : Nat := 118140960795 + 417634 * 2 ^ 59
def prefixEnd_417634 : Nat := 4983230072969 + 3 ^ 40 * 417634 * 2
def baseEnd_417634 : Nat := 31769922912581368704347

theorem tailTrace_417634 : CollatzResearch.WordTrace tailWord_417634 prefixEnd_417634 31769922912581368704347 := by
  unfold tailWord_417634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808090842247704763434989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10154908912660546035826637 3808090842247704763434989)
  ·
    refine ⟨1428034065842889286288121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3808090842247704763434989 1428034065842889286288121)
    ·
      refine ⟨1071025549382166964716091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1428034065842889286288121 1071025549382166964716091)
      ·
        refine ⟨1606538324073250447074137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071025549382166964716091 1606538324073250447074137)
        ·
          refine ⟨1204903743054937835305603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1606538324073250447074137 1204903743054937835305603)
          ·
            refine ⟨1807355614582406752958405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204903743054937835305603 1807355614582406752958405)
            ·
              refine ⟨338879177734201266179701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1807355614582406752958405 338879177734201266179701)
              ·
                refine ⟨31769922912581368704347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338879177734201266179701 31769922912581368704347)
                ·
                  rfl

theorem cell21_417634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_417634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417634 prefixEnd_417634 := by exact prefixLift 417634
  have htrace : WordTrace (prefixWord ++ tailWord_417634) baseStart_417634 baseEnd_417634 := by
    simpa [prefixWord, tailWord_417634, baseEnd_417634] using wordTrace_append hprefix tailTrace_417634
  have hstable : (prefixWord ++ tailWord_417634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417634).length < 2 ^ (prefixWord ++ tailWord_417634).sum := by decide
  have hdescent : baseEnd_417634 < baseStart_417634 := by decide
  rcases family_descends (prefixWord ++ tailWord_417634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417710 : List Nat := [4, 1, 5, 1, 10]
def baseStart_417710 : Nat := 118140960795 + 417710 * 2 ^ 59
def prefixEnd_417710 : Nat := 4983230072969 + 3 ^ 40 * 417710 * 2
def baseEnd_417710 : Nat := 1176877937940553862299

theorem tailTrace_417710 : CollatzResearch.WordTrace tailWord_417710 prefixEnd_417710 1176877937940553862299 := by
  unfold tailWord_417710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904391914589435504188323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10156756877810322689004389 1904391914589435504188323)
  ·
    refine ⟨2856587871884153256282485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1904391914589435504188323 2856587871884153256282485)
    ·
      refine ⟨267805112989139367776483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2856587871884153256282485 267805112989139367776483)
      ·
        refine ⟨401707669483709051664725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267805112989139367776483 401707669483709051664725)
        ·
          refine ⟨1176877937940553862299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 401707669483709051664725 1176877937940553862299)
          ·
            rfl

theorem cell21_417710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 10].length) (baseStart_417710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417710 prefixEnd_417710 := by exact prefixLift 417710
  have htrace : WordTrace (prefixWord ++ tailWord_417710) baseStart_417710 baseEnd_417710 := by
    simpa [prefixWord, tailWord_417710, baseEnd_417710] using wordTrace_append hprefix tailTrace_417710
  have hstable : (prefixWord ++ tailWord_417710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417710).length < 2 ^ (prefixWord ++ tailWord_417710).sum := by decide
  have hdescent : baseEnd_417710 < baseStart_417710 := by decide
  rcases family_descends (prefixWord ++ tailWord_417710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417716 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_417716 : Nat := 118140960795 + 417716 * 2 ^ 59
def prefixEnd_417716 : Nat := 4983230072969 + 3 ^ 40 * 417716 * 2
def baseEnd_417716 : Nat := 95328482254930185746207

theorem tailTrace_417716 : CollatzResearch.WordTrace tailWord_417716 prefixEnd_417716 95328482254930185746207 := by
  unfold tailWord_417716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7617677077346873529112501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10156902769795831372150001 7617677077346873529112501)
  ·
    refine ⟨714157226001269393354297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7617677077346873529112501 714157226001269393354297)
    ·
      refine ⟨535617919500952045015723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 714157226001269393354297 535617919500952045015723)
      ·
        refine ⟨803426879251428067523585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535617919500952045015723 803426879251428067523585)
        ·
          refine ⟨602570159438571050642689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803426879251428067523585 602570159438571050642689)
          ·
            refine ⟨451927619578928287982017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602570159438571050642689 451927619578928287982017)
            ·
              refine ⟨338945714684196215986513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451927619578928287982017 338945714684196215986513)
              ·
                refine ⟨254209286013147161989885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338945714684196215986513 254209286013147161989885)
                ·
                  refine ⟨95328482254930185746207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254209286013147161989885 95328482254930185746207)
                  ·
                    rfl

theorem cell21_417716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_417716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417716 prefixEnd_417716 := by exact prefixLift 417716
  have htrace : WordTrace (prefixWord ++ tailWord_417716) baseStart_417716 baseEnd_417716 := by
    simpa [prefixWord, tailWord_417716, baseEnd_417716] using wordTrace_append hprefix tailTrace_417716
  have hstable : (prefixWord ++ tailWord_417716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417716).length < 2 ^ (prefixWord ++ tailWord_417716).sum := by decide
  have hdescent : baseEnd_417716 < baseStart_417716 := by decide
  rcases family_descends (prefixWord ++ tailWord_417716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417738 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_417738 : Nat := 118140960795 + 417738 * 2 ^ 59
def prefixEnd_417738 : Nat := 4983230072969 + 3 ^ 40 * 417738 * 2
def baseEnd_417738 : Nat := 95333502954663036379495

theorem tailTrace_417738 : CollatzResearch.WordTrace tailWord_417738 prefixEnd_417738 95333502954663036379495 := by
  unfold tailWord_417738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809039140153511203881467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10157437707076029877017245 3809039140153511203881467)
  ·
    refine ⟨5713558710230266805822201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3809039140153511203881467 5713558710230266805822201)
    ·
      refine ⟨4285169032672700104366651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5713558710230266805822201 4285169032672700104366651)
      ·
        refine ⟨6427753549009050156549977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285169032672700104366651 6427753549009050156549977)
        ·
          refine ⟨4820815161756787617412483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6427753549009050156549977 4820815161756787617412483)
          ·
            refine ⟨7231222742635181426118725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820815161756787617412483 7231222742635181426118725)
            ·
              refine ⟨1355854264244096517397261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7231222742635181426118725 1355854264244096517397261)
              ·
                refine ⟨508445349091536194023973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355854264244096517397261 508445349091536194023973)
                ·
                  refine ⟨95333502954663036379495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508445349091536194023973 95333502954663036379495)
                  ·
                    rfl

theorem cell21_417738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_417738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417738 prefixEnd_417738 := by exact prefixLift 417738
  have htrace : WordTrace (prefixWord ++ tailWord_417738) baseStart_417738 baseEnd_417738 := by
    simpa [prefixWord, tailWord_417738, baseEnd_417738] using wordTrace_append hprefix tailTrace_417738
  have hstable : (prefixWord ++ tailWord_417738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417738).length < 2 ^ (prefixWord ++ tailWord_417738).sum := by decide
  have hdescent : baseEnd_417738 < baseStart_417738 := by decide
  rcases family_descends (prefixWord ++ tailWord_417738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417834 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_417834 : Nat := 118140960795 + 417834 * 2 ^ 59
def prefixEnd_417834 : Nat := 4983230072969 + 3 ^ 40 * 417834 * 2
def baseEnd_417834 : Nat := 95355411462588202779299

theorem tailTrace_417834 : CollatzResearch.WordTrace tailWord_417834 prefixEnd_417834 95355411462588202779299 := by
  unfold tailWord_417834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809914492066563302755139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10159771978844168807347037 3809914492066563302755139)
  ·
    refine ⟨5714871738099844954132709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3809914492066563302755139 5714871738099844954132709)
    ·
      refine ⟨1071538450893720928899883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5714871738099844954132709 1071538450893720928899883)
      ·
        refine ⟨1607307676340581393349825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071538450893720928899883 1607307676340581393349825)
        ·
          refine ⟨1205480757255436045012369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607307676340581393349825 1205480757255436045012369)
          ·
            refine ⟨904110567941577033759277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1205480757255436045012369 904110567941577033759277)
            ·
              refine ⟨339041462978091387659729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 904110567941577033759277 339041462978091387659729)
              ·
                refine ⟨254281097233568540744797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339041462978091387659729 254281097233568540744797)
                ·
                  refine ⟨95355411462588202779299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254281097233568540744797 95355411462588202779299)
                  ·
                    rfl

theorem cell21_417834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_417834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417834 prefixEnd_417834 := by exact prefixLift 417834
  have htrace : WordTrace (prefixWord ++ tailWord_417834) baseStart_417834 baseEnd_417834 := by
    simpa [prefixWord, tailWord_417834, baseEnd_417834] using wordTrace_append hprefix tailTrace_417834
  have hstable : (prefixWord ++ tailWord_417834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417834).length < 2 ^ (prefixWord ++ tailWord_417834).sum := by decide
  have hdescent : baseEnd_417834 < baseStart_417834 := by decide
  rcases family_descends (prefixWord ++ tailWord_417834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417848 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_417848 : Nat := 118140960795 + 417848 * 2 ^ 59
def prefixEnd_417848 : Nat := 4983230072969 + 3 ^ 40 * 417848 * 2
def baseEnd_417848 : Nat := 95358606453327289545937

theorem tailTrace_417848 : CollatzResearch.WordTrace tailWord_417848 prefixEnd_417848 95358606453327289545937 := by
  unfold tailWord_417848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620084295107766801015099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10160112393477022401353465 7620084295107766801015099)
  ·
    refine ⟨11430126442661650201522649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7620084295107766801015099 11430126442661650201522649)
    ·
      refine ⟨8572594831996237651141987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11430126442661650201522649 8572594831996237651141987)
      ·
        refine ⟨12858892247994356476712981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572594831996237651141987 12858892247994356476712981)
        ·
          refine ⟨602760574124735459845921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12858892247994356476712981 602760574124735459845921)
          ·
            refine ⟨452070430593551594884441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602760574124735459845921 452070430593551594884441)
            ·
              refine ⟨339052822945163696163331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452070430593551594884441 339052822945163696163331)
              ·
                refine ⟨508579234417745544244997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339052822945163696163331 508579234417745544244997)
                ·
                  refine ⟨95358606453327289545937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508579234417745544244997 95358606453327289545937)
                  ·
                    rfl

theorem cell21_417848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_417848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417848 prefixEnd_417848 := by exact prefixLift 417848
  have htrace : WordTrace (prefixWord ++ tailWord_417848) baseStart_417848 baseEnd_417848 := by
    simpa [prefixWord, tailWord_417848, baseEnd_417848] using wordTrace_append hprefix tailTrace_417848
  have hstable : (prefixWord ++ tailWord_417848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417848).length < 2 ^ (prefixWord ++ tailWord_417848).sum := by decide
  have hdescent : baseEnd_417848 < baseStart_417848 := by decide
  rcases family_descends (prefixWord ++ tailWord_417848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417876 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_417876 : Nat := 118140960795 + 417876 * 2 ^ 59
def prefixEnd_417876 : Nat := 4983230072969 + 3 ^ 40 * 417876 * 2
def baseEnd_417876 : Nat := 95364996434805463079213

theorem tailTrace_417876 : CollatzResearch.WordTrace tailWord_417876 prefixEnd_417876 95364996434805463079213 := by
  unfold tailWord_417876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620594917057047192024741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10160793222742729589366321 7620594917057047192024741)
  ·
    refine ⟨1428861546948196348504639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7620594917057047192024741 1428861546948196348504639)
    ·
      refine ⟨2143292320422294522756959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428861546948196348504639 2143292320422294522756959)
      ·
        refine ⟨3214938480633441784135439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143292320422294522756959 3214938480633441784135439)
        ·
          refine ⟨4822407720950162676203159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214938480633441784135439 4822407720950162676203159)
          ·
            refine ⟨7233611581425244014304739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822407720950162676203159 7233611581425244014304739)
            ·
              refine ⟨10850417372137866021457109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233611581425244014304739 10850417372137866021457109)
              ·
                refine ⟨254306657159481234877901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10850417372137866021457109 254306657159481234877901)
                ·
                  refine ⟨95364996434805463079213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254306657159481234877901 95364996434805463079213)
                  ·
                    rfl

theorem cell21_417876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_417876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417876 prefixEnd_417876 := by exact prefixLift 417876
  have htrace : WordTrace (prefixWord ++ tailWord_417876) baseStart_417876 baseEnd_417876 := by
    simpa [prefixWord, tailWord_417876, baseEnd_417876] using wordTrace_append hprefix tailTrace_417876
  have hstable : (prefixWord ++ tailWord_417876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417876).length < 2 ^ (prefixWord ++ tailWord_417876).sum := by decide
  have hdescent : baseEnd_417876 < baseStart_417876 := by decide
  rcases family_descends (prefixWord ++ tailWord_417876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417893 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 3]
def baseStart_417893 : Nat := 118140960795 + 417893 * 2 ^ 59
def prefixEnd_417893 : Nat := 4983230072969 + 3 ^ 40 * 417893 * 2
def baseEnd_417893 : Nat := 95368876066417211295845

theorem tailTrace_417893 : CollatzResearch.WordTrace tailWord_417893 prefixEnd_417893 95368876066417211295845 := by
  unfold tailWord_417893
  simp only [CollatzResearch.WordTrace]
  refine ⟨15241809875052506287418333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10161206583368337524945555 15241809875052506287418333)
  ·
    refine ⟨5715678703144689857781875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15241809875052506287418333 5715678703144689857781875)
    ·
      refine ⟨8573518054717034786672813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5715678703144689857781875 8573518054717034786672813)
      ·
        refine ⟨3215069270518888045002305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8573518054717034786672813 3215069270518888045002305)
        ·
          refine ⟨2411301952889166033751729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3215069270518888045002305 2411301952889166033751729)
          ·
            refine ⟨1808476464666874525313797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411301952889166033751729 1808476464666874525313797)
            ·
              refine ⟨339089337125038973496337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1808476464666874525313797 339089337125038973496337)
              ·
                refine ⟨254317002843779230122253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339089337125038973496337 254317002843779230122253)
                ·
                  refine ⟨95368876066417211295845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254317002843779230122253 95368876066417211295845)
                  ·
                    rfl

theorem cell21_417893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_417893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417893 prefixEnd_417893 := by exact prefixLift 417893
  have htrace : WordTrace (prefixWord ++ tailWord_417893) baseStart_417893 baseEnd_417893 := by
    simpa [prefixWord, tailWord_417893, baseEnd_417893] using wordTrace_append hprefix tailTrace_417893
  have hstable : (prefixWord ++ tailWord_417893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417893).length < 2 ^ (prefixWord ++ tailWord_417893).sum := by decide
  have hdescent : baseEnd_417893 < baseStart_417893 := by decide
  rcases family_descends (prefixWord ++ tailWord_417893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417904 : List Nat := [2, 1, 1, 1, 5, 2, 3, 6]
def baseStart_417904 : Nat := 118140960795 + 417904 * 2 ^ 59
def prefixEnd_417904 : Nat := 4983230072969 + 3 ^ 40 * 417904 * 2
def baseEnd_417904 : Nat := 31790462138761212204163

theorem tailTrace_417904 : CollatzResearch.WordTrace tailWord_417904 prefixEnd_417904 31790462138761212204163 := by
  unfold tailWord_417904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621105539006327583034383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10161474052008436777379177 7621105539006327583034383)
  ·
    refine ⟨11431658308509491374551575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7621105539006327583034383 11431658308509491374551575)
    ·
      refine ⟨17147487462764237061827363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11431658308509491374551575 17147487462764237061827363)
      ·
        refine ⟨25721231194146355592741045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17147487462764237061827363 25721231194146355592741045)
        ·
          refine ⟨2411365424451220836819473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25721231194146355592741045 2411365424451220836819473)
          ·
            refine ⟨1808524068338415627614605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411365424451220836819473 1808524068338415627614605)
            ·
              refine ⟨678196525626905860355477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1808524068338415627614605 678196525626905860355477)
              ·
                refine ⟨31790462138761212204163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 678196525626905860355477 31790462138761212204163)
                ·
                  rfl

theorem cell21_417904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_417904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417904 prefixEnd_417904 := by exact prefixLift 417904
  have htrace : WordTrace (prefixWord ++ tailWord_417904) baseStart_417904 baseEnd_417904 := by
    simpa [prefixWord, tailWord_417904, baseEnd_417904] using wordTrace_append hprefix tailTrace_417904
  have hstable : (prefixWord ++ tailWord_417904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417904).length < 2 ^ (prefixWord ++ tailWord_417904).sum := by decide
  have hdescent : baseEnd_417904 < baseStart_417904 := by decide
  rcases family_descends (prefixWord ++ tailWord_417904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417952 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_417952 : Nat := 118140960795 + 417952 * 2 ^ 59
def prefixEnd_417952 : Nat := 4983230072969 + 3 ^ 40 * 417952 * 2
def baseEnd_417952 : Nat := 95382340670246219812391

theorem tailTrace_417952 : CollatzResearch.WordTrace tailWord_417952 prefixEnd_417952 95382340670246219812391 := by
  unfold tailWord_417952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621980890919379681908055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10162641187892506242544073 7621980890919379681908055)
  ·
    refine ⟨11432971336379069522862083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7621980890919379681908055 11432971336379069522862083)
    ·
      refine ⟨17149457004568604284293125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11432971336379069522862083 17149457004568604284293125)
      ·
        refine ⟨3215523188356613303304961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17149457004568604284293125 3215523188356613303304961)
        ·
          refine ⟨2411642391267459977478721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3215523188356613303304961 2411642391267459977478721)
          ·
            refine ⟨1808731793450594983109041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411642391267459977478721 1808731793450594983109041)
            ·
              refine ⟨1356548845087946237331781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808731793450594983109041 1356548845087946237331781)
              ·
                refine ⟨254352908453989919499709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1356548845087946237331781 254352908453989919499709)
                ·
                  refine ⟨95382340670246219812391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254352908453989919499709 95382340670246219812391)
                  ·
                    rfl

theorem cell21_417952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_417952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_417952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_417952 prefixEnd_417952 := by exact prefixLift 417952
  have htrace : WordTrace (prefixWord ++ tailWord_417952) baseStart_417952 baseEnd_417952 := by
    simpa [prefixWord, tailWord_417952, baseEnd_417952] using wordTrace_append hprefix tailTrace_417952
  have hstable : (prefixWord ++ tailWord_417952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417952).length < 2 ^ (prefixWord ++ tailWord_417952).sum := by decide
  have hdescent : baseEnd_417952 < baseStart_417952 := by decide
  rcases family_descends (prefixWord ++ tailWord_417952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418025 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 4]
def baseStart_418025 : Nat := 118140960795 + 418025 * 2 ^ 59
def prefixEnd_418025 : Nat := 4983230072969 + 3 ^ 40 * 418025 * 2
def baseEnd_418025 : Nat := 95399000264814315095575

theorem tailTrace_418025 : CollatzResearch.WordTrace tailWord_418025 prefixEnd_418025 95399000264814315095575 := by
  unfold tailWord_418025
  simp only [CollatzResearch.WordTrace]
  refine ⟨15246624310574292831223529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10164416207049528554149019 15246624310574292831223529)
  ·
    refine ⟨11434968232930719623417647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15246624310574292831223529 11434968232930719623417647)
    ·
      refine ⟨17152452349396079435126471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11434968232930719623417647 17152452349396079435126471)
      ·
        refine ⟨25728678524094119152689707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17152452349396079435126471 25728678524094119152689707)
        ·
          refine ⟨38593017786141178729034561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25728678524094119152689707 38593017786141178729034561)
          ·
            refine ⟨28944763339605884046775921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38593017786141178729034561 28944763339605884046775921)
            ·
              refine ⟨21708572504704413035081941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28944763339605884046775921 21708572504704413035081941)
              ·
                refine ⟨508794668079009680509733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21708572504704413035081941 508794668079009680509733)
                ·
                  refine ⟨95399000264814315095575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508794668079009680509733 95399000264814315095575)
                  ·
                    rfl

theorem cell21_418025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_418025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418025 prefixEnd_418025 := by exact prefixLift 418025
  have htrace : WordTrace (prefixWord ++ tailWord_418025) baseStart_418025 baseEnd_418025 := by
    simpa [prefixWord, tailWord_418025, baseEnd_418025] using wordTrace_append hprefix tailTrace_418025
  have hstable : (prefixWord ++ tailWord_418025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418025).length < 2 ^ (prefixWord ++ tailWord_418025).sum := by decide
  have hdescent : baseEnd_418025 < baseStart_418025 := by decide
  rcases family_descends (prefixWord ++ tailWord_418025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418090 : List Nat := [3, 1, 4, 2, 2, 1, 3, 5]
def baseStart_418090 : Nat := 118140960795 + 418090 * 2 ^ 59
def prefixEnd_418090 : Nat := 4983230072969 + 3 ^ 40 * 418090 * 2
def baseEnd_418090 : Nat := 31804611383462882170703

theorem tailTrace_418090 : CollatzResearch.WordTrace tailWord_418090 prefixEnd_418090 31804611383462882170703 := by
  unfold tailWord_418090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812248763834702233084931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10165996703559205954893149 3812248763834702233084931)
  ·
    refine ⟨5718373145752053349627397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3812248763834702233084931 5718373145752053349627397)
    ·
      refine ⟨1072194964828510003055137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5718373145752053349627397 1072194964828510003055137)
      ·
        refine ⟨804146223621382502291353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072194964828510003055137 804146223621382502291353)
        ·
          refine ⟨603109667716036876718515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804146223621382502291353 603109667716036876718515)
          ·
            refine ⟨904664501574055315077773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603109667716036876718515 904664501574055315077773)
            ·
              refine ⟨339249188090270743154165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 904664501574055315077773 339249188090270743154165)
              ·
                refine ⟨31804611383462882170703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339249188090270743154165 31804611383462882170703)
                ·
                  rfl

theorem cell21_418090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_418090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418090 prefixEnd_418090 := by exact prefixLift 418090
  have htrace : WordTrace (prefixWord ++ tailWord_418090) baseStart_418090 baseEnd_418090 := by
    simpa [prefixWord, tailWord_418090, baseEnd_418090] using wordTrace_append hprefix tailTrace_418090
  have hstable : (prefixWord ++ tailWord_418090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418090).length < 2 ^ (prefixWord ++ tailWord_418090).sum := by decide
  have hdescent : baseEnd_418090 < baseStart_418090 := by decide
  rcases family_descends (prefixWord ++ tailWord_418090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418101 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_418101 : Nat := 118140960795 + 418101 * 2 ^ 59
def prefixEnd_418101 : Nat := 4983230072969 + 3 ^ 40 * 418101 * 2
def baseEnd_418101 : Nat := 95416344500255071828753

theorem tailTrace_418101 : CollatzResearch.WordTrace tailWord_418101 prefixEnd_418101 95416344500255071828753 := by
  unfold tailWord_418101
  simp only [CollatzResearch.WordTrace]
  refine ⟨15249396258298957810990157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10166264172199305207326771 15249396258298957810990157)
  ·
    refine ⟨5718523596862109179121309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15249396258298957810990157 5718523596862109179121309)
    ·
      refine ⟨2144446348823290942170491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5718523596862109179121309 2144446348823290942170491)
      ·
        refine ⟨3216669523234936413255737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144446348823290942170491 3216669523234936413255737)
        ·
          refine ⟨2412502142426202309941803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3216669523234936413255737 2412502142426202309941803)
          ·
            refine ⟨3618753213639303464912705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412502142426202309941803 3618753213639303464912705)
            ·
              refine ⟨2714064910229477598684529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618753213639303464912705 2714064910229477598684529)
              ·
                refine ⟨2035548682672108199013397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714064910229477598684529 2035548682672108199013397)
                ·
                  refine ⟨95416344500255071828753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2035548682672108199013397 95416344500255071828753)
                  ·
                    rfl

theorem cell21_418101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_418101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418101 prefixEnd_418101 := by exact prefixLift 418101
  have htrace : WordTrace (prefixWord ++ tailWord_418101) baseStart_418101 baseEnd_418101 := by
    simpa [prefixWord, tailWord_418101, baseEnd_418101] using wordTrace_append hprefix tailTrace_418101
  have hstable : (prefixWord ++ tailWord_418101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418101).length < 2 ^ (prefixWord ++ tailWord_418101).sum := by decide
  have hdescent : baseEnd_418101 < baseStart_418101 := by decide
  rcases family_descends (prefixWord ++ tailWord_418101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418149 : List Nat := [1, 3, 1, 3, 1, 5, 2, 5]
def baseStart_418149 : Nat := 118140960795 + 418149 * 2 ^ 59
def prefixEnd_418149 : Nat := 4983230072969 + 3 ^ 40 * 418149 * 2
def baseEnd_418149 : Nat := 31809099584739218342885

theorem tailTrace_418149 : CollatzResearch.WordTrace tailWord_418149 prefixEnd_418149 31809099584739218342885 := by
  unfold tailWord_418149
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251146962125062008737501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10167431308083374672491667 15251146962125062008737501)
  ·
    refine ⟨5719180110796898253276563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15251146962125062008737501 5719180110796898253276563)
    ·
      refine ⟨8578770166195347379914845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719180110796898253276563 8578770166195347379914845)
      ·
        refine ⟨3217038812323255267468067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8578770166195347379914845 3217038812323255267468067)
        ·
          refine ⟨4825558218484882901202101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217038812323255267468067 4825558218484882901202101)
          ·
            refine ⟨452396082982957771987697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4825558218484882901202101 452396082982957771987697)
            ·
              refine ⟨339297062237218328990773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452396082982957771987697 339297062237218328990773)
              ·
                refine ⟨31809099584739218342885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339297062237218328990773 31809099584739218342885)
                ·
                  rfl

theorem cell21_418149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 5].length) (baseStart_418149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418149 prefixEnd_418149 := by exact prefixLift 418149
  have htrace : WordTrace (prefixWord ++ tailWord_418149) baseStart_418149 baseEnd_418149 := by
    simpa [prefixWord, tailWord_418149, baseEnd_418149] using wordTrace_append hprefix tailTrace_418149
  have hstable : (prefixWord ++ tailWord_418149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418149).length < 2 ^ (prefixWord ++ tailWord_418149).sum := by decide
  have hdescent : baseEnd_418149 < baseStart_418149 := by decide
  rcases family_descends (prefixWord ++ tailWord_418149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418166 : List Nat := [5, 1, 1, 4, 1, 2, 7]
def baseStart_418166 : Nat := 118140960795 + 418166 * 2 ^ 59
def prefixEnd_418166 : Nat := 4983230072969 + 3 ^ 40 * 418166 * 2
def baseEnd_418166 : Nat := 10603464265092155916143

theorem tailTrace_418166 : CollatzResearch.WordTrace tailWord_418166 prefixEnd_418166 10603464265092155916143 := by
  unfold tailWord_418166
  simp only [CollatzResearch.WordTrace]
  refine ⟨953235437691467119506647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10167844668708982608070901 953235437691467119506647)
  ·
    refine ⟨1429853156537200679259971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 953235437691467119506647 1429853156537200679259971)
    ·
      refine ⟨2144779734805801018889957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429853156537200679259971 2144779734805801018889957)
      ·
        refine ⟨402146200276087691041867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2144779734805801018889957 402146200276087691041867)
        ·
          refine ⟨603219300414131536562801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402146200276087691041867 603219300414131536562801)
          ·
            refine ⟨452414475310598652422101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603219300414131536562801 452414475310598652422101)
            ·
              refine ⟨10603464265092155916143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 452414475310598652422101 10603464265092155916143)
              ·
                rfl

theorem cell21_418166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 7].length) (baseStart_418166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418166 prefixEnd_418166 := by exact prefixLift 418166
  have htrace : WordTrace (prefixWord ++ tailWord_418166) baseStart_418166 baseEnd_418166 := by
    simpa [prefixWord, tailWord_418166, baseEnd_418166] using wordTrace_append hprefix tailTrace_418166
  have hstable : (prefixWord ++ tailWord_418166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418166).length < 2 ^ (prefixWord ++ tailWord_418166).sum := by decide
  have hdescent : baseEnd_418166 < baseStart_418166 := by decide
  rcases family_descends (prefixWord ++ tailWord_418166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418332 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_418332 : Nat := 118140960795 + 418332 * 2 ^ 59
def prefixEnd_418332 : Nat := 4983230072969 + 3 ^ 40 * 418332 * 2
def baseEnd_418332 : Nat := 95469061847450003478281

theorem tailTrace_418332 : CollatzResearch.WordTrace tailWord_418332 prefixEnd_418332 95469061847450003478281 := by
  unfold tailWord_418332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628910760231042131324625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10171881013641389508432833 7628910760231042131324625)
  ·
    refine ⟨5721683070173281598493469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7628910760231042131324625 5721683070173281598493469)
    ·
      refine ⟨2145631151314980599435051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5721683070173281598493469 2145631151314980599435051)
      ·
        refine ⟨3218446726972470899152577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145631151314980599435051 3218446726972470899152577)
        ·
          refine ⟨2413835045229353174364433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3218446726972470899152577 2413835045229353174364433)
          ·
            refine ⟨1810376283922014880773325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413835045229353174364433 1810376283922014880773325)
            ·
              refine ⟨678891106470755580289997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1810376283922014880773325 678891106470755580289997)
              ·
                refine ⟨254584164926533342608749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678891106470755580289997 254584164926533342608749)
                ·
                  refine ⟨95469061847450003478281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254584164926533342608749 95469061847450003478281)
                  ·
                    rfl

theorem cell21_418332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_418332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418332 prefixEnd_418332 := by exact prefixLift 418332
  have htrace : WordTrace (prefixWord ++ tailWord_418332) baseStart_418332 baseEnd_418332 := by
    simpa [prefixWord, tailWord_418332, baseEnd_418332] using wordTrace_append hprefix tailTrace_418332
  have hstable : (prefixWord ++ tailWord_418332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418332).length < 2 ^ (prefixWord ++ tailWord_418332).sum := by decide
  have hdescent : baseEnd_418332 < baseStart_418332 := by decide
  rcases family_descends (prefixWord ++ tailWord_418332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418391 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 3]
def baseStart_418391 : Nat := 118140960795 + 418391 * 2 ^ 59
def prefixEnd_418391 : Nat := 4983230072969 + 3 ^ 40 * 418391 * 2
def baseEnd_418391 : Nat := 95482526451279011994827

theorem tailTrace_418391 : CollatzResearch.WordTrace tailWord_418391 prefixEnd_418391 95482526451279011994827 := by
  unfold tailWord_418391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259973427248337339047027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10173315618165558226031351 15259973427248337339047027)
  ·
    refine ⟨22889960140872506008570541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15259973427248337339047027 22889960140872506008570541)
    ·
      refine ⟨8583735052827189753213953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22889960140872506008570541 8583735052827189753213953)
      ·
        refine ⟨6437801289620392314910465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8583735052827189753213953 6437801289620392314910465)
        ·
          refine ⟨4828350967215294236182849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6437801289620392314910465 4828350967215294236182849)
          ·
            refine ⟨3621263225411470677137137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4828350967215294236182849 3621263225411470677137137)
            ·
              refine ⟨2715947419058603007852853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621263225411470677137137 2715947419058603007852853)
              ·
                refine ⟨254620070536744031986205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2715947419058603007852853 254620070536744031986205)
                ·
                  refine ⟨95482526451279011994827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254620070536744031986205 95482526451279011994827)
                  ·
                    rfl

theorem cell21_418391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 3].length) (baseStart_418391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418391 prefixEnd_418391 := by exact prefixLift 418391
  have htrace : WordTrace (prefixWord ++ tailWord_418391) baseStart_418391 baseEnd_418391 := by
    simpa [prefixWord, tailWord_418391, baseEnd_418391] using wordTrace_append hprefix tailTrace_418391
  have hstable : (prefixWord ++ tailWord_418391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418391).length < 2 ^ (prefixWord ++ tailWord_418391).sum := by decide
  have hdescent : baseEnd_418391 < baseStart_418391 := by decide
  rcases family_descends (prefixWord ++ tailWord_418391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418495 : List Nat := [1, 1, 2, 2, 2, 5, 1, 7]
def baseStart_418495 : Nat := 118140960795 + 418495 * 2 ^ 59
def prefixEnd_418495 : Nat := 4983230072969 + 3 ^ 40 * 418495 * 2
def baseEnd_418495 : Nat := 31835420222732647420427

theorem tailTrace_418495 : CollatzResearch.WordTrace tailWord_418495 prefixEnd_418495 31835420222732647420427 := by
  unfold tailWord_418495
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263766618871563100832939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10175844412581042067221959 15263766618871563100832939)
  ·
    refine ⟨22895649928307344651249409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15263766618871563100832939 22895649928307344651249409)
    ·
      refine ⟨17171737446230508488437057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22895649928307344651249409 17171737446230508488437057)
      ·
        refine ⟨12878803084672881366327793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17171737446230508488437057 12878803084672881366327793)
        ·
          refine ⟨9659102313504661024745845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12878803084672881366327793 9659102313504661024745845)
          ·
            refine ⟨905540841891061971069923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9659102313504661024745845 905540841891061971069923)
            ·
              refine ⟨1358311262836592956604885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905540841891061971069923 1358311262836592956604885)
              ·
                refine ⟨31835420222732647420427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1358311262836592956604885 31835420222732647420427)
                ·
                  rfl

theorem cell21_418495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_418495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418495 prefixEnd_418495 := by exact prefixLift 418495
  have htrace : WordTrace (prefixWord ++ tailWord_418495) baseStart_418495 baseEnd_418495 := by
    simpa [prefixWord, tailWord_418495, baseEnd_418495] using wordTrace_append hprefix tailTrace_418495
  have hstable : (prefixWord ++ tailWord_418495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418495).length < 2 ^ (prefixWord ++ tailWord_418495).sum := by decide
  have hdescent : baseEnd_418495 < baseStart_418495 := by decide
  rcases family_descends (prefixWord ++ tailWord_418495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418588 : List Nat := [2, 2, 3, 1, 1, 5, 1, 6]
def baseStart_418588 : Nat := 118140960795 + 418588 * 2 ^ 59
def prefixEnd_418588 : Nat := 4983230072969 + 3 ^ 40 * 418588 * 2
def baseEnd_418588 : Nat := 31842494845083482403697

theorem tailTrace_418588 : CollatzResearch.WordTrace tailWord_418588 prefixEnd_418588 31842494845083482403697 := by
  unfold tailWord_418588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633579303767319991984209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10178105738356426655978945 7633579303767319991984209)
  ·
    refine ⟨5725184477825489993988157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7633579303767319991984209 5725184477825489993988157)
    ·
      refine ⟨2146944179184558747745559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5725184477825489993988157 2146944179184558747745559)
      ·
        refine ⟨3220416268776838121618339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146944179184558747745559 3220416268776838121618339)
        ·
          refine ⟨4830624403165257182427509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220416268776838121618339 4830624403165257182427509)
          ·
            refine ⟨452871037796742860852579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4830624403165257182427509 452871037796742860852579)
            ·
              refine ⟨679306556695114291278869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452871037796742860852579 679306556695114291278869)
              ·
                refine ⟨31842494845083482403697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 679306556695114291278869 31842494845083482403697)
                ·
                  rfl

theorem cell21_418588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_418588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418588 prefixEnd_418588 := by exact prefixLift 418588
  have htrace : WordTrace (prefixWord ++ tailWord_418588) baseStart_418588 baseEnd_418588 := by
    simpa [prefixWord, tailWord_418588, baseEnd_418588] using wordTrace_append hprefix tailTrace_418588
  have hstable : (prefixWord ++ tailWord_418588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418588).length < 2 ^ (prefixWord ++ tailWord_418588).sum := by decide
  have hdescent : baseEnd_418588 < baseStart_418588 := by decide
  rcases family_descends (prefixWord ++ tailWord_418588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418616 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_418616 : Nat := 118140960795 + 418616 * 2 ^ 59
def prefixEnd_418616 : Nat := 4983230072969 + 3 ^ 40 * 418616 * 2
def baseEnd_418616 : Nat := 95533874516728620744367

theorem tailTrace_418616 : CollatzResearch.WordTrace tailWord_418616 prefixEnd_418616 95533874516728620744367 := by
  unfold tailWord_418616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7634089925716600382993851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10178786567622133843991801 7634089925716600382993851)
  ·
    refine ⟨11451134888574900574490777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7634089925716600382993851 11451134888574900574490777)
    ·
      refine ⟨8588351166431175430868083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11451134888574900574490777 8588351166431175430868083)
      ·
        refine ⟨12882526749646763146302125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588351166431175430868083 12882526749646763146302125)
        ·
          refine ⟨4830947531117536179863297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12882526749646763146302125 4830947531117536179863297)
          ·
            refine ⟨3623210648338152134897473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830947531117536179863297 3623210648338152134897473)
            ·
              refine ⟨2717407986253614101173105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623210648338152134897473 2717407986253614101173105)
              ·
                refine ⟨2038055989690210575879829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717407986253614101173105 2038055989690210575879829)
                ·
                  refine ⟨95533874516728620744367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2038055989690210575879829 95533874516728620744367)
                  ·
                    rfl

theorem cell21_418616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_418616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418616 prefixEnd_418616 := by exact prefixLift 418616
  have htrace : WordTrace (prefixWord ++ tailWord_418616) baseStart_418616 baseEnd_418616 := by
    simpa [prefixWord, tailWord_418616, baseEnd_418616] using wordTrace_append hprefix tailTrace_418616
  have hstable : (prefixWord ++ tailWord_418616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418616).length < 2 ^ (prefixWord ++ tailWord_418616).sum := by decide
  have hdescent : baseEnd_418616 < baseStart_418616 := by decide
  rcases family_descends (prefixWord ++ tailWord_418616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418633 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 4]
def baseStart_418633 : Nat := 118140960795 + 418633 * 2 ^ 59
def prefixEnd_418633 : Nat := 4983230072969 + 3 ^ 40 * 418633 * 2
def baseEnd_418633 : Nat := 95537754148340368960999

theorem tailTrace_418633 : CollatzResearch.WordTrace tailWord_418633 prefixEnd_418633 95537754148340368960999 := by
  unfold tailWord_418633
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268799892371612669356553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10179199928247741779571035 15268799892371612669356553)
  ·
    refine ⟨11451599919278709502017415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15268799892371612669356553 11451599919278709502017415)
    ·
      refine ⟨17177399878918064253026123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11451599919278709502017415 17177399878918064253026123)
      ·
        refine ⟨25766099818377096379539185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17177399878918064253026123 25766099818377096379539185)
        ·
          refine ⟨19324574863782822284654389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25766099818377096379539185 19324574863782822284654389)
          ·
            refine ⟨1811678893479639589186349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19324574863782822284654389 1811678893479639589186349)
            ·
              refine ⟨679379585054864845944881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811678893479639589186349 679379585054864845944881)
              ·
                refine ⟨509534688791148634458661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679379585054864845944881 509534688791148634458661)
                ·
                  refine ⟨95537754148340368960999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509534688791148634458661 95537754148340368960999)
                  ·
                    rfl

theorem cell21_418633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_418633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418633 prefixEnd_418633 := by exact prefixLift 418633
  have htrace : WordTrace (prefixWord ++ tailWord_418633) baseStart_418633 baseEnd_418633 := by
    simpa [prefixWord, tailWord_418633, baseEnd_418633] using wordTrace_append hprefix tailTrace_418633
  have hstable : (prefixWord ++ tailWord_418633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418633).length < 2 ^ (prefixWord ++ tailWord_418633).sum := by decide
  have hdescent : baseEnd_418633 < baseStart_418633 := by decide
  rcases family_descends (prefixWord ++ tailWord_418633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418650 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_418650 : Nat := 118140960795 + 418650 * 2 ^ 59
def prefixEnd_418650 : Nat := 4983230072969 + 3 ^ 40 * 418650 * 2
def baseEnd_418650 : Nat := 95541633779952117177631

theorem tailTrace_418650 : CollatzResearch.WordTrace tailWord_418650 prefixEnd_418650 95541633779952117177631 := by
  unfold tailWord_418650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817354983327506143181351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10179613288873349715150269 3817354983327506143181351)
  ·
    refine ⟨5726032474991259214772027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817354983327506143181351 5726032474991259214772027)
    ·
      refine ⟨8589048712486888822158041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726032474991259214772027 8589048712486888822158041)
      ·
        refine ⟨6441786534365166616618531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8589048712486888822158041 6441786534365166616618531)
        ·
          refine ⟨9662679801547749924927797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441786534365166616618531 9662679801547749924927797)
          ·
            refine ⟨905876231395101555461981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9662679801547749924927797 905876231395101555461981)
            ·
              refine ⟨339703586773163083298243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905876231395101555461981 339703586773163083298243)
              ·
                refine ⟨509555380159744624947365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339703586773163083298243 509555380159744624947365)
                ·
                  refine ⟨95541633779952117177631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509555380159744624947365 95541633779952117177631)
                  ·
                    rfl

theorem cell21_418650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_418650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418650 prefixEnd_418650 := by exact prefixLift 418650
  have htrace : WordTrace (prefixWord ++ tailWord_418650) baseStart_418650 baseEnd_418650 := by
    simpa [prefixWord, tailWord_418650, baseEnd_418650] using wordTrace_append hprefix tailTrace_418650
  have hstable : (prefixWord ++ tailWord_418650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418650).length < 2 ^ (prefixWord ++ tailWord_418650).sum := by decide
  have hdescent : baseEnd_418650 < baseStart_418650 := by decide
  rcases family_descends (prefixWord ++ tailWord_418650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418664 : List Nat := [2, 1, 4, 2, 1, 2, 4, 5]
def baseStart_418664 : Nat := 118140960795 + 418664 * 2 ^ 59
def prefixEnd_418664 : Nat := 4983230072969 + 3 ^ 40 * 418664 * 2
def baseEnd_418664 : Nat := 31848276256897067981423

theorem tailTrace_418664 : CollatzResearch.WordTrace tailWord_418664 prefixEnd_418664 31848276256897067981423 := by
  unfold tailWord_418664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7634965277629652481867523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10179953703506203309156697 7634965277629652481867523)
  ·
    refine ⟨11452447916444478722801285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7634965277629652481867523 11452447916444478722801285)
    ·
      refine ⟨2147333984333339760525241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11452447916444478722801285 2147333984333339760525241)
      ·
        refine ⟨1610500488250004820393931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147333984333339760525241 1610500488250004820393931)
        ·
          refine ⟨2415750732375007230590897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610500488250004820393931 2415750732375007230590897)
          ·
            refine ⟨1811813049281255422943173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415750732375007230590897 1811813049281255422943173)
            ·
              refine ⟨339714946740235391801845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1811813049281255422943173 339714946740235391801845)
              ·
                refine ⟨31848276256897067981423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339714946740235391801845 31848276256897067981423)
                ·
                  rfl

theorem cell21_418664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_418664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418664 prefixEnd_418664 := by exact prefixLift 418664
  have htrace : WordTrace (prefixWord ++ tailWord_418664) baseStart_418664 baseEnd_418664 := by
    simpa [prefixWord, tailWord_418664, baseEnd_418664] using wordTrace_append hprefix tailTrace_418664
  have hstable : (prefixWord ++ tailWord_418664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418664).length < 2 ^ (prefixWord ++ tailWord_418664).sum := by decide
  have hdescent : baseEnd_418664 < baseStart_418664 := by decide
  rcases family_descends (prefixWord ++ tailWord_418664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418670 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_418670 : Nat := 118140960795 + 418670 * 2 ^ 59
def prefixEnd_418670 : Nat := 4983230072969 + 3 ^ 40 * 418670 * 2
def baseEnd_418670 : Nat := 95546198052436526844257

theorem tailTrace_418670 : CollatzResearch.WordTrace tailWord_418670 prefixEnd_418670 95546198052436526844257 := by
  unfold tailWord_418670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908768674154695998556683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10180099595491711992302309 1908768674154695998556683)
  ·
    refine ⟨2863153011232043997835025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908768674154695998556683 2863153011232043997835025)
    ·
      refine ⟨2147364758424032998376269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2863153011232043997835025 2147364758424032998376269)
      ·
        refine ⟨805261784409012374391101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2147364758424032998376269 805261784409012374391101)
        ·
          refine ⟨301973169153379640396663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805261784409012374391101 301973169153379640396663)
          ·
            refine ⟨452959753730069460594995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301973169153379640396663 452959753730069460594995)
            ·
              refine ⟨679439630595104190892493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452959753730069460594995 679439630595104190892493)
              ·
                refine ⟨254789861473164071584685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679439630595104190892493 254789861473164071584685)
                ·
                  refine ⟨95546198052436526844257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254789861473164071584685 95546198052436526844257)
                  ·
                    rfl

theorem cell21_418670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_418670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418670 prefixEnd_418670 := by exact prefixLift 418670
  have htrace : WordTrace (prefixWord ++ tailWord_418670) baseStart_418670 baseEnd_418670 := by
    simpa [prefixWord, tailWord_418670, baseEnd_418670] using wordTrace_append hprefix tailTrace_418670
  have hstable : (prefixWord ++ tailWord_418670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418670).length < 2 ^ (prefixWord ++ tailWord_418670).sum := by decide
  have hdescent : baseEnd_418670 < baseStart_418670 := by decide
  rcases family_descends (prefixWord ++ tailWord_418670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418695 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 5]
def baseStart_418695 : Nat := 118140960795 + 418695 * 2 ^ 59
def prefixEnd_418695 : Nat := 4983230072969 + 3 ^ 40 * 418695 * 2
def baseEnd_418695 : Nat := 95551903393042038927539

theorem tailTrace_418695 : CollatzResearch.WordTrace tailWord_418695 prefixEnd_418695 95551903393042038927539 := by
  unfold tailWord_418695
  simp only [CollatzResearch.WordTrace]
  refine ⟨15271061218146997258113539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10180707478764664838742359 15271061218146997258113539)
  ·
    refine ⟨22906591827220495887170309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15271061218146997258113539 22906591827220495887170309)
    ·
      refine ⟨4294985967603842978844433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22906591827220495887170309 4294985967603842978844433)
      ·
        refine ⟨3221239475702882234133325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4294985967603842978844433 3221239475702882234133325)
        ·
          refine ⟨1207964803388580837799997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3221239475702882234133325 1207964803388580837799997)
          ·
            refine ⟨452986801270717814174999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1207964803388580837799997 452986801270717814174999)
            ·
              refine ⟨679480201906076721262499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452986801270717814174999 679480201906076721262499)
              ·
                refine ⟨1019220302859115081893749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679480201906076721262499 1019220302859115081893749)
                ·
                  refine ⟨95551903393042038927539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019220302859115081893749 95551903393042038927539)
                  ·
                    rfl

theorem cell21_418695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].length) (baseStart_418695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418695 prefixEnd_418695 := by exact prefixLift 418695
  have htrace : WordTrace (prefixWord ++ tailWord_418695) baseStart_418695 baseEnd_418695 := by
    simpa [prefixWord, tailWord_418695, baseEnd_418695] using wordTrace_append hprefix tailTrace_418695
  have hstable : (prefixWord ++ tailWord_418695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418695).length < 2 ^ (prefixWord ++ tailWord_418695).sum := by decide
  have hdescent : baseEnd_418695 < baseStart_418695 := by decide
  rcases family_descends (prefixWord ++ tailWord_418695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418709 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 4]
def baseStart_418709 : Nat := 118140960795 + 418709 * 2 ^ 59
def prefixEnd_418709 : Nat := 4983230072969 + 3 ^ 40 * 418709 * 2
def baseEnd_418709 : Nat := 95555098383781125694177

theorem tailTrace_418709 : CollatzResearch.WordTrace tailWord_418709 prefixEnd_418709 95555098383781125694177 := by
  unfold tailWord_418709
  simp only [CollatzResearch.WordTrace]
  refine ⟨15271571840096277649123181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10181047893397518432748787 15271571840096277649123181)
  ·
    refine ⟨5726839440036104118421193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15271571840096277649123181 5726839440036104118421193)
    ·
      refine ⟨4295129580027078088815895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5726839440036104118421193 4295129580027078088815895)
      ·
        refine ⟨6442694370040617133223843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295129580027078088815895 6442694370040617133223843)
        ·
          refine ⟨9664041555060925699835765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442694370040617133223843 9664041555060925699835765)
          ·
            refine ⟨906003895786961784359603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9664041555060925699835765 906003895786961784359603)
            ·
              refine ⟨1359005843680442676539405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906003895786961784359603 1359005843680442676539405)
              ·
                refine ⟨509627191380166003702277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359005843680442676539405 509627191380166003702277)
                ·
                  refine ⟨95555098383781125694177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509627191380166003702277 95555098383781125694177)
                  ·
                    rfl

theorem cell21_418709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_418709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418709 prefixEnd_418709 := by exact prefixLift 418709
  have htrace : WordTrace (prefixWord ++ tailWord_418709) baseStart_418709 baseEnd_418709 := by
    simpa [prefixWord, tailWord_418709, baseEnd_418709] using wordTrace_append hprefix tailTrace_418709
  have hstable : (prefixWord ++ tailWord_418709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418709).length < 2 ^ (prefixWord ++ tailWord_418709).sum := by decide
  have hdescent : baseEnd_418709 < baseStart_418709 := by decide
  rcases family_descends (prefixWord ++ tailWord_418709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418740 : List Nat := [2, 5, 2, 1, 1, 10]
def baseStart_418740 : Nat := 118140960795 + 418740 * 2 ^ 59
def prefixEnd_418740 : Nat := 4983230072969 + 3 ^ 40 * 418740 * 2
def baseEnd_418740 : Nat := 3539339740967850395461

theorem tailTrace_418740 : CollatzResearch.WordTrace tailWord_418740 prefixEnd_418740 3539339740967850395461 := by
  unfold tailWord_418740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636351251491984971750837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10181801668655979962334449 7636351251491984971750837)
  ·
    refine ⟨715907929827373591101641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7636351251491984971750837 715907929827373591101641)
    ·
      refine ⟨536930947370530193326231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 715907929827373591101641 536930947370530193326231)
      ·
        refine ⟨805396421055795289989347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536930947370530193326231 805396421055795289989347)
        ·
          refine ⟨1208094631583692934984021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805396421055795289989347 1208094631583692934984021)
          ·
            refine ⟨3539339740967850395461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1208094631583692934984021 3539339740967850395461)
            ·
              rfl

theorem cell21_418740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 10].length) (baseStart_418740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418740 prefixEnd_418740 := by exact prefixLift 418740
  have htrace : WordTrace (prefixWord ++ tailWord_418740) baseStart_418740 baseEnd_418740 := by
    simpa [prefixWord, tailWord_418740, baseEnd_418740] using wordTrace_append hprefix tailTrace_418740
  have hstable : (prefixWord ++ tailWord_418740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418740).length < 2 ^ (prefixWord ++ tailWord_418740).sum := by decide
  have hdescent : baseEnd_418740 < baseStart_418740 := by decide
  rcases family_descends (prefixWord ++ tailWord_418740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418802 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_418802 : Nat := 118140960795 + 418802 * 2 ^ 59
def prefixEnd_418802 : Nat := 4983230072969 + 3 ^ 40 * 418802 * 2
def baseEnd_418802 : Nat := 95576322250833630643987

theorem tailTrace_418802 : CollatzResearch.WordTrace tailWord_418802 prefixEnd_418802 95576322250833630643987 := by
  unfold tailWord_418802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818740957189838633064665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10183309219172903021505773 3818740957189838633064665)
  ·
    refine ⟨2864055717892378974798499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3818740957189838633064665 2864055717892378974798499)
    ·
      refine ⟨4296083576838568462197749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2864055717892378974798499 4296083576838568462197749)
      ·
        refine ⟨402757835328615793331039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4296083576838568462197749 402757835328615793331039)
        ·
          refine ⟨604136752992923689996559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402757835328615793331039 604136752992923689996559)
          ·
            refine ⟨906205129489385534994839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604136752992923689996559 906205129489385534994839)
            ·
              refine ⟨1359307694234078302492259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906205129489385534994839 1359307694234078302492259)
              ·
                refine ⟨2038961541351117453738389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359307694234078302492259 2038961541351117453738389)
                ·
                  refine ⟨95576322250833630643987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2038961541351117453738389 95576322250833630643987)
                  ·
                    rfl

theorem cell21_418802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_418802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418802 prefixEnd_418802 := by exact prefixLift 418802
  have htrace : WordTrace (prefixWord ++ tailWord_418802) baseStart_418802 baseEnd_418802 := by
    simpa [prefixWord, tailWord_418802, baseEnd_418802] using wordTrace_append hprefix tailTrace_418802
  have hstable : (prefixWord ++ tailWord_418802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418802).length < 2 ^ (prefixWord ++ tailWord_418802).sum := by decide
  have hdescent : baseEnd_418802 < baseStart_418802 := by decide
  rcases family_descends (prefixWord ++ tailWord_418802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418830 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_418830 : Nat := 118140960795 + 418830 * 2 ^ 59
def prefixEnd_418830 : Nat := 4983230072969 + 3 ^ 40 * 418830 * 2
def baseEnd_418830 : Nat := 95582712232311804177263

theorem tailTrace_418830 : CollatzResearch.WordTrace tailWord_418830 prefixEnd_418830 95582712232311804177263 := by
  unfold tailWord_418830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909498134082239414284743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10183990048438610209518629 1909498134082239414284743)
  ·
    refine ⟨2864247201123359121427115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1909498134082239414284743 2864247201123359121427115)
    ·
      refine ⟨4296370801685038682140673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2864247201123359121427115 4296370801685038682140673)
      ·
        refine ⟨3222278101263779011605505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4296370801685038682140673 3222278101263779011605505)
        ·
          refine ⟨2416708575947834258704129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222278101263779011605505 2416708575947834258704129)
          ·
            refine ⟨1812531431960875694028097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2416708575947834258704129 1812531431960875694028097)
            ·
              refine ⟨1359398573970656770521073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812531431960875694028097 1359398573970656770521073)
              ·
                refine ⟨1019548930477992577890805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359398573970656770521073 1019548930477992577890805)
                ·
                  refine ⟨95582712232311804177263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019548930477992577890805 95582712232311804177263)
                  ·
                    rfl

theorem cell21_418830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_418830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418830 prefixEnd_418830 := by exact prefixLift 418830
  have htrace : WordTrace (prefixWord ++ tailWord_418830) baseStart_418830 baseEnd_418830 := by
    simpa [prefixWord, tailWord_418830, baseEnd_418830] using wordTrace_append hprefix tailTrace_418830
  have hstable : (prefixWord ++ tailWord_418830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418830).length < 2 ^ (prefixWord ++ tailWord_418830).sum := by decide
  have hdescent : baseEnd_418830 < baseStart_418830 := by decide
  rcases family_descends (prefixWord ++ tailWord_418830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418847 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 3]
def baseStart_418847 : Nat := 118140960795 + 418847 * 2 ^ 59
def prefixEnd_418847 : Nat := 4983230072969 + 3 ^ 40 * 418847 * 2
def baseEnd_418847 : Nat := 95586591863923552393895

theorem tailTrace_418847 : CollatzResearch.WordTrace tailWord_418847 prefixEnd_418847 95586591863923552393895 := by
  unfold tailWord_418847
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276605113596327217646795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10184403409064218145097863 15276605113596327217646795)
  ·
    refine ⟨22914907670394490826470193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15276605113596327217646795 22914907670394490826470193)
    ·
      refine ⟨17186180752795868119852645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22914907670394490826470193 17186180752795868119852645)
      ·
        refine ⟨3222408891149225272472371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17186180752795868119852645 3222408891149225272472371)
        ·
          refine ⟨4833613336723837908708557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222408891149225272472371 4833613336723837908708557)
          ·
            refine ⟨1812605001271439215765709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4833613336723837908708557 1812605001271439215765709)
            ·
              refine ⟨679726875476789705912141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1812605001271439215765709 679726875476789705912141)
              ·
                refine ⟨254897578303796139717053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679726875476789705912141 254897578303796139717053)
                ·
                  refine ⟨95586591863923552393895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254897578303796139717053 95586591863923552393895)
                  ·
                    rfl

theorem cell21_418847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 3].length) (baseStart_418847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418847 prefixEnd_418847 := by exact prefixLift 418847
  have htrace : WordTrace (prefixWord ++ tailWord_418847) baseStart_418847 baseEnd_418847 := by
    simpa [prefixWord, tailWord_418847, baseEnd_418847] using wordTrace_append hprefix tailTrace_418847
  have hstable : (prefixWord ++ tailWord_418847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418847).length < 2 ^ (prefixWord ++ tailWord_418847).sum := by decide
  have hdescent : baseEnd_418847 < baseStart_418847 := by decide
  rcases family_descends (prefixWord ++ tailWord_418847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418878 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_418878 : Nat := 118140960795 + 418878 * 2 ^ 59
def prefixEnd_418878 : Nat := 4983230072969 + 3 ^ 40 * 418878 * 2
def baseEnd_418878 : Nat := 95593666486274387377165

theorem tailTrace_418878 : CollatzResearch.WordTrace tailWord_418878 prefixEnd_418878 95593666486274387377165 := by
  unfold tailWord_418878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909716972060502439003161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10185157184322679674683525 1909716972060502439003161)
  ·
    refine ⟨1432287729045376829252371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1909716972060502439003161 1432287729045376829252371)
    ·
      refine ⟨2148431593568065243878557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432287729045376829252371 2148431593568065243878557)
      ·
        refine ⟨805661847588024466454459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2148431593568065243878557 805661847588024466454459)
        ·
          refine ⟨1208492771382036699681689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805661847588024466454459 1208492771382036699681689)
          ·
            refine ⟨906369578536527524761267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208492771382036699681689 906369578536527524761267)
            ·
              refine ⟨1359554367804791287141901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906369578536527524761267 1359554367804791287141901)
              ·
                refine ⟨509832887926796732678213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359554367804791287141901 509832887926796732678213)
                ·
                  refine ⟨95593666486274387377165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509832887926796732678213 95593666486274387377165)
                  ·
                    rfl

theorem cell21_418878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_418878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418878 prefixEnd_418878 := by exact prefixLift 418878
  have htrace : WordTrace (prefixWord ++ tailWord_418878) baseStart_418878 baseEnd_418878 := by
    simpa [prefixWord, tailWord_418878, baseEnd_418878] using wordTrace_append hprefix tailTrace_418878
  have hstable : (prefixWord ++ tailWord_418878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418878).length < 2 ^ (prefixWord ++ tailWord_418878).sum := by decide
  have hdescent : baseEnd_418878 < baseStart_418878 := by decide
  rcases family_descends (prefixWord ++ tailWord_418878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419047 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 4]
def baseStart_419047 : Nat := 118140960795 + 419047 * 2 ^ 59
def prefixEnd_419047 : Nat := 4983230072969 + 3 ^ 40 * 419047 * 2
def baseEnd_419047 : Nat := 95632234588767649060153

theorem tailTrace_419047 : CollatzResearch.WordTrace tailWord_419047 prefixEnd_419047 95632234588767649060153 := by
  unfold tailWord_419047
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283899712871761374927395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10189266475247840916618263 15283899712871761374927395)
  ·
    refine ⟨22925849569307642062391093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15283899712871761374927395 22925849569307642062391093)
    ·
      refine ⟨2149298397122591443349165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22925849569307642062391093 2149298397122591443349165)
      ·
        refine ⟨805986898920971791255937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2149298397122591443349165 805986898920971791255937)
        ·
          refine ⟨604490174190728843441953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805986898920971791255937 604490174190728843441953)
          ·
            refine ⟨453367630643046632581465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604490174190728843441953 453367630643046632581465)
            ·
              refine ⟨340025722982284974436099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453367630643046632581465 340025722982284974436099)
              ·
                refine ⟨510038584473427461654149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340025722982284974436099 510038584473427461654149)
                ·
                  refine ⟨95632234588767649060153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510038584473427461654149 95632234588767649060153)
                  ·
                    rfl

theorem cell21_419047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 4].length) (baseStart_419047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419047 prefixEnd_419047 := by exact prefixLift 419047
  have htrace : WordTrace (prefixWord ++ tailWord_419047) baseStart_419047 baseEnd_419047 := by
    simpa [prefixWord, tailWord_419047, baseEnd_419047] using wordTrace_append hprefix tailTrace_419047
  have hstable : (prefixWord ++ tailWord_419047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419047).length < 2 ^ (prefixWord ++ tailWord_419047).sum := by decide
  have hdescent : baseEnd_419047 < baseStart_419047 := by decide
  rcases family_descends (prefixWord ++ tailWord_419047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419086 : List Nat := [4, 1, 1, 2, 1, 12]
def baseStart_419086 : Nat := 118140960795 + 419086 * 2 ^ 59
def prefixEnd_419086 : Nat := 4983230072969 + 3 ^ 40 * 419086 * 2
def baseEnd_419086 : Nat := 3542264256300453626299

theorem tailTrace_419086 : CollatzResearch.WordTrace tailWord_419086 prefixEnd_419086 3542264256300453626299 := by
  unfold tailWord_419086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910665269966308879449639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10190214773153647357064741 1910665269966308879449639)
  ·
    refine ⟨2865997904949463319174459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1910665269966308879449639 2865997904949463319174459)
    ·
      refine ⟨4298996857424194978761689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865997904949463319174459 4298996857424194978761689)
      ·
        refine ⟨3224247643068146234071267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4298996857424194978761689 3224247643068146234071267)
        ·
          refine ⟨4836371464602219351106901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224247643068146234071267 4836371464602219351106901)
          ·
            refine ⟨3542264256300453626299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4836371464602219351106901 3542264256300453626299)
            ·
              rfl

theorem cell21_419086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 12].length) (baseStart_419086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419086 prefixEnd_419086 := by exact prefixLift 419086
  have htrace : WordTrace (prefixWord ++ tailWord_419086) baseStart_419086 baseEnd_419086 := by
    simpa [prefixWord, tailWord_419086, baseEnd_419086] using wordTrace_append hprefix tailTrace_419086
  have hstable : (prefixWord ++ tailWord_419086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419086).length < 2 ^ (prefixWord ++ tailWord_419086).sum := by decide
  have hdescent : baseEnd_419086 < baseStart_419086 := by decide
  rcases family_descends (prefixWord ++ tailWord_419086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419148 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_419148 : Nat := 118140960795 + 419148 * 2 ^ 59
def prefixEnd_419148 : Nat := 4983230072969 + 3 ^ 40 * 419148 * 2
def baseEnd_419148 : Nat := 95655284164813917876613

theorem tailTrace_419148 : CollatzResearch.WordTrace tailWord_419148 prefixEnd_419148 95655284164813917876613 := by
  unfold tailWord_419148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643791742752927812177049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10191722323670570416236065 7643791742752927812177049)
  ·
    refine ⟨5732843807064695859132787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7643791742752927812177049 5732843807064695859132787)
    ·
      refine ⟨8599265710597043788699181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5732843807064695859132787 8599265710597043788699181)
      ·
        refine ⟨3224724641473891420762193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8599265710597043788699181 3224724641473891420762193)
        ·
          refine ⟨2418543481105418565571645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3224724641473891420762193 2418543481105418565571645)
          ·
            refine ⟨906953805414531962089367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2418543481105418565571645 906953805414531962089367)
            ·
              refine ⟨1360430708121797943134051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906953805414531962089367 1360430708121797943134051)
              ·
                refine ⟨2040646062182696914701077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360430708121797943134051 2040646062182696914701077)
                ·
                  refine ⟨95655284164813917876613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2040646062182696914701077 95655284164813917876613)
                  ·
                    rfl

theorem cell21_419148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_419148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419148 prefixEnd_419148 := by exact prefixLift 419148
  have htrace : WordTrace (prefixWord ++ tailWord_419148) baseStart_419148 baseEnd_419148 := by
    simpa [prefixWord, tailWord_419148, baseEnd_419148] using wordTrace_append hprefix tailTrace_419148
  have hstable : (prefixWord ++ tailWord_419148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419148).length < 2 ^ (prefixWord ++ tailWord_419148).sum := by decide
  have hdescent : baseEnd_419148 < baseStart_419148 := by decide
  rcases family_descends (prefixWord ++ tailWord_419148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419286 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_419286 : Nat := 118140960795 + 419286 * 2 ^ 59
def prefixEnd_419286 : Nat := 4983230072969 + 3 ^ 40 * 419286 * 2
def baseEnd_419286 : Nat := 95686777644956344576331

theorem tailTrace_419286 : CollatzResearch.WordTrace tailWord_419286 prefixEnd_419286 95686777644956344576331 := by
  unfold tailWord_419286
  simp only [CollatzResearch.WordTrace]
  refine ⟨955788547437869074554857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10195077839337270128585141 955788547437869074554857)
  ·
    refine ⟨716841410578401805916143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 955788547437869074554857 716841410578401805916143)
    ·
      refine ⟨1075262115867602708874215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716841410578401805916143 1075262115867602708874215)
      ·
        refine ⟨1612893173801404063311323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075262115867602708874215 1612893173801404063311323)
        ·
          refine ⟨2419339760702106094966985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612893173801404063311323 2419339760702106094966985)
          ·
            refine ⟨1814504820526579571225239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419339760702106094966985 1814504820526579571225239)
            ·
              refine ⟨2721757230789869356837859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814504820526579571225239 2721757230789869356837859)
              ·
                refine ⟨4082635846184804035256789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721757230789869356837859 4082635846184804035256789)
                ·
                  refine ⟨95686777644956344576331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4082635846184804035256789 95686777644956344576331)
                  ·
                    rfl

theorem cell21_419286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_419286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419286 prefixEnd_419286 := by exact prefixLift 419286
  have htrace : WordTrace (prefixWord ++ tailWord_419286) baseStart_419286 baseEnd_419286 := by
    simpa [prefixWord, tailWord_419286, baseEnd_419286] using wordTrace_append hprefix tailTrace_419286
  have hstable : (prefixWord ++ tailWord_419286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419286).length < 2 ^ (prefixWord ++ tailWord_419286).sum := by decide
  have hdescent : baseEnd_419286 < baseStart_419286 := by decide
  rcases family_descends (prefixWord ++ tailWord_419286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419303 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 3]
def baseStart_419303 : Nat := 118140960795 + 419303 * 2 ^ 59
def prefixEnd_419303 : Nat := 4983230072969 + 3 ^ 40 * 419303 * 2
def baseEnd_419303 : Nat := 95690657276568092792963

theorem tailTrace_419303 : CollatzResearch.WordTrace tailWord_419303 prefixEnd_419303 95690657276568092792963 := by
  unfold tailWord_419303
  simp only [CollatzResearch.WordTrace]
  refine ⟨15293236799944317096246563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10195491199962878064164375 15293236799944317096246563)
  ·
    refine ⟨22939855199916475644369845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15293236799944317096246563 22939855199916475644369845)
    ·
      refine ⟨2150611424992169591659673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22939855199916475644369845 2150611424992169591659673)
      ·
        refine ⟨1612958568744127193744755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2150611424992169591659673 1612958568744127193744755)
        ·
          refine ⟨2419437853116190790617133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612958568744127193744755 2419437853116190790617133)
          ·
            refine ⟨907289194918571546481425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2419437853116190790617133 907289194918571546481425)
            ·
              refine ⟨680466896188928659861069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907289194918571546481425 680466896188928659861069)
              ·
                refine ⟨255175086070848247447901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680466896188928659861069 255175086070848247447901)
                ·
                  refine ⟨95690657276568092792963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255175086070848247447901 95690657276568092792963)
                  ·
                    rfl

theorem cell21_419303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 3].length) (baseStart_419303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419303 prefixEnd_419303 := by exact prefixLift 419303
  have htrace : WordTrace (prefixWord ++ tailWord_419303) baseStart_419303 baseEnd_419303 := by
    simpa [prefixWord, tailWord_419303, baseEnd_419303] using wordTrace_append hprefix tailTrace_419303
  have hstable : (prefixWord ++ tailWord_419303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419303).length < 2 ^ (prefixWord ++ tailWord_419303).sum := by decide
  have hdescent : baseEnd_419303 < baseStart_419303 := by decide
  rcases family_descends (prefixWord ++ tailWord_419303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419317 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 6]
def baseStart_419317 : Nat := 118140960795 + 419317 * 2 ^ 59
def prefixEnd_419317 : Nat := 4983230072969 + 3 ^ 40 * 419317 * 2
def baseEnd_419317 : Nat := 95693852267307179559601

theorem tailTrace_419317 : CollatzResearch.WordTrace tailWord_419317 prefixEnd_419317 95693852267307179559601 := by
  unfold tailWord_419317
  simp only [CollatzResearch.WordTrace]
  refine ⟨15293747421893597487256205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10195831614595731658170803 15293747421893597487256205)
  ·
    refine ⟨5735155283210099057721077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15293747421893597487256205 5735155283210099057721077)
    ·
      refine ⟨537670807800946786661351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5735155283210099057721077 537670807800946786661351)
      ·
        refine ⟨806506211701420179992027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537670807800946786661351 806506211701420179992027)
        ·
          refine ⟨1209759317552130269988041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806506211701420179992027 1209759317552130269988041)
          ·
            refine ⟨907319488164097702491031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209759317552130269988041 907319488164097702491031)
            ·
              refine ⟨1360979232246146553736547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907319488164097702491031 1360979232246146553736547)
              ·
                refine ⟨2041468848369219830604821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360979232246146553736547 2041468848369219830604821)
                ·
                  refine ⟨95693852267307179559601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2041468848369219830604821 95693852267307179559601)
                  ·
                    rfl

theorem cell21_419317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_419317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419317 prefixEnd_419317 := by exact prefixLift 419317
  have htrace : WordTrace (prefixWord ++ tailWord_419317) baseStart_419317 baseEnd_419317 := by
    simpa [prefixWord, tailWord_419317, baseEnd_419317] using wordTrace_append hprefix tailTrace_419317
  have hstable : (prefixWord ++ tailWord_419317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419317).length < 2 ^ (prefixWord ++ tailWord_419317).sum := by decide
  have hdescent : baseEnd_419317 < baseStart_419317 := by decide
  rcases family_descends (prefixWord ++ tailWord_419317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419348 : List Nat := [2, 4, 3, 1, 2, 1, 1, 7]
def baseStart_419348 : Nat := 118140960795 + 419348 * 2 ^ 59
def prefixEnd_419348 : Nat := 4983230072969 + 3 ^ 40 * 419348 * 2
def baseEnd_419348 : Nat := 31900308963219338180957

theorem tailTrace_419348 : CollatzResearch.WordTrace tailWord_419348 prefixEnd_419348 31900308963219338180957 := by
  unfold tailWord_419348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647439042390644890817349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10196585389854193187756465 7647439042390644890817349)
  ·
    refine ⟨1433894820448245917028253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7647439042390644890817349 1433894820448245917028253)
    ·
      refine ⟨537710557668092218885595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1433894820448245917028253 537710557668092218885595)
      ·
        refine ⟨806565836502138328328393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537710557668092218885595 806565836502138328328393)
        ·
          refine ⟨604924377376603746246295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806565836502138328328393 604924377376603746246295)
          ·
            refine ⟨907386566064905619369443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604924377376603746246295 907386566064905619369443)
            ·
              refine ⟨1361079849097358429054165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907386566064905619369443 1361079849097358429054165)
              ·
                refine ⟨31900308963219338180957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1361079849097358429054165 31900308963219338180957)
                ·
                  rfl

theorem cell21_419348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_419348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419348 prefixEnd_419348 := by exact prefixLift 419348
  have htrace : WordTrace (prefixWord ++ tailWord_419348) baseStart_419348 baseEnd_419348 := by
    simpa [prefixWord, tailWord_419348, baseEnd_419348] using wordTrace_append hprefix tailTrace_419348
  have hstable : (prefixWord ++ tailWord_419348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419348).length < 2 ^ (prefixWord ++ tailWord_419348).sum := by decide
  have hdescent : baseEnd_419348 < baseStart_419348 := by decide
  rcases family_descends (prefixWord ++ tailWord_419348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419359 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_419359 : Nat := 118140960795 + 419359 * 2 ^ 59
def prefixEnd_419359 : Nat := 4983230072969 + 3 ^ 40 * 419359 * 2
def baseEnd_419359 : Nat := 95703437239524439859515

theorem tailTrace_419359 : CollatzResearch.WordTrace tailWord_419359 prefixEnd_419359 95703437239524439859515 := by
  unfold tailWord_419359
  simp only [CollatzResearch.WordTrace]
  refine ⟨15295279287741438660285131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10196852858494292440190087 15295279287741438660285131)
  ·
    refine ⟨22942918931612157990427697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15295279287741438660285131 22942918931612157990427697)
    ·
      refine ⟨17207189198709118492820773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22942918931612157990427697 17207189198709118492820773)
      ·
        refine ⟨3226347974757959717403895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17207189198709118492820773 3226347974757959717403895)
        ·
          refine ⟨4839521962136939576105843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226347974757959717403895 4839521962136939576105843)
          ·
            refine ⟨7259282943205409364158765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839521962136939576105843 7259282943205409364158765)
            ·
              refine ⟨2722231103702028511559537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7259282943205409364158765 2722231103702028511559537)
              ·
                refine ⟨2041673327776521383669653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722231103702028511559537 2041673327776521383669653)
                ·
                  refine ⟨95703437239524439859515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2041673327776521383669653 95703437239524439859515)
                  ·
                    rfl

theorem cell21_419359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_419359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419359 prefixEnd_419359 := by exact prefixLift 419359
  have htrace : WordTrace (prefixWord ++ tailWord_419359) baseStart_419359 baseEnd_419359 := by
    simpa [prefixWord, tailWord_419359, baseEnd_419359] using wordTrace_append hprefix tailTrace_419359
  have hstable : (prefixWord ++ tailWord_419359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419359).length < 2 ^ (prefixWord ++ tailWord_419359).sum := by decide
  have hdescent : baseEnd_419359 < baseStart_419359 := by decide
  rcases family_descends (prefixWord ++ tailWord_419359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419379 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 3]
def baseStart_419379 : Nat := 118140960795 + 419379 * 2 ^ 59
def prefixEnd_419379 : Nat := 4983230072969 + 3 ^ 40 * 419379 * 2
def baseEnd_419379 : Nat := 95708001512008849526141

theorem tailTrace_419379 : CollatzResearch.WordTrace tailWord_419379 prefixEnd_419379 95708001512008849526141 := by
  unfold tailWord_419379
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296008747668982076013191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10197339165112654717342127 15296008747668982076013191)
  ·
    refine ⟨22944013121503473114019787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15296008747668982076013191 22944013121503473114019787)
    ·
      refine ⟨34416019682255209671029681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22944013121503473114019787 34416019682255209671029681)
      ·
        refine ⟨25812014761691407253272261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34416019682255209671029681 25812014761691407253272261)
        ·
          refine ⟨4839752767817138859988549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25812014761691407253272261 4839752767817138859988549)
          ·
            refine ⟨907453643965713536247853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4839752767817138859988549 907453643965713536247853)
            ·
              refine ⟨340295116487142576092945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 907453643965713536247853 340295116487142576092945)
              ·
                refine ⟨255221337365356932069709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340295116487142576092945 255221337365356932069709)
                ·
                  refine ⟨95708001512008849526141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255221337365356932069709 95708001512008849526141)
                  ·
                    rfl

theorem cell21_419379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 3].length) (baseStart_419379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419379 prefixEnd_419379 := by exact prefixLift 419379
  have htrace : WordTrace (prefixWord ++ tailWord_419379) baseStart_419379 baseEnd_419379 := by
    simpa [prefixWord, tailWord_419379, baseEnd_419379] using wordTrace_append hprefix tailTrace_419379
  have hstable : (prefixWord ++ tailWord_419379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419379).length < 2 ^ (prefixWord ++ tailWord_419379).sum := by decide
  have hdescent : baseEnd_419379 < baseStart_419379 := by decide
  rcases family_descends (prefixWord ++ tailWord_419379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419486 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_419486 : Nat := 118140960795 + 419486 * 2 ^ 59
def prefixEnd_419486 : Nat := 4983230072969 + 3 ^ 40 * 419486 * 2
def baseEnd_419486 : Nat := 95732420369800441242589

theorem tailTrace_419486 : CollatzResearch.WordTrace tailWord_419486 prefixEnd_419486 95732420369800441242589 := by
  unfold tailWord_419486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912488919785167418769789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10199940905520892900105541 1912488919785167418769789)
  ·
    refine ⟨717183344919437782038671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1912488919785167418769789 717183344919437782038671)
    ·
      refine ⟨1075775017379156673058007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717183344919437782038671 1075775017379156673058007)
      ·
        refine ⟨1613662526068735009587011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075775017379156673058007 1613662526068735009587011)
        ·
          refine ⟨2420493789103102514380517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613662526068735009587011 2420493789103102514380517)
          ·
            refine ⟨453842585456831721446347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2420493789103102514380517 453842585456831721446347)
            ·
              refine ⟨680763878185247582169521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453842585456831721446347 680763878185247582169521)
              ·
                refine ⟨510572908638935686627141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680763878185247582169521 510572908638935686627141)
                ·
                  refine ⟨95732420369800441242589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510572908638935686627141 95732420369800441242589)
                  ·
                    rfl

theorem cell21_419486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_419486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419486 prefixEnd_419486 := by exact prefixLift 419486
  have htrace : WordTrace (prefixWord ++ tailWord_419486) baseStart_419486 baseEnd_419486 := by
    simpa [prefixWord, tailWord_419486, baseEnd_419486] using wordTrace_append hprefix tailTrace_419486
  have hstable : (prefixWord ++ tailWord_419486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419486).length < 2 ^ (prefixWord ++ tailWord_419486).sum := by decide
  have hdescent : baseEnd_419486 < baseStart_419486 := by decide
  rcases family_descends (prefixWord ++ tailWord_419486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419525 : List Nat := [1, 3, 1, 1, 1, 1, 2, 11]
def baseStart_419525 : Nat := 118140960795 + 419525 * 2 ^ 59
def prefixEnd_419525 : Nat := 4983230072969 + 3 ^ 40 * 419525 * 2
def baseEnd_419525 : Nat := 31913773567048346697503

theorem tailTrace_419525 : CollatzResearch.WordTrace tailWord_419525 prefixEnd_419525 31913773567048346697503 := by
  unfold tailWord_419525
  simp only [CollatzResearch.WordTrace]
  refine ⟨15301333805140049010828029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10200889203426699340552019 15301333805140049010828029)
  ·
    refine ⟨5738000176927518379060511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15301333805140049010828029 5738000176927518379060511)
    ·
      refine ⟨8607000265391277568590767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738000176927518379060511 8607000265391277568590767)
      ·
        refine ⟨12910500398086916352886151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607000265391277568590767 12910500398086916352886151)
        ·
          refine ⟨19365750597130374529329227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12910500398086916352886151 19365750597130374529329227)
          ·
            refine ⟨29048625895695561793993841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19365750597130374529329227 29048625895695561793993841)
            ·
              refine ⟨21786469421771671345495381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29048625895695561793993841 21786469421771671345495381)
              ·
                refine ⟨31913773567048346697503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21786469421771671345495381 31913773567048346697503)
                ·
                  rfl

theorem cell21_419525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_419525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419525 prefixEnd_419525 := by exact prefixLift 419525
  have htrace : WordTrace (prefixWord ++ tailWord_419525) baseStart_419525 baseEnd_419525 := by
    simpa [prefixWord, tailWord_419525, baseEnd_419525] using wordTrace_append hprefix tailTrace_419525
  have hstable : (prefixWord ++ tailWord_419525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419525).length < 2 ^ (prefixWord ++ tailWord_419525).sum := by decide
  have hdescent : baseEnd_419525 < baseStart_419525 := by decide
  rcases family_descends (prefixWord ++ tailWord_419525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419548 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_419548 : Nat := 118140960795 + 419548 * 2 ^ 59
def prefixEnd_419548 : Nat := 4983230072969 + 3 ^ 40 * 419548 * 2
def baseEnd_419548 : Nat := 95746569614502111209129

theorem tailTrace_419548 : CollatzResearch.WordTrace tailWord_419548 prefixEnd_419548 95746569614502111209129 := by
  unfold tailWord_419548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651086342028361969457649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10201448456037815959276865 7651086342028361969457649)
  ·
    refine ⟨5738314756521271477093237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7651086342028361969457649 5738314756521271477093237)
    ·
      refine ⟨537967008423869200977491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5738314756521271477093237 537967008423869200977491)
      ·
        refine ⟨806950512635803801466237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537967008423869200977491 806950512635803801466237)
        ·
          refine ⟨302606442238426425549839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 806950512635803801466237 302606442238426425549839)
          ·
            refine ⟨453909663357639638324759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302606442238426425549839 453909663357639638324759)
            ·
              refine ⟨680864495036459457487139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453909663357639638324759 680864495036459457487139)
              ·
                refine ⟨1021296742554689186230709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680864495036459457487139 1021296742554689186230709)
                ·
                  refine ⟨95746569614502111209129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1021296742554689186230709 95746569614502111209129)
                  ·
                    rfl

theorem cell21_419548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_419548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419548 prefixEnd_419548 := by exact prefixLift 419548
  have htrace : WordTrace (prefixWord ++ tailWord_419548) baseStart_419548 baseEnd_419548 := by
    simpa [prefixWord, tailWord_419548, baseEnd_419548] using wordTrace_append hprefix tailTrace_419548
  have hstable : (prefixWord ++ tailWord_419548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419548).length < 2 ^ (prefixWord ++ tailWord_419548).sum := by decide
  have hdescent : baseEnd_419548 < baseStart_419548 := by decide
  rcases family_descends (prefixWord ++ tailWord_419548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419607 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 3]
def baseStart_419607 : Nat := 118140960795 + 419607 * 2 ^ 59
def prefixEnd_419607 : Nat := 4983230072969 + 3 ^ 40 * 419607 * 2
def baseEnd_419607 : Nat := 95760034218331119725675

theorem tailTrace_419607 : CollatzResearch.WordTrace tailWord_419607 prefixEnd_419607 95760034218331119725675 := by
  unfold tailWord_419607
  simp only [CollatzResearch.WordTrace]
  refine ⟨15304324590842977015313075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10202883060561984676875383 15304324590842977015313075)
  ·
    refine ⟨22956486886264465522969613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15304324590842977015313075 22956486886264465522969613)
    ·
      refine ⟨8608682582349174571113605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22956486886264465522969613 8608682582349174571113605)
      ·
        refine ⟨1614127984190470232083801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8608682582349174571113605 1614127984190470232083801)
        ·
          refine ⟨1210595988142852674062851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614127984190470232083801 1210595988142852674062851)
          ·
            refine ⟨1815893982214279011094277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210595988142852674062851 1815893982214279011094277)
            ·
              refine ⟨340480121665177314580177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1815893982214279011094277 340480121665177314580177)
              ·
                refine ⟨255360091248882985935133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340480121665177314580177 255360091248882985935133)
                ·
                  refine ⟨95760034218331119725675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255360091248882985935133 95760034218331119725675)
                  ·
                    rfl

theorem cell21_419607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 3].length) (baseStart_419607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419607 prefixEnd_419607 := by exact prefixLift 419607
  have htrace : WordTrace (prefixWord ++ tailWord_419607) baseStart_419607 baseEnd_419607 := by
    simpa [prefixWord, tailWord_419607, baseEnd_419607] using wordTrace_append hprefix tailTrace_419607
  have hstable : (prefixWord ++ tailWord_419607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419607).length < 2 ^ (prefixWord ++ tailWord_419607).sum := by decide
  have hdescent : baseEnd_419607 < baseStart_419607 := by decide
  rcases family_descends (prefixWord ++ tailWord_419607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419635 : List Nat := [1, 1, 1, 2, 7, 1, 3, 5]
def baseStart_419635 : Nat := 118140960795 + 419635 * 2 ^ 59
def prefixEnd_419635 : Nat := 4983230072969 + 3 ^ 40 * 419635 * 2
def baseEnd_419635 : Nat := 31922141399936431086317

theorem tailTrace_419635 : CollatzResearch.WordTrace tailWord_419635 prefixEnd_419635 31922141399936431086317 := by
  unfold tailWord_419635
  simp only [CollatzResearch.WordTrace]
  refine ⟨15305345834741537797332359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10203563889827691864888239 15305345834741537797332359)
  ·
    refine ⟨22958018752112306695998539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15305345834741537797332359 22958018752112306695998539)
    ·
      refine ⟨34437028128168460043997809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22958018752112306695998539 34437028128168460043997809)
      ·
        refine ⟨25827771096126345032998357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34437028128168460043997809 25827771096126345032998357)
        ·
          refine ⟨605338385065461211710899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25827771096126345032998357 605338385065461211710899)
          ·
            refine ⟨908007577598191817566349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605338385065461211710899 908007577598191817566349)
            ·
              refine ⟨340502841599321931587381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908007577598191817566349 340502841599321931587381)
              ·
                refine ⟨31922141399936431086317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 340502841599321931587381 31922141399936431086317)
                ·
                  rfl

theorem cell21_419635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 5].length) (baseStart_419635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419635 prefixEnd_419635 := by exact prefixLift 419635
  have htrace : WordTrace (prefixWord ++ tailWord_419635) baseStart_419635 baseEnd_419635 := by
    simpa [prefixWord, tailWord_419635, baseEnd_419635] using wordTrace_append hprefix tailTrace_419635
  have hstable : (prefixWord ++ tailWord_419635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419635).length < 2 ^ (prefixWord ++ tailWord_419635).sum := by decide
  have hdescent : baseEnd_419635 < baseStart_419635 := by decide
  rcases family_descends (prefixWord ++ tailWord_419635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419666 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_419666 : Nat := 118140960795 + 419666 * 2 ^ 59
def prefixEnd_419666 : Nat := 4983230072969 + 3 ^ 40 * 419666 * 2
def baseEnd_419666 : Nat := 95773498822160128242221

theorem tailTrace_419666 : CollatzResearch.WordTrace tailWord_419666 prefixEnd_419666 95773498822160128242221 := by
  unfold tailWord_419666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3826619124407307522927713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10204317665086153394473901 3826619124407307522927713)
  ·
    refine ⟨2869964343305480642195785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3826619124407307522927713 2869964343305480642195785)
    ·
      refine ⟨2152473257479110481646839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2869964343305480642195785 2152473257479110481646839)
      ·
        refine ⟨3228709886218665722470259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152473257479110481646839 3228709886218665722470259)
        ·
          refine ⟨4843064829327998583705389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228709886218665722470259 4843064829327998583705389)
          ·
            refine ⟨1816149310997999468889521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4843064829327998583705389 1816149310997999468889521)
            ·
              refine ⟨1362111983248499601667141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816149310997999468889521 1362111983248499601667141)
              ·
                refine ⟨255395996859093675312589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1362111983248499601667141 255395996859093675312589)
                ·
                  refine ⟨95773498822160128242221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255395996859093675312589 95773498822160128242221)
                  ·
                    rfl

theorem cell21_419666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_419666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419666 prefixEnd_419666 := by exact prefixLift 419666
  have htrace : WordTrace (prefixWord ++ tailWord_419666) baseStart_419666 baseEnd_419666 := by
    simpa [prefixWord, tailWord_419666, baseEnd_419666] using wordTrace_append hprefix tailTrace_419666
  have hstable : (prefixWord ++ tailWord_419666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419666).length < 2 ^ (prefixWord ++ tailWord_419666).sum := by decide
  have hdescent : baseEnd_419666 < baseStart_419666 := by decide
  rcases family_descends (prefixWord ++ tailWord_419666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419801 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 5]
def baseStart_419801 : Nat := 118140960795 + 419801 * 2 ^ 59
def prefixEnd_419801 : Nat := 4983230072969 + 3 ^ 40 * 419801 * 2
def baseEnd_419801 : Nat := 95804307661429893491945

theorem tailTrace_419801 : CollatzResearch.WordTrace tailWord_419801 prefixEnd_419801 95804307661429893491945 := by
  unfold tailWord_419801
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311400352140148147875257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10207600234760098765250171 15311400352140148147875257)
  ·
    refine ⟨11483550264105111110906443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15311400352140148147875257 11483550264105111110906443)
    ·
      refine ⟨17225325396157666666359665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11483550264105111110906443 17225325396157666666359665)
      ·
        refine ⟨12918994047118249999769749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17225325396157666666359665 12918994047118249999769749)
        ·
          refine ⟨605577845958667968739207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12918994047118249999769749 605577845958667968739207)
          ·
            refine ⟨908366768938001953108811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605577845958667968739207 908366768938001953108811)
            ·
              refine ⟨1362550153407002929663217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908366768938001953108811 1362550153407002929663217)
              ·
                refine ⟨1021912615055252197247413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362550153407002929663217 1021912615055252197247413)
                ·
                  refine ⟨95804307661429893491945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1021912615055252197247413 95804307661429893491945)
                  ·
                    rfl

theorem cell21_419801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_419801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419801 prefixEnd_419801 := by exact prefixLift 419801
  have htrace : WordTrace (prefixWord ++ tailWord_419801) baseStart_419801 baseEnd_419801 := by
    simpa [prefixWord, tailWord_419801, baseEnd_419801] using wordTrace_append hprefix tailTrace_419801
  have hstable : (prefixWord ++ tailWord_419801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419801).length < 2 ^ (prefixWord ++ tailWord_419801).sum := by decide
  have hdescent : baseEnd_419801 < baseStart_419801 := by decide
  rcases family_descends (prefixWord ++ tailWord_419801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419818 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_419818 : Nat := 118140960795 + 419818 * 2 ^ 59
def prefixEnd_419818 : Nat := 4983230072969 + 3 ^ 40 * 419818 * 2
def baseEnd_419818 : Nat := 95808187293041641708577

theorem tailTrace_419818 : CollatzResearch.WordTrace tailWord_419818 prefixEnd_419818 95808187293041641708577 := by
  unfold tailWord_419818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828005098269640012811027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10208013595385706700829405 3828005098269640012811027)
  ·
    refine ⟨5742007647404460019216541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3828005098269640012811027 5742007647404460019216541)
    ·
      refine ⟨2153252867776672507206203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5742007647404460019216541 2153252867776672507206203)
      ·
        refine ⟨3229879301665008760809305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153252867776672507206203 3229879301665008760809305)
        ·
          refine ⟨2422409476248756570606979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3229879301665008760809305 2422409476248756570606979)
          ·
            refine ⟨3633614214373134855910469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422409476248756570606979 3633614214373134855910469)
            ·
              refine ⟨681302665194962785483213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3633614214373134855910469 681302665194962785483213)
              ·
                refine ⟨255488499448111044556205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 681302665194962785483213 255488499448111044556205)
                ·
                  refine ⟨95808187293041641708577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255488499448111044556205 95808187293041641708577)
                  ·
                    rfl

theorem cell21_419818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_419818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419818 prefixEnd_419818 := by exact prefixLift 419818
  have htrace : WordTrace (prefixWord ++ tailWord_419818) baseStart_419818 baseEnd_419818 := by
    simpa [prefixWord, tailWord_419818, baseEnd_419818] using wordTrace_append hprefix tailTrace_419818
  have hstable : (prefixWord ++ tailWord_419818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419818).length < 2 ^ (prefixWord ++ tailWord_419818).sum := by decide
  have hdescent : baseEnd_419818 < baseStart_419818 := by decide
  rcases family_descends (prefixWord ++ tailWord_419818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419880 : List Nat := [2, 1, 5, 3, 2, 1, 7]
def baseStart_419880 : Nat := 118140960795 + 419880 * 2 ^ 59
def prefixEnd_419880 : Nat := 4983230072969 + 3 ^ 40 * 419880 * 2
def baseEnd_419880 : Nat := 10646926281971479075013

theorem tailTrace_419880 : CollatzResearch.WordTrace tailWord_419880 prefixEnd_419880 10646926281971479075013 := by
  unfold tailWord_419880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657140859426972320000547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10209521145902629760000729 7657140859426972320000547)
  ·
    refine ⟨11485711289140458480000821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7657140859426972320000547 11485711289140458480000821)
    ·
      refine ⟨1076785433356917982500077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11485711289140458480000821 1076785433356917982500077)
      ·
        refine ⟨403794537508844243437529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1076785433356917982500077 403794537508844243437529)
        ·
          refine ⟨302845903131633182578147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403794537508844243437529 302845903131633182578147)
          ·
            refine ⟨454268854697449773867221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302845903131633182578147 454268854697449773867221)
            ·
              refine ⟨10646926281971479075013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 454268854697449773867221 10646926281971479075013)
              ·
                rfl

theorem cell21_419880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 7].length) (baseStart_419880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419880 prefixEnd_419880 := by exact prefixLift 419880
  have htrace : WordTrace (prefixWord ++ tailWord_419880) baseStart_419880 baseEnd_419880 := by
    simpa [prefixWord, tailWord_419880, baseEnd_419880] using wordTrace_append hprefix tailTrace_419880
  have hstable : (prefixWord ++ tailWord_419880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419880).length < 2 ^ (prefixWord ++ tailWord_419880).sum := by decide
  have hdescent : baseEnd_419880 < baseStart_419880 := by decide
  rcases family_descends (prefixWord ++ tailWord_419880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419953 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 3]
def baseStart_419953 : Nat := 118140960795 + 419953 * 2 ^ 59
def prefixEnd_419953 : Nat := 4983230072969 + 3 ^ 40 * 419953 * 2
def baseEnd_419953 : Nat := 95838996132311406958301

theorem tailTrace_419953 : CollatzResearch.WordTrace tailWord_419953 prefixEnd_419953 95838996132311406958301 := by
  unfold tailWord_419953
  simp only [CollatzResearch.WordTrace]
  refine ⟨15316944247589478107408513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10211296165059652071605675 15316944247589478107408513)
  ·
    refine ⟨11487708185692108580556385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15316944247589478107408513 11487708185692108580556385)
    ·
      refine ⟨8615781139269081435417289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11487708185692108580556385 8615781139269081435417289)
      ·
        refine ⟨6461835854451811076562967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8615781139269081435417289 6461835854451811076562967)
        ·
          refine ⟨9692753781677716614844451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461835854451811076562967 9692753781677716614844451)
          ·
            refine ⟨14539130672516574922266677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692753781677716614844451 14539130672516574922266677)
            ·
              refine ⟨1363043500548428898962501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14539130672516574922266677 1363043500548428898962501)
              ·
                refine ⟨255570656352830418555469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1363043500548428898962501 255570656352830418555469)
                ·
                  refine ⟨95838996132311406958301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255570656352830418555469 95838996132311406958301)
                  ·
                    rfl

theorem cell21_419953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_419953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419953 prefixEnd_419953 := by exact prefixLift 419953
  have htrace : WordTrace (prefixWord ++ tailWord_419953) baseStart_419953 baseEnd_419953 := by
    simpa [prefixWord, tailWord_419953, baseEnd_419953] using wordTrace_append hprefix tailTrace_419953
  have hstable : (prefixWord ++ tailWord_419953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419953).length < 2 ^ (prefixWord ++ tailWord_419953).sum := by decide
  have hdescent : baseEnd_419953 < baseStart_419953 := by decide
  rcases family_descends (prefixWord ++ tailWord_419953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419995 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_419995 : Nat := 118140960795 + 419995 * 2 ^ 59
def prefixEnd_419995 : Nat := 4983230072969 + 3 ^ 40 * 419995 * 2
def baseEnd_419995 : Nat := 95848581104528667258215

theorem tailTrace_419995 : CollatzResearch.WordTrace tailWord_419995 prefixEnd_419995 95848581104528667258215 := by
  unfold tailWord_419995
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318476113437319280437439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10212317408958212853624959 15318476113437319280437439)
  ·
    refine ⟨22977714170155978920656159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15318476113437319280437439 22977714170155978920656159)
    ·
      refine ⟨34466571255233968380984239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22977714170155978920656159 34466571255233968380984239)
      ·
        refine ⟨51699856882850952571476359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34466571255233968380984239 51699856882850952571476359)
        ·
          refine ⟨77549785324276428857214539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51699856882850952571476359 77549785324276428857214539)
          ·
            refine ⟨116324677986414643285821809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77549785324276428857214539 116324677986414643285821809)
            ·
              refine ⟨87243508489810982464366357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116324677986414643285821809 87243508489810982464366357)
              ·
                refine ⟨4089539460459889803017173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87243508489810982464366357 4089539460459889803017173)
                ·
                  refine ⟨95848581104528667258215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4089539460459889803017173 95848581104528667258215)
                  ·
                    rfl

theorem cell21_419995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_419995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_419995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_419995 prefixEnd_419995 := by exact prefixLift 419995
  have htrace : WordTrace (prefixWord ++ tailWord_419995) baseStart_419995 baseEnd_419995 := by
    simpa [prefixWord, tailWord_419995, baseEnd_419995] using wordTrace_append hprefix tailTrace_419995
  have hstable : (prefixWord ++ tailWord_419995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419995).length < 2 ^ (prefixWord ++ tailWord_419995).sum := by decide
  have hdescent : baseEnd_419995 < baseStart_419995 := by decide
  rcases family_descends (prefixWord ++ tailWord_419995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420046 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_420046 : Nat := 118140960795 + 420046 * 2 ^ 59
def prefixEnd_420046 : Nat := 4983230072969 + 3 ^ 40 * 420046 * 2
def baseEnd_420046 : Nat := 95860219999363911908111

theorem tailTrace_420046 : CollatzResearch.WordTrace tailWord_420046 prefixEnd_420046 95860219999363911908111 := by
  unfold tailWord_420046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915042029531569373817999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10213557490835036660362661 1915042029531569373817999)
  ·
    refine ⟨2872563044297354060726999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1915042029531569373817999 2872563044297354060726999)
    ·
      refine ⟨4308844566446031091090499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872563044297354060726999 4308844566446031091090499)
      ·
        refine ⟨6463266849669046636635749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308844566446031091090499 6463266849669046636635749)
        ·
          refine ⟨1211862534312946244369203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6463266849669046636635749 1211862534312946244369203)
          ·
            refine ⟨1817793801469419366553805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211862534312946244369203 1817793801469419366553805)
            ·
              refine ⟨681672675551032262457677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1817793801469419366553805 681672675551032262457677)
              ·
                refine ⟨255627253331637098421629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 681672675551032262457677 255627253331637098421629)
                ·
                  refine ⟨95860219999363911908111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255627253331637098421629 95860219999363911908111)
                  ·
                    rfl

theorem cell21_420046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_420046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420046 prefixEnd_420046 := by exact prefixLift 420046
  have htrace : WordTrace (prefixWord ++ tailWord_420046) baseStart_420046 baseEnd_420046 := by
    simpa [prefixWord, tailWord_420046, baseEnd_420046] using wordTrace_append hprefix tailTrace_420046
  have hstable : (prefixWord ++ tailWord_420046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420046).length < 2 ^ (prefixWord ++ tailWord_420046).sum := by decide
  have hdescent : baseEnd_420046 < baseStart_420046 := by decide
  rcases family_descends (prefixWord ++ tailWord_420046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420119 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 4]
def baseStart_420119 : Nat := 118140960795 + 420119 * 2 ^ 59
def prefixEnd_420119 : Nat := 4983230072969 + 3 ^ 40 * 420119 * 2
def baseEnd_420119 : Nat := 95876879593932007191295

theorem tailTrace_420119 : CollatzResearch.WordTrace tailWord_420119 prefixEnd_420119 95876879593932007191295 := by
  unfold tailWord_420119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15322998764988088457951411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10215332509992058971967607 15322998764988088457951411)
  ·
    refine ⟨22984498147482132686927117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15322998764988088457951411 22984498147482132686927117)
    ·
      refine ⟨8619186805305799757597669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22984498147482132686927117 8619186805305799757597669)
      ·
        refine ⟨1616097525994837454549563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8619186805305799757597669 1616097525994837454549563)
        ·
          refine ⟨2424146288992256181824345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616097525994837454549563 2424146288992256181824345)
          ·
            refine ⟨1818109716744192136368259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424146288992256181824345 1818109716744192136368259)
            ·
              refine ⟨2727164575116288204552389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818109716744192136368259 2727164575116288204552389)
              ·
                refine ⟨511343357834304038353573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2727164575116288204552389 511343357834304038353573)
                ·
                  refine ⟨95876879593932007191295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511343357834304038353573 95876879593932007191295)
                  ·
                    rfl

theorem cell21_420119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_420119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420119 prefixEnd_420119 := by exact prefixLift 420119
  have htrace : WordTrace (prefixWord ++ tailWord_420119) baseStart_420119 baseEnd_420119 := by
    simpa [prefixWord, tailWord_420119, baseEnd_420119] using wordTrace_append hprefix tailTrace_420119
  have hstable : (prefixWord ++ tailWord_420119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420119).length < 2 ^ (prefixWord ++ tailWord_420119).sum := by decide
  have hdescent : baseEnd_420119 < baseStart_420119 := by decide
  rcases family_descends (prefixWord ++ tailWord_420119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420122 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_420122 : Nat := 118140960795 + 420122 * 2 ^ 59
def prefixEnd_420122 : Nat := 4983230072969 + 3 ^ 40 * 420122 * 2
def baseEnd_420122 : Nat := 95877564234804668641289

theorem tailTrace_420122 : CollatzResearch.WordTrace tailWord_420122 prefixEnd_420122 95877564234804668641289 := by
  unfold tailWord_420122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830777045994304992577655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10215405455984813313540413 3830777045994304992577655)
  ·
    refine ⟨5746165568991457488866483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3830777045994304992577655 5746165568991457488866483)
    ·
      refine ⟨8619248353487186233299725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746165568991457488866483 8619248353487186233299725)
      ·
        refine ⟨3232218132557694837487397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8619248353487186233299725 3232218132557694837487397)
        ·
          refine ⟨606040899854567782028887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3232218132557694837487397 606040899854567782028887)
          ·
            refine ⟨909061349781851673043331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606040899854567782028887 909061349781851673043331)
            ·
              refine ⟨1363592024672777509564997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909061349781851673043331 1363592024672777509564997)
              ·
                refine ⟨255673504626145783043437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1363592024672777509564997 255673504626145783043437)
                ·
                  refine ⟨95877564234804668641289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255673504626145783043437 95877564234804668641289)
                  ·
                    rfl

theorem cell21_420122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_420122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420122 prefixEnd_420122 := by exact prefixLift 420122
  have htrace : WordTrace (prefixWord ++ tailWord_420122) baseStart_420122 baseEnd_420122 := by
    simpa [prefixWord, tailWord_420122, baseEnd_420122] using wordTrace_append hprefix tailTrace_420122
  have hstable : (prefixWord ++ tailWord_420122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420122).length < 2 ^ (prefixWord ++ tailWord_420122).sum := by decide
  have hdescent : baseEnd_420122 < baseStart_420122 := by decide
  rcases family_descends (prefixWord ++ tailWord_420122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420181 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 5]
def baseStart_420181 : Nat := 118140960795 + 420181 * 2 ^ 59
def prefixEnd_420181 : Nat := 4983230072969 + 3 ^ 40 * 420181 * 2
def baseEnd_420181 : Nat := 95891028838633677157835

theorem tailTrace_420181 : CollatzResearch.WordTrace tailWord_420181 prefixEnd_420181 95891028838633677157835 := by
  unfold tailWord_420181
  simp only [CollatzResearch.WordTrace]
  refine ⟨15325260090763473046708397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10216840060508982031138931 15325260090763473046708397)
  ·
    refine ⟨5746972534036302392515649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15325260090763473046708397 5746972534036302392515649)
    ·
      refine ⟨4310229400527226794386737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5746972534036302392515649 4310229400527226794386737)
      ·
        refine ⟨3232672050395420095790053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4310229400527226794386737 3232672050395420095790053)
        ·
          refine ⟨606126009449141267960635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3232672050395420095790053 606126009449141267960635)
          ·
            refine ⟨909189014173711901940953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606126009449141267960635 909189014173711901940953)
            ·
              refine ⟨681891760630283926455715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909189014173711901940953 681891760630283926455715)
              ·
                refine ⟨1022837640945425889683573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681891760630283926455715 1022837640945425889683573)
                ·
                  refine ⟨95891028838633677157835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1022837640945425889683573 95891028838633677157835)
                  ·
                    rfl

theorem cell21_420181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_420181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420181 prefixEnd_420181 := by exact prefixLift 420181
  have htrace : WordTrace (prefixWord ++ tailWord_420181) baseStart_420181 baseEnd_420181 := by
    simpa [prefixWord, tailWord_420181, baseEnd_420181] using wordTrace_append hprefix tailTrace_420181
  have hstable : (prefixWord ++ tailWord_420181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420181).length < 2 ^ (prefixWord ++ tailWord_420181).sum := by decide
  have hdescent : baseEnd_420181 < baseStart_420181 := by decide
  rcases family_descends (prefixWord ++ tailWord_420181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420299 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_420299 : Nat := 118140960795 + 420299 * 2 ^ 59
def prefixEnd_420299 : Nat := 4983230072969 + 3 ^ 40 * 420299 * 2
def baseEnd_420299 : Nat := 95917958046291694190927

theorem tailTrace_420299 : CollatzResearch.WordTrace tailWord_420299 prefixEnd_420299 95917958046291694190927 := by
  unfold tailWord_420299
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329563904335979199503951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10219709269557319466335967 15329563904335979199503951)
  ·
    refine ⟨22994345856503968799255927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15329563904335979199503951 22994345856503968799255927)
    ·
      refine ⟨34491518784755953198883891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22994345856503968799255927 34491518784755953198883891)
      ·
        refine ⟨51737278177133929798325837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34491518784755953198883891 51737278177133929798325837)
        ·
          refine ⟨19401479316425223674372189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51737278177133929798325837 19401479316425223674372189)
          ·
            refine ⟨7275554743659458877889571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19401479316425223674372189 7275554743659458877889571)
            ·
              refine ⟨10913332115489188316834357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275554743659458877889571 10913332115489188316834357)
              ·
                refine ⟨1023124885827111404703221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10913332115489188316834357 1023124885827111404703221)
                ·
                  refine ⟨95917958046291694190927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1023124885827111404703221 95917958046291694190927)
                  ·
                    rfl

theorem cell21_420299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_420299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420299 prefixEnd_420299 := by exact prefixLift 420299
  have htrace : WordTrace (prefixWord ++ tailWord_420299) baseStart_420299 baseEnd_420299 := by
    simpa [prefixWord, tailWord_420299, baseEnd_420299] using wordTrace_append hprefix tailTrace_420299
  have hstable : (prefixWord ++ tailWord_420299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420299).length < 2 ^ (prefixWord ++ tailWord_420299).sum := by decide
  have hdescent : baseEnd_420299 < baseStart_420299 := by decide
  rcases family_descends (prefixWord ++ tailWord_420299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420344 : List Nat := [2, 1, 2, 1, 1, 4, 10]
def baseStart_420344 : Nat := 118140960795 + 420344 * 2 ^ 59
def prefixEnd_420344 : Nat := 4983230072969 + 3 ^ 40 * 420344 * 2
def baseEnd_420344 : Nat := 10658691962153512882315

theorem tailTrace_420344 : CollatzResearch.WordTrace tailWord_420344 prefixEnd_420344 10658691962153512882315 := by
  unfold tailWord_420344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7665602594586475942446043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10220803459448634589928057 7665602594586475942446043)
  ·
    refine ⟨11498403891879713913669065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7665602594586475942446043 11498403891879713913669065)
    ·
      refine ⟨8623802918909785435251799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11498403891879713913669065 8623802918909785435251799)
      ·
        refine ⟨12935704378364678152877699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8623802918909785435251799 12935704378364678152877699)
        ·
          refine ⟨19403556567547017229316549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12935704378364678152877699 19403556567547017229316549)
          ·
            refine ⟨3638166856415065730496853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19403556567547017229316549 3638166856415065730496853)
            ·
              refine ⟨10658691962153512882315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3638166856415065730496853 10658691962153512882315)
              ·
                rfl

theorem cell21_420344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 10].length) (baseStart_420344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420344 prefixEnd_420344 := by exact prefixLift 420344
  have htrace : WordTrace (prefixWord ++ tailWord_420344) baseStart_420344 baseEnd_420344 := by
    simpa [prefixWord, tailWord_420344, baseEnd_420344] using wordTrace_append hprefix tailTrace_420344
  have hstable : (prefixWord ++ tailWord_420344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420344).length < 2 ^ (prefixWord ++ tailWord_420344).sum := by decide
  have hdescent : baseEnd_420344 < baseStart_420344 := by decide
  rcases family_descends (prefixWord ++ tailWord_420344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420364 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_420364 : Nat := 118140960795 + 420364 * 2 ^ 59
def prefixEnd_420364 : Nat := 4983230072969 + 3 ^ 40 * 420364 * 2
def baseEnd_420364 : Nat := 95932791931866025607461

theorem tailTrace_420364 : CollatzResearch.WordTrace tailWord_420364 prefixEnd_420364 95932791931866025607461 := by
  unfold tailWord_420364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7665967324550247650310073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10221289766066996867080097 7665967324550247650310073)
  ·
    refine ⟨5749475493412685737732555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7665967324550247650310073 5749475493412685737732555)
    ·
      refine ⟨8624213240119028606598833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749475493412685737732555 8624213240119028606598833)
      ·
        refine ⟨6468159930089271454949125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8624213240119028606598833 6468159930089271454949125)
        ·
          refine ⟨1212779986891738397802961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6468159930089271454949125 1212779986891738397802961)
          ·
            refine ⟨909584990168803798352221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212779986891738397802961 909584990168803798352221)
            ·
              refine ⟨341094371313301424382083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 909584990168803798352221 341094371313301424382083)
              ·
                refine ⟨511641556969952136573125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341094371313301424382083 511641556969952136573125)
                ·
                  refine ⟨95932791931866025607461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511641556969952136573125 95932791931866025607461)
                  ·
                    rfl

theorem cell21_420364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_420364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420364 prefixEnd_420364 := by exact prefixLift 420364
  have htrace : WordTrace (prefixWord ++ tailWord_420364) baseStart_420364 baseEnd_420364 := by
    simpa [prefixWord, tailWord_420364, baseEnd_420364] using wordTrace_append hprefix tailTrace_420364
  have hstable : (prefixWord ++ tailWord_420364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420364).length < 2 ^ (prefixWord ++ tailWord_420364).sum := by decide
  have hdescent : baseEnd_420364 < baseStart_420364 := by decide
  rcases family_descends (prefixWord ++ tailWord_420364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420423 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 4]
def baseStart_420423 : Nat := 118140960795 + 420423 * 2 ^ 59
def prefixEnd_420423 : Nat := 4983230072969 + 3 ^ 40 * 420423 * 2
def baseEnd_420423 : Nat := 95946256535695034124007

theorem tailTrace_420423 : CollatzResearch.WordTrace tailWord_420423 prefixEnd_420423 95946256535695034124007 := by
  unfold tailWord_420423
  simp only [CollatzResearch.WordTrace]
  refine ⟨15334086555886748377017923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10222724370591165584678615 15334086555886748377017923)
  ·
    refine ⟨23001129833830122565526885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15334086555886748377017923 23001129833830122565526885)
    ·
      refine ⟨4312711843843147981036291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23001129833830122565526885 4312711843843147981036291)
      ·
        refine ⟨6469067765764721971554437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312711843843147981036291 6469067765764721971554437)
        ·
          refine ⟨1212950206080885369666457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6469067765764721971554437 1212950206080885369666457)
          ·
            refine ⟨909712654560664027249843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212950206080885369666457 909712654560664027249843)
            ·
              refine ⟨1364568981840996040874765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909712654560664027249843 1364568981840996040874765)
              ·
                refine ⟨511713368190373515328037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1364568981840996040874765 511713368190373515328037)
                ·
                  refine ⟨95946256535695034124007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511713368190373515328037 95946256535695034124007)
                  ·
                    rfl

theorem cell21_420423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_420423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420423 prefixEnd_420423 := by exact prefixLift 420423
  have htrace : WordTrace (prefixWord ++ tailWord_420423) baseStart_420423 baseEnd_420423 := by
    simpa [prefixWord, tailWord_420423, baseEnd_420423] using wordTrace_append hprefix tailTrace_420423
  have hstable : (prefixWord ++ tailWord_420423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420423).length < 2 ^ (prefixWord ++ tailWord_420423).sum := by decide
  have hdescent : baseEnd_420423 < baseStart_420423 := by decide
  rcases family_descends (prefixWord ++ tailWord_420423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420513 : List Nat := [1, 2, 3, 3, 3, 1, 8]
def baseStart_420513 : Nat := 118140960795 + 420513 * 2 ^ 59
def prefixEnd_420513 : Nat := 4983230072969 + 3 ^ 40 * 420513 * 2
def baseEnd_420513 : Nat := 10662977306874986402647

theorem tailTrace_420513 : CollatzResearch.WordTrace tailWord_420513 prefixEnd_420513 10662977306874986402647 := by
  unfold tailWord_420513
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337369125560693747794193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10224912750373795831862795 15337369125560693747794193)
  ·
    refine ⟨11503026844170520310845645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15337369125560693747794193 11503026844170520310845645)
    ·
      refine ⟨4313635066563945116567117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11503026844170520310845645 4313635066563945116567117)
      ·
        refine ⟨1617613149961479418712669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4313635066563945116567117 1617613149961479418712669)
        ·
          refine ⟨606604931235554782017251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1617613149961479418712669 606604931235554782017251)
          ·
            refine ⟨909907396853332173025877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606604931235554782017251 909907396853332173025877)
            ·
              refine ⟨10662977306874986402647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 909907396853332173025877 10662977306874986402647)
              ·
                rfl

theorem cell21_420513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 8].length) (baseStart_420513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420513 prefixEnd_420513 := by exact prefixLift 420513
  have htrace : WordTrace (prefixWord ++ tailWord_420513) baseStart_420513 baseEnd_420513 := by
    simpa [prefixWord, tailWord_420513, baseEnd_420513] using wordTrace_append hprefix tailTrace_420513
  have hstable : (prefixWord ++ tailWord_420513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420513).length < 2 ^ (prefixWord ++ tailWord_420513).sum := by decide
  have hdescent : baseEnd_420513 < baseStart_420513 := by decide
  rcases family_descends (prefixWord ++ tailWord_420513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420527 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_420527 : Nat := 118140960795 + 420527 * 2 ^ 59
def prefixEnd_420527 : Nat := 4983230072969 + 3 ^ 40 * 420527 * 2
def baseEnd_420527 : Nat := 95969990752613964390461

theorem tailTrace_420527 : CollatzResearch.WordTrace tailWord_420527 prefixEnd_420527 95969990752613964390461 := by
  unfold tailWord_420527
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337879747509974138803835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10225253165006649425869223 15337879747509974138803835)
  ·
    refine ⟨23006819621264961208205753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15337879747509974138803835 23006819621264961208205753)
    ·
      refine ⟨17255114715948720906154315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23006819621264961208205753 17255114715948720906154315)
      ·
        refine ⟨25882672073923081359231473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17255114715948720906154315 25882672073923081359231473)
        ·
          refine ⟨19412004055442311019423605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25882672073923081359231473 19412004055442311019423605)
          ·
            refine ⟨1819875380197716658070963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19412004055442311019423605 1819875380197716658070963)
            ·
              refine ⟨2729813070296574987106445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819875380197716658070963 2729813070296574987106445)
              ·
                refine ⟨1023679901361215620164917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2729813070296574987106445 1023679901361215620164917)
                ·
                  refine ⟨95969990752613964390461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1023679901361215620164917 95969990752613964390461)
                  ·
                    rfl

theorem cell21_420527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_420527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420527 prefixEnd_420527 := by exact prefixLift 420527
  have htrace : WordTrace (prefixWord ++ tailWord_420527) baseStart_420527 baseEnd_420527 := by
    simpa [prefixWord, tailWord_420527, baseEnd_420527] using wordTrace_append hprefix tailTrace_420527
  have hstable : (prefixWord ++ tailWord_420527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420527).length < 2 ^ (prefixWord ++ tailWord_420527).sum := by decide
  have hdescent : baseEnd_420527 < baseStart_420527 := by decide
  rcases family_descends (prefixWord ++ tailWord_420527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420558 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_420558 : Nat := 118140960795 + 420558 * 2 ^ 59
def prefixEnd_420558 : Nat := 4983230072969 + 3 ^ 40 * 420558 * 2
def baseEnd_420558 : Nat := 95977065374964799373731

theorem tailTrace_420558 : CollatzResearch.WordTrace tailWord_420558 prefixEnd_420558 95977065374964799373731 := by
  unfold tailWord_420558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917376301299708304147791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10226006940265110955454885 1917376301299708304147791)
  ·
    refine ⟨2876064451949562456221687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1917376301299708304147791 2876064451949562456221687)
    ·
      refine ⟨4314096677924343684332531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876064451949562456221687 4314096677924343684332531)
      ·
        refine ⟨6471145016886515526498797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314096677924343684332531 6471145016886515526498797)
        ·
          refine ⟨2426679381332443322437049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6471145016886515526498797 2426679381332443322437049)
          ·
            refine ⟨1820009535999332491827787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426679381332443322437049 1820009535999332491827787)
            ·
              refine ⟨2730014303998998737741681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820009535999332491827787 2730014303998998737741681)
              ·
                refine ⟨2047510727999249053306261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730014303998998737741681 2047510727999249053306261)
                ·
                  refine ⟨95977065374964799373731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2047510727999249053306261 95977065374964799373731)
                  ·
                    rfl

theorem cell21_420558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_420558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420558 prefixEnd_420558 := by exact prefixLift 420558
  have htrace : WordTrace (prefixWord ++ tailWord_420558) baseStart_420558 baseEnd_420558 := by
    simpa [prefixWord, tailWord_420558, baseEnd_420558] using wordTrace_append hprefix tailTrace_420558
  have hstable : (prefixWord ++ tailWord_420558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420558).length < 2 ^ (prefixWord ++ tailWord_420558).sum := by decide
  have hdescent : baseEnd_420558 < baseStart_420558 := by decide
  rcases family_descends (prefixWord ++ tailWord_420558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420589 : List Nat := [1, 5, 1, 2, 1, 1, 4, 6]
def baseStart_420589 : Nat := 118140960795 + 420589 * 2 ^ 59
def prefixEnd_420589 : Nat := 4983230072969 + 3 ^ 40 * 420589 * 2
def baseEnd_420589 : Nat := 31994713332438544785667

theorem tailTrace_420589 : CollatzResearch.WordTrace tailWord_420589 prefixEnd_420589 31994713332438544785667 := by
  unfold tailWord_420589
  simp only [CollatzResearch.WordTrace]
  refine ⟨15340141073285358727560821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10226760715523572485040547 15340141073285358727560821)
  ·
    refine ⟨1438138225620502380708827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15340141073285358727560821 1438138225620502380708827)
    ·
      refine ⟨2157207338430753571063241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438138225620502380708827 2157207338430753571063241)
      ·
        refine ⟨1617905503823065178297431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2157207338430753571063241 1617905503823065178297431)
        ·
          refine ⟨2426858255734597767446147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617905503823065178297431 2426858255734597767446147)
          ·
            refine ⟨3640287383601896651169221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426858255734597767446147 3640287383601896651169221)
            ·
              refine ⟨682553884425355622094229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3640287383601896651169221 682553884425355622094229)
              ·
                refine ⟨31994713332438544785667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 682553884425355622094229 31994713332438544785667)
                ·
                  rfl

theorem cell21_420589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 6].length) (baseStart_420589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420589 prefixEnd_420589 := by exact prefixLift 420589
  have htrace : WordTrace (prefixWord ++ tailWord_420589) baseStart_420589 baseEnd_420589 := by
    simpa [prefixWord, tailWord_420589, baseEnd_420589] using wordTrace_append hprefix tailTrace_420589
  have hstable : (prefixWord ++ tailWord_420589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420589).length < 2 ^ (prefixWord ++ tailWord_420589).sum := by decide
  have hdescent : baseEnd_420589 < baseStart_420589 := by decide
  rcases family_descends (prefixWord ++ tailWord_420589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420617 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_420617 : Nat := 118140960795 + 420617 * 2 ^ 59
def prefixEnd_420617 : Nat := 4983230072969 + 3 ^ 40 * 420617 * 2
def baseEnd_420617 : Nat := 95990529978793807890277

theorem tailTrace_420617 : CollatzResearch.WordTrace tailWord_420617 prefixEnd_420617 95990529978793807890277 := by
  unfold tailWord_420617
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341162317183919509580105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10227441544789279673053403 15341162317183919509580105)
  ·
    refine ⟨11505871737887939632185079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15341162317183919509580105 11505871737887939632185079)
    ·
      refine ⟨17258807606831909448277619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11505871737887939632185079 17258807606831909448277619)
      ·
        refine ⟨25888211410247864172416429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17258807606831909448277619 25888211410247864172416429)
        ·
          refine ⟨9708079278842949064656161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25888211410247864172416429 9708079278842949064656161)
          ·
            refine ⟨7281059459132211798492121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9708079278842949064656161 7281059459132211798492121)
            ·
              refine ⟨5460794594349158848869091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7281059459132211798492121 5460794594349158848869091)
              ·
                refine ⟨8191191891523738273303637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460794594349158848869091 8191191891523738273303637)
                ·
                  refine ⟨95990529978793807890277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8191191891523738273303637 95990529978793807890277)
                  ·
                    rfl

theorem cell21_420617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_420617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420617 prefixEnd_420617 := by exact prefixLift 420617
  have htrace : WordTrace (prefixWord ++ tailWord_420617) baseStart_420617 baseEnd_420617 := by
    simpa [prefixWord, tailWord_420617, baseEnd_420617] using wordTrace_append hprefix tailTrace_420617
  have hstable : (prefixWord ++ tailWord_420617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420617).length < 2 ^ (prefixWord ++ tailWord_420617).sum := by decide
  have hdescent : baseEnd_420617 < baseStart_420617 := by decide
  rcases family_descends (prefixWord ++ tailWord_420617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420620 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_420620 : Nat := 118140960795 + 420620 * 2 ^ 59
def prefixEnd_420620 : Nat := 4983230072969 + 3 ^ 40 * 420620 * 2
def baseEnd_420620 : Nat := 95991214619666469340271

theorem tailTrace_420620 : CollatzResearch.WordTrace tailWord_420620 prefixEnd_420620 95991214619666469340271 := by
  unfold tailWord_420620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670635868086525510969657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10227514490782034014626209 7670635868086525510969657)
  ·
    refine ⟨5752976901064894133227243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7670635868086525510969657 5752976901064894133227243)
    ·
      refine ⟨8629465351597341199840865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752976901064894133227243 8629465351597341199840865)
      ·
        refine ⟨6472099013698005899880649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8629465351597341199840865 6472099013698005899880649)
        ·
          refine ⟨4854074260273504424910487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6472099013698005899880649 4854074260273504424910487)
          ·
            refine ⟨7281111390410256637365731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854074260273504424910487 7281111390410256637365731)
            ·
              refine ⟨10921667085615384956048597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281111390410256637365731 10921667085615384956048597)
              ·
                refine ⟨255976572319110584907389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10921667085615384956048597 255976572319110584907389)
                ·
                  refine ⟨95991214619666469340271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255976572319110584907389 95991214619666469340271)
                  ·
                    rfl

theorem cell21_420620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_420620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420620 prefixEnd_420620 := by exact prefixLift 420620
  have htrace : WordTrace (prefixWord ++ tailWord_420620) baseStart_420620 baseEnd_420620 := by
    simpa [prefixWord, tailWord_420620, baseEnd_420620] using wordTrace_append hprefix tailTrace_420620
  have hstable : (prefixWord ++ tailWord_420620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420620).length < 2 ^ (prefixWord ++ tailWord_420620).sum := by decide
  have hdescent : baseEnd_420620 < baseStart_420620 := by decide
  rcases family_descends (prefixWord ++ tailWord_420620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420685 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 4]
def baseStart_420685 : Nat := 118140960795 + 420685 * 2 ^ 59
def prefixEnd_420685 : Nat := 4983230072969 + 3 ^ 40 * 420685 * 2
def baseEnd_420685 : Nat := 96006048505240800756805

theorem tailTrace_420685 : CollatzResearch.WordTrace tailWord_420685 prefixEnd_420685 96006048505240800756805 := by
  unfold tailWord_420685
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343642480937567123055509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10229094987291711415370339 15343642480937567123055509)
  ·
    refine ⟨719233241293948458893227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15343642480937567123055509 719233241293948458893227)
    ·
      refine ⟨1078849861940922688339841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 719233241293948458893227 1078849861940922688339841)
      ·
        refine ⟨809137396455692016254881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1078849861940922688339841 809137396455692016254881)
        ·
          refine ⟨606853047341769012191161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809137396455692016254881 606853047341769012191161)
          ·
            refine ⟨455139785506326759143371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606853047341769012191161 455139785506326759143371)
            ·
              refine ⟨682709678259490138715057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455139785506326759143371 682709678259490138715057)
              ·
                refine ⟨512032258694617604036293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682709678259490138715057 512032258694617604036293)
                ·
                  refine ⟨96006048505240800756805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512032258694617604036293 96006048505240800756805)
                  ·
                    rfl

theorem cell21_420685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_420685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420685 prefixEnd_420685 := by exact prefixLift 420685
  have htrace : WordTrace (prefixWord ++ tailWord_420685) baseStart_420685 baseEnd_420685 := by
    simpa [prefixWord, tailWord_420685, baseEnd_420685] using wordTrace_append hprefix tailTrace_420685
  have hstable : (prefixWord ++ tailWord_420685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420685).length < 2 ^ (prefixWord ++ tailWord_420685).sum := by decide
  have hdescent : baseEnd_420685 < baseStart_420685 := by decide
  rcases family_descends (prefixWord ++ tailWord_420685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420893 : List Nat := [1, 4, 2, 2, 3, 1, 1, 7]
def baseStart_420893 : Nat := 118140960795 + 420893 * 2 ^ 59
def prefixEnd_420893 : Nat := 4983230072969 + 3 ^ 40 * 420893 * 2
def baseEnd_420893 : Nat := 32017838979692887096571

theorem tailTrace_420893 : CollatzResearch.WordTrace tailWord_420893 prefixEnd_420893 32017838979692887096571 := by
  unfold tailWord_420893
  simp only [CollatzResearch.WordTrace]
  refine ⟨15351228864184018646627333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10234152576122679097751555 15351228864184018646627333)
  ·
    refine ⟨2878355412034503496242625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15351228864184018646627333 2878355412034503496242625)
    ·
      refine ⟨2158766559025877622181969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2878355412034503496242625 2158766559025877622181969)
      ·
        refine ⟨1619074919269408216636477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158766559025877622181969 1619074919269408216636477)
        ·
          refine ⟨607153094726028081238679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1619074919269408216636477 607153094726028081238679)
          ·
            refine ⟨910729642089042121858019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607153094726028081238679 910729642089042121858019)
            ·
              refine ⟨1366094463133563182787029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910729642089042121858019 1366094463133563182787029)
              ·
                refine ⟨32017838979692887096571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1366094463133563182787029 32017838979692887096571)
                ·
                  rfl

theorem cell21_420893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 7].length) (baseStart_420893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420893 prefixEnd_420893 := by exact prefixLift 420893
  have htrace : WordTrace (prefixWord ++ tailWord_420893) baseStart_420893 baseEnd_420893 := by
    simpa [prefixWord, tailWord_420893, baseEnd_420893] using wordTrace_append hprefix tailTrace_420893
  have hstable : (prefixWord ++ tailWord_420893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420893).length < 2 ^ (prefixWord ++ tailWord_420893).sum := by decide
  have hdescent : baseEnd_420893 < baseStart_420893 := by decide
  rcases family_descends (prefixWord ++ tailWord_420893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420924 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_420924 : Nat := 118140960795 + 420924 * 2 ^ 59
def prefixEnd_420924 : Nat := 4983230072969 + 3 ^ 40 * 420924 * 2
def baseEnd_420924 : Nat := 96060591561429496272983

theorem tailTrace_420924 : CollatzResearch.WordTrace tailWord_420924 prefixEnd_420924 96060591561429496272983 := by
  unfold tailWord_420924
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676179763535855470502913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10234906351381140627337217 7676179763535855470502913)
  ·
    refine ⟨5757134822651891602877185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7676179763535855470502913 5757134822651891602877185)
    ·
      refine ⟨4317851116988918702157889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5757134822651891602877185 4317851116988918702157889)
      ·
        refine ⟨3238388337741689026618417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4317851116988918702157889 3238388337741689026618417)
        ·
          refine ⟨2428791253306266769963813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3238388337741689026618417 2428791253306266769963813)
          ·
            refine ⟨455398359994925019368215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2428791253306266769963813 455398359994925019368215)
            ·
              refine ⟨683097539992387529052323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455398359994925019368215 683097539992387529052323)
              ·
                refine ⟨1024646309988581293578485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683097539992387529052323 1024646309988581293578485)
                ·
                  refine ⟨96060591561429496272983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1024646309988581293578485 96060591561429496272983)
                  ·
                    rfl

theorem cell21_420924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_420924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_420924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_420924 prefixEnd_420924 := by exact prefixLift 420924
  have htrace : WordTrace (prefixWord ++ tailWord_420924) baseStart_420924 baseEnd_420924 := by
    simpa [prefixWord, tailWord_420924, baseEnd_420924] using wordTrace_append hprefix tailTrace_420924
  have hstable : (prefixWord ++ tailWord_420924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420924).length < 2 ^ (prefixWord ++ tailWord_420924).sum := by decide
  have hdescent : baseEnd_420924 < baseStart_420924 := by decide
  rcases family_descends (prefixWord ++ tailWord_420924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421000 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_421000 : Nat := 118140960795 + 421000 * 2 ^ 59
def prefixEnd_421000 : Nat := 4983230072969 + 3 ^ 40 * 421000 * 2
def baseEnd_421000 : Nat := 96077935796870253006161

theorem tailTrace_421000 : CollatzResearch.WordTrace tailWord_421000 prefixEnd_421000 96077935796870253006161 := by
  unfold tailWord_421000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677565737398187960386227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10236754316530917280514969 7677565737398187960386227)
  ·
    refine ⟨11516348606097281940579341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677565737398187960386227 11516348606097281940579341)
    ·
      refine ⟨4318630727286480727717253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11516348606097281940579341 4318630727286480727717253)
      ·
        refine ⟨809743261366215136446985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4318630727286480727717253 809743261366215136446985)
        ·
          refine ⟨607307446024661352335239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809743261366215136446985 607307446024661352335239)
          ·
            refine ⟨910961169036992028502859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607307446024661352335239 910961169036992028502859)
            ·
              refine ⟨1366441753555488042754289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910961169036992028502859 1366441753555488042754289)
              ·
                refine ⟨1024831315166616032065717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366441753555488042754289 1024831315166616032065717)
                ·
                  refine ⟨96077935796870253006161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1024831315166616032065717 96077935796870253006161)
                  ·
                    rfl

theorem cell21_421000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_421000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421000 prefixEnd_421000 := by exact prefixLift 421000
  have htrace : WordTrace (prefixWord ++ tailWord_421000) baseStart_421000 baseEnd_421000 := by
    simpa [prefixWord, tailWord_421000, baseEnd_421000] using wordTrace_append hprefix tailTrace_421000
  have hstable : (prefixWord ++ tailWord_421000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421000).length < 2 ^ (prefixWord ++ tailWord_421000).sum := by decide
  have hdescent : baseEnd_421000 < baseStart_421000 := by decide
  rcases family_descends (prefixWord ++ tailWord_421000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421011 : List Nat := [1, 1, 1, 2, 1, 2, 4, 9]
def baseStart_421011 : Nat := 118140960795 + 421011 * 2 ^ 59
def prefixEnd_421011 : Nat := 4983230072969 + 3 ^ 40 * 421011 * 2
def baseEnd_421011 : Nat := 32026815382245559440935

theorem tailTrace_421011 : CollatzResearch.WordTrace tailWord_421011 prefixEnd_421011 32026815382245559440935 := by
  unfold tailWord_421011
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355532677756524799422887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10237021785171016532948591 15355532677756524799422887)
  ·
    refine ⟨23033299016634787199134331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15355532677756524799422887 23033299016634787199134331)
    ·
      refine ⟨34549948524952180798701497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23033299016634787199134331 34549948524952180798701497)
      ·
        refine ⟨25912461393714135599026123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34549948524952180798701497 25912461393714135599026123)
        ·
          refine ⟨38868692090571203398539185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25912461393714135599026123 38868692090571203398539185)
          ·
            refine ⟨29151519067928402548904389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38868692090571203398539185 29151519067928402548904389)
            ·
              refine ⟨5465909825236575477919573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29151519067928402548904389 5465909825236575477919573)
              ·
                refine ⟨32026815382245559440935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5465909825236575477919573 32026815382245559440935)
                ·
                  rfl

theorem cell21_421011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_421011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421011 prefixEnd_421011 := by exact prefixLift 421011
  have htrace : WordTrace (prefixWord ++ tailWord_421011) baseStart_421011 baseEnd_421011 := by
    simpa [prefixWord, tailWord_421011, baseEnd_421011] using wordTrace_append hprefix tailTrace_421011
  have hstable : (prefixWord ++ tailWord_421011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421011).length < 2 ^ (prefixWord ++ tailWord_421011).sum := by decide
  have hdescent : baseEnd_421011 < baseStart_421011 := by decide
  rcases family_descends (prefixWord ++ tailWord_421011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421028 : List Nat := [2, 3, 1, 2, 3, 2, 8]
def baseStart_421028 : Nat := 118140960795 + 421028 * 2 ^ 59
def prefixEnd_421028 : Nat := 4983230072969 + 3 ^ 40 * 421028 * 2
def baseEnd_421028 : Nat := 10676036197594269615493

theorem tailTrace_421028 : CollatzResearch.WordTrace tailWord_421028 prefixEnd_421028 10676036197594269615493 := by
  unfold tailWord_421028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678076359347468351395869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10237435145796624468527825 7678076359347468351395869)
  ·
    refine ⟨2879278634755300631773451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7678076359347468351395869 2879278634755300631773451)
    ·
      refine ⟨4318917952132950947660177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879278634755300631773451 4318917952132950947660177)
      ·
        refine ⟨3239188464099713210745133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4318917952132950947660177 3239188464099713210745133)
        ·
          refine ⟨1214695674037392454029425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3239188464099713210745133 1214695674037392454029425)
          ·
            refine ⟨911021755528044340522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214695674037392454029425 911021755528044340522069)
            ·
              refine ⟨10676036197594269615493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 911021755528044340522069 10676036197594269615493)
              ·
                rfl

theorem cell21_421028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 8].length) (baseStart_421028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421028 prefixEnd_421028 := by exact prefixLift 421028
  have htrace : WordTrace (prefixWord ++ tailWord_421028) baseStart_421028 baseEnd_421028 := by
    simpa [prefixWord, tailWord_421028, baseEnd_421028] using wordTrace_append hprefix tailTrace_421028
  have hstable : (prefixWord ++ tailWord_421028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421028).length < 2 ^ (prefixWord ++ tailWord_421028).sum := by decide
  have hdescent : baseEnd_421028 < baseStart_421028 := by decide
  rcases family_descends (prefixWord ++ tailWord_421028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421031 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 4]
def baseStart_421031 : Nat := 118140960795 + 421031 * 2 ^ 59
def prefixEnd_421031 : Nat := 4983230072969 + 3 ^ 40 * 421031 * 2
def baseEnd_421031 : Nat := 96085010419221087989431

theorem tailTrace_421031 : CollatzResearch.WordTrace tailWord_421031 prefixEnd_421031 96085010419221087989431 := by
  unfold tailWord_421031
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356262137684068215150947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10237508091789378810100631 15356262137684068215150947)
  ·
    refine ⟨23034393206526102322726421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15356262137684068215150947 23034393206526102322726421)
    ·
      refine ⟨1079737181555911046377801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23034393206526102322726421 1079737181555911046377801)
      ·
        refine ⟨809802886166933284783351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1079737181555911046377801 809802886166933284783351)
        ·
          refine ⟨1214704329250399927175027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809802886166933284783351 1214704329250399927175027)
          ·
            refine ⟨1822056493875599890762541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214704329250399927175027 1822056493875599890762541)
            ·
              refine ⟨683271185203349959035953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1822056493875599890762541 683271185203349959035953)
              ·
                refine ⟨512453388902512469276965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683271185203349959035953 512453388902512469276965)
                ·
                  refine ⟨96085010419221087989431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512453388902512469276965 96085010419221087989431)
                  ·
                    rfl

theorem cell21_421031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_421031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421031 prefixEnd_421031 := by exact prefixLift 421031
  have htrace : WordTrace (prefixWord ++ tailWord_421031) baseStart_421031 baseEnd_421031 := by
    simpa [prefixWord, tailWord_421031, baseEnd_421031] using wordTrace_append hprefix tailTrace_421031
  have hstable : (prefixWord ++ tailWord_421031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421031).length < 2 ^ (prefixWord ++ tailWord_421031).sum := by decide
  have hdescent : baseEnd_421031 < baseStart_421031 := by decide
  rcases family_descends (prefixWord ++ tailWord_421031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421087 : List Nat := [1, 1, 2, 3, 2, 1, 11]
def baseStart_421087 : Nat := 118140960795 + 421087 * 2 ^ 59
def prefixEnd_421087 : Nat := 4983230072969 + 3 ^ 40 * 421087 * 2
def baseEnd_421087 : Nat := 10677532264686381672887

theorem tailTrace_421087 : CollatzResearch.WordTrace tailWord_421087 prefixEnd_421087 10677532264686381672887 := by
  unfold tailWord_421087
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358304625481189779189515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10238869750320793186126343 15358304625481189779189515)
  ·
    refine ⟨23037456938221784668784273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15358304625481189779189515 23037456938221784668784273)
    ·
      refine ⟨17278092703666338501588205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23037456938221784668784273 17278092703666338501588205)
      ·
        refine ⟨6479284763874876938095577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17278092703666338501588205 6479284763874876938095577)
        ·
          refine ⟨4859463572906157703571683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479284763874876938095577 4859463572906157703571683)
          ·
            refine ⟨7289195359359236555357525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859463572906157703571683 7289195359359236555357525)
            ·
              refine ⟨10677532264686381672887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7289195359359236555357525 10677532264686381672887)
              ·
                rfl

theorem cell21_421087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 11].length) (baseStart_421087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421087 prefixEnd_421087 := by exact prefixLift 421087
  have htrace : WordTrace (prefixWord ++ tailWord_421087) baseStart_421087 baseEnd_421087 := by
    simpa [prefixWord, tailWord_421087, baseEnd_421087] using wordTrace_append hprefix tailTrace_421087
  have hstable : (prefixWord ++ tailWord_421087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421087).length < 2 ^ (prefixWord ++ tailWord_421087).sum := by decide
  have hdescent : baseEnd_421087 < baseStart_421087 := by decide
  rcases family_descends (prefixWord ++ tailWord_421087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421093 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 5]
def baseStart_421093 : Nat := 118140960795 + 421093 * 2 ^ 59
def prefixEnd_421093 : Nat := 4983230072969 + 3 ^ 40 * 421093 * 2
def baseEnd_421093 : Nat := 96099159663922757955971

theorem tailTrace_421093 : CollatzResearch.WordTrace tailWord_421093 prefixEnd_421093 96099159663922757955971 := by
  unfold tailWord_421093
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358523463459452803907933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10239015642306301869271955 15358523463459452803907933)
  ·
    refine ⟨5759446298797294801465475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15358523463459452803907933 5759446298797294801465475)
    ·
      refine ⟨8639169448195942202198213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759446298797294801465475 8639169448195942202198213)
      ·
        refine ⟨1619844271536739162912165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8639169448195942202198213 1619844271536739162912165)
        ·
          refine ⟨303720800913138593046031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1619844271536739162912165 303720800913138593046031)
          ·
            refine ⟨455581201369707889569047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303720800913138593046031 455581201369707889569047)
            ·
              refine ⟨683371802054561834353571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455581201369707889569047 683371802054561834353571)
              ·
                refine ⟨1025057703081842751530357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683371802054561834353571 1025057703081842751530357)
                ·
                  refine ⟨96099159663922757955971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025057703081842751530357 96099159663922757955971)
                  ·
                    rfl

theorem cell21_421093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_421093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421093 prefixEnd_421093 := by exact prefixLift 421093
  have htrace : WordTrace (prefixWord ++ tailWord_421093) baseStart_421093 baseEnd_421093 := by
    simpa [prefixWord, tailWord_421093, baseEnd_421093] using wordTrace_append hprefix tailTrace_421093
  have hstable : (prefixWord ++ tailWord_421093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421093).length < 2 ^ (prefixWord ++ tailWord_421093).sum := by decide
  have hdescent : baseEnd_421093 < baseStart_421093 := by decide
  rcases family_descends (prefixWord ++ tailWord_421093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421107 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 4]
def baseStart_421107 : Nat := 118140960795 + 421107 * 2 ^ 59
def prefixEnd_421107 : Nat := 4983230072969 + 3 ^ 40 * 421107 * 2
def baseEnd_421107 : Nat := 96102354654661844722609

theorem tailTrace_421107 : CollatzResearch.WordTrace tailWord_421107 prefixEnd_421107 96102354654661844722609 := by
  unfold tailWord_421107
  simp only [CollatzResearch.WordTrace]
  refine ⟨15359034085408733194917575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10239356056939155463278383 15359034085408733194917575)
  ·
    refine ⟨23038551128113099792376363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15359034085408733194917575 23038551128113099792376363)
    ·
      refine ⟨34557826692169649688564545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23038551128113099792376363 34557826692169649688564545)
      ·
        refine ⟨25918370019127237266423409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34557826692169649688564545 25918370019127237266423409)
        ·
          refine ⟨19438777514345427949817557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25918370019127237266423409 19438777514345427949817557)
          ·
            refine ⟨455596347992470967573849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19438777514345427949817557 455596347992470967573849)
            ·
              refine ⟨341697260994353225680387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455596347992470967573849 341697260994353225680387)
              ·
                refine ⟨512545891491529838520581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341697260994353225680387 512545891491529838520581)
                ·
                  refine ⟨96102354654661844722609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512545891491529838520581 96102354654661844722609)
                  ·
                    rfl

theorem cell21_421107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 4].length) (baseStart_421107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421107 prefixEnd_421107 := by exact prefixLift 421107
  have htrace : WordTrace (prefixWord ++ tailWord_421107) baseStart_421107 baseEnd_421107 := by
    simpa [prefixWord, tailWord_421107, baseEnd_421107] using wordTrace_append hprefix tailTrace_421107
  have hstable : (prefixWord ++ tailWord_421107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421107).length < 2 ^ (prefixWord ++ tailWord_421107).sum := by decide
  have hdescent : baseEnd_421107 < baseStart_421107 := by decide
  rcases family_descends (prefixWord ++ tailWord_421107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421138 : List Nat := [3, 2, 4, 2, 2, 8]
def baseStart_421138 : Nat := 118140960795 + 421138 * 2 ^ 59
def prefixEnd_421138 : Nat := 4983230072969 + 3 ^ 40 * 421138 * 2
def baseEnd_421138 : Nat := 3559608491741210359477

theorem tailTrace_421138 : CollatzResearch.WordTrace tailWord_421138 prefixEnd_421138 3559608491741210359477 := by
  unfold tailWord_421138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840041187074106372324017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10240109832197616992864045 3840041187074106372324017)
  ·
    refine ⟨2880030890305579779243013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3840041187074106372324017 2880030890305579779243013)
    ·
      refine ⟨540005791932296208608065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2880030890305579779243013 540005791932296208608065)
      ·
        refine ⟨405004343949222156456049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540005791932296208608065 405004343949222156456049)
        ·
          refine ⟨303753257961916617342037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405004343949222156456049 303753257961916617342037)
          ·
            refine ⟨3559608491741210359477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 303753257961916617342037 3559608491741210359477)
            ·
              rfl

theorem cell21_421138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 8].length) (baseStart_421138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421138 prefixEnd_421138 := by exact prefixLift 421138
  have htrace : WordTrace (prefixWord ++ tailWord_421138) baseStart_421138 baseEnd_421138 := by
    simpa [prefixWord, tailWord_421138, baseEnd_421138] using wordTrace_append hprefix tailTrace_421138
  have hstable : (prefixWord ++ tailWord_421138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421138).length < 2 ^ (prefixWord ++ tailWord_421138).sum := by decide
  have hdescent : baseEnd_421138 < baseStart_421138 := by decide
  rcases family_descends (prefixWord ++ tailWord_421138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421239 : List Nat := [1, 1, 3, 1, 1, 2, 5, 7]
def baseStart_421239 : Nat := 118140960795 + 421239 * 2 ^ 59
def prefixEnd_421239 : Nat := 4983230072969 + 3 ^ 40 * 421239 * 2
def baseEnd_421239 : Nat := 32044159617686316174113

theorem tailTrace_421239 : CollatzResearch.WordTrace tailWord_421239 prefixEnd_421239 32044159617686316174113 := by
  unfold tailWord_421239
  simp only [CollatzResearch.WordTrace]
  refine ⟨15363848520930519738722771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10242565680620346492481847 15363848520930519738722771)
  ·
    refine ⟨23045772781395779608084157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15363848520930519738722771 23045772781395779608084157)
    ·
      refine ⟨8642164793023417353031559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23045772781395779608084157 8642164793023417353031559)
      ·
        refine ⟨12963247189535126029547339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8642164793023417353031559 12963247189535126029547339)
        ·
          refine ⟨19444870784302689044321009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963247189535126029547339 19444870784302689044321009)
          ·
            refine ⟨14583653088227016783240757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19444870784302689044321009 14583653088227016783240757)
            ·
              refine ⟨1367217477021282823428821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14583653088227016783240757 1367217477021282823428821)
              ·
                refine ⟨32044159617686316174113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1367217477021282823428821 32044159617686316174113)
                ·
                  rfl

theorem cell21_421239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_421239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421239 prefixEnd_421239 := by exact prefixLift 421239
  have htrace : WordTrace (prefixWord ++ tailWord_421239) baseStart_421239 baseEnd_421239 := by
    simpa [prefixWord, tailWord_421239, baseEnd_421239] using wordTrace_append hprefix tailTrace_421239
  have hstable : (prefixWord ++ tailWord_421239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421239).length < 2 ^ (prefixWord ++ tailWord_421239).sum := by decide
  have hdescent : baseEnd_421239 < baseStart_421239 := by decide
  rcases family_descends (prefixWord ++ tailWord_421239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421256 : List Nat := [2, 1, 3, 3, 1, 4, 7]
def baseStart_421256 : Nat := 118140960795 + 421256 * 2 ^ 59
def prefixEnd_421256 : Nat := 4983230072969 + 3 ^ 40 * 421256 * 2
def baseEnd_421256 : Nat := 10681817609407855193219

theorem tailTrace_421256 : CollatzResearch.WordTrace tailWord_421256 prefixEnd_421256 10681817609407855193219 := by
  unfold tailWord_421256
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682234280934465821045811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10242979041245954428061081 7682234280934465821045811)
  ·
    refine ⟨11523351421401698731568717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682234280934465821045811 11523351421401698731568717)
    ·
      refine ⟨4321256783025637024338269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11523351421401698731568717 4321256783025637024338269)
      ·
        refine ⟨1620471293634613884126851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4321256783025637024338269 1620471293634613884126851)
        ·
          refine ⟨2430706940451920826190277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620471293634613884126851 2430706940451920826190277)
          ·
            refine ⟨455757551334735154910677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2430706940451920826190277 455757551334735154910677)
            ·
              refine ⟨10681817609407855193219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 455757551334735154910677 10681817609407855193219)
              ·
                rfl

theorem cell21_421256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 7].length) (baseStart_421256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421256 prefixEnd_421256 := by exact prefixLift 421256
  have htrace : WordTrace (prefixWord ++ tailWord_421256) baseStart_421256 baseEnd_421256 := by
    simpa [prefixWord, tailWord_421256, baseEnd_421256] using wordTrace_append hprefix tailTrace_421256
  have hstable : (prefixWord ++ tailWord_421256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421256).length < 2 ^ (prefixWord ++ tailWord_421256).sum := by decide
  have hdescent : baseEnd_421256 < baseStart_421256 := by decide
  rcases family_descends (prefixWord ++ tailWord_421256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421262 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_421262 : Nat := 118140960795 + 421262 * 2 ^ 59
def prefixEnd_421262 : Nat := 4983230072969 + 3 ^ 40 * 421262 * 2
def baseEnd_421262 : Nat := 96137727766416019638959

theorem tailTrace_421262 : CollatzResearch.WordTrace tailWord_421262 prefixEnd_421262 96137727766416019638959 := by
  unfold tailWord_421262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920585924980899333351255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10243124933231463111206693 1920585924980899333351255)
  ·
    refine ⟨2880878887471349000026883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1920585924980899333351255 2880878887471349000026883)
    ·
      refine ⟨4321318331207023500040325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2880878887471349000026883 4321318331207023500040325)
      ·
        refine ⟨810247187101316906257561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4321318331207023500040325 810247187101316906257561)
        ·
          refine ⟨607685390325987679693171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810247187101316906257561 607685390325987679693171)
          ·
            refine ⟨911528085488981519539757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607685390325987679693171 911528085488981519539757)
            ·
              refine ⟨341823032058368069827409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911528085488981519539757 341823032058368069827409)
              ·
                refine ⟨256367274043776052370557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341823032058368069827409 256367274043776052370557)
                ·
                  refine ⟨96137727766416019638959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256367274043776052370557 96137727766416019638959)
                  ·
                    rfl

theorem cell21_421262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_421262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421262 prefixEnd_421262 := by exact prefixLift 421262
  have htrace : WordTrace (prefixWord ++ tailWord_421262) baseStart_421262 baseEnd_421262 := by
    simpa [prefixWord, tailWord_421262, baseEnd_421262] using wordTrace_append hprefix tailTrace_421262
  have hstable : (prefixWord ++ tailWord_421262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421262).length < 2 ^ (prefixWord ++ tailWord_421262).sum := by decide
  have hdescent : baseEnd_421262 < baseStart_421262 := by decide
  rcases family_descends (prefixWord ++ tailWord_421262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421349 : List Nat := [1, 3, 1, 5, 1, 2, 3, 5]
def baseStart_421349 : Nat := 118140960795 + 421349 * 2 ^ 59
def prefixEnd_421349 : Nat := 4983230072969 + 3 ^ 40 * 421349 * 2
def baseEnd_421349 : Nat := 32052527450574400562927

theorem tailTrace_421349 : CollatzResearch.WordTrace tailWord_421349 prefixEnd_421349 32052527450574400562927 := by
  unfold tailWord_421349
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367860550532008525227101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10245240367021339016818067 15367860550532008525227101)
  ·
    refine ⟨5762947706449503196960163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15367860550532008525227101 5762947706449503196960163)
    ·
      refine ⟨8644421559674254795440245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5762947706449503196960163 8644421559674254795440245)
      ·
        refine ⟨810414521219461387072523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8644421559674254795440245 810414521219461387072523)
        ·
          refine ⟨1215621781829192080608785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810414521219461387072523 1215621781829192080608785)
          ·
            refine ⟨911716336371894060456589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215621781829192080608785 911716336371894060456589)
            ·
              refine ⟨341893626139460272671221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911716336371894060456589 341893626139460272671221)
              ·
                refine ⟨32052527450574400562927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341893626139460272671221 32052527450574400562927)
                ·
                  rfl

theorem cell21_421349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 5].length) (baseStart_421349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421349 prefixEnd_421349 := by exact prefixLift 421349
  have htrace : WordTrace (prefixWord ++ tailWord_421349) baseStart_421349 baseEnd_421349 := by
    simpa [prefixWord, tailWord_421349, baseEnd_421349] using wordTrace_append hprefix tailTrace_421349
  have hstable : (prefixWord ++ tailWord_421349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421349).length < 2 ^ (prefixWord ++ tailWord_421349).sum := by decide
  have hdescent : baseEnd_421349 < baseStart_421349 := by decide
  rcases family_descends (prefixWord ++ tailWord_421349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421380 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_421380 : Nat := 118140960795 + 421380 * 2 ^ 59
def prefixEnd_421380 : Nat := 4983230072969 + 3 ^ 40 * 421380 * 2
def baseEnd_421380 : Nat := 96164656974074036672051

theorem tailTrace_421380 : CollatzResearch.WordTrace tailWord_421380 prefixEnd_421380 96164656974074036672051 := by
  unfold tailWord_421380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684495606709850409802797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10245994142279800546403729 7684495606709850409802797)
  ·
    refine ⟨2881685852516193903676049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7684495606709850409802797 2881685852516193903676049)
    ·
      refine ⟨2161264389387145427757037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2881685852516193903676049 2161264389387145427757037)
      ·
        refine ⟨810474146020179535408889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2161264389387145427757037 810474146020179535408889)
        ·
          refine ⟨607855609515134651556667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810474146020179535408889 607855609515134651556667)
          ·
            refine ⟨911783414272701977335001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607855609515134651556667 911783414272701977335001)
            ·
              refine ⟨683837560704526483001251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911783414272701977335001 683837560704526483001251)
              ·
                refine ⟨1025756341056789724501877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683837560704526483001251 1025756341056789724501877)
                ·
                  refine ⟨96164656974074036672051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025756341056789724501877 96164656974074036672051)
                  ·
                    rfl

theorem cell21_421380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_421380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421380 prefixEnd_421380 := by exact prefixLift 421380
  have htrace : WordTrace (prefixWord ++ tailWord_421380) baseStart_421380 baseEnd_421380 := by
    simpa [prefixWord, tailWord_421380, baseEnd_421380] using wordTrace_append hprefix tailTrace_421380
  have hstable : (prefixWord ++ tailWord_421380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421380).length < 2 ^ (prefixWord ++ tailWord_421380).sum := by decide
  have hdescent : baseEnd_421380 < baseStart_421380 := by decide
  rcases family_descends (prefixWord ++ tailWord_421380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421408 : List Nat := [2, 1, 1, 6, 1, 2, 1, 7]
def baseStart_421408 : Nat := 118140960795 + 421408 * 2 ^ 59
def prefixEnd_421408 : Nat := 4983230072969 + 3 ^ 40 * 421408 * 2
def baseEnd_421408 : Nat := 32057015651850736735109

theorem tailTrace_421408 : CollatzResearch.WordTrace tailWord_421408 prefixEnd_421408 32057015651850736735109 := by
  unfold tailWord_421408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685006228659130800812439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10246674971545507734416585 7685006228659130800812439)
  ·
    refine ⟨11527509342988696201218659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7685006228659130800812439 11527509342988696201218659)
    ·
      refine ⟨17291264014483044301827989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11527509342988696201218659 17291264014483044301827989)
      ·
        refine ⟨810528000678892701648187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17291264014483044301827989 810528000678892701648187)
        ·
          refine ⟨1215792001018339052472281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810528000678892701648187 1215792001018339052472281)
          ·
            refine ⟨911844000763754289354211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215792001018339052472281 911844000763754289354211)
            ·
              refine ⟨1367766001145631434031317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911844000763754289354211 1367766001145631434031317)
              ·
                refine ⟨32057015651850736735109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1367766001145631434031317 32057015651850736735109)
                ·
                  rfl

theorem cell21_421408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_421408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421408 prefixEnd_421408 := by exact prefixLift 421408
  have htrace : WordTrace (prefixWord ++ tailWord_421408) baseStart_421408 baseEnd_421408 := by
    simpa [prefixWord, tailWord_421408, baseEnd_421408] using wordTrace_append hprefix tailTrace_421408
  have hstable : (prefixWord ++ tailWord_421408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421408).length < 2 ^ (prefixWord ++ tailWord_421408).sum := by decide
  have hdescent : baseEnd_421408 < baseStart_421408 := by decide
  rcases family_descends (prefixWord ++ tailWord_421408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421439 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 5]
def baseStart_421439 : Nat := 118140960795 + 421439 * 2 ^ 59
def prefixEnd_421439 : Nat := 4983230072969 + 3 ^ 40 * 421439 * 2
def baseEnd_421439 : Nat := 96178121577903045188597

theorem tailTrace_421439 : CollatzResearch.WordTrace tailWord_421439 prefixEnd_421439 96178121577903045188597 := by
  unfold tailWord_421439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371143120205953896003371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10247428746803969264002247 15371143120205953896003371)
  ·
    refine ⟨23056714680308930844005057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15371143120205953896003371 23056714680308930844005057)
    ·
      refine ⟨17292536010231698133003793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23056714680308930844005057 17292536010231698133003793)
      ·
        refine ⟨12969402007673773599752845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17292536010231698133003793 12969402007673773599752845)
        ·
          refine ⟨4863525752877665099907317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12969402007673773599752845 4863525752877665099907317)
          ·
            refine ⟨455955539332281103116311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4863525752877665099907317 455955539332281103116311)
            ·
              refine ⟨683933308998421654674467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455955539332281103116311 683933308998421654674467)
              ·
                refine ⟨1025899963497632482011701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683933308998421654674467 1025899963497632482011701)
                ·
                  refine ⟨96178121577903045188597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025899963497632482011701 96178121577903045188597)
                  ·
                    rfl

theorem cell21_421439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].length) (baseStart_421439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421439 prefixEnd_421439 := by exact prefixLift 421439
  have htrace : WordTrace (prefixWord ++ tailWord_421439) baseStart_421439 baseEnd_421439 := by
    simpa [prefixWord, tailWord_421439, baseEnd_421439] using wordTrace_append hprefix tailTrace_421439
  have hstable : (prefixWord ++ tailWord_421439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421439).length < 2 ^ (prefixWord ++ tailWord_421439).sum := by decide
  have hdescent : baseEnd_421439 < baseStart_421439 := by decide
  rcases family_descends (prefixWord ++ tailWord_421439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421605 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 4]
def baseStart_421605 : Nat := 118140960795 + 421605 * 2 ^ 59
def prefixEnd_421605 : Nat := 4983230072969 + 3 ^ 40 * 421605 * 2
def baseEnd_421605 : Nat := 96216005039523645421591

theorem tailTrace_421605 : CollatzResearch.WordTrace tailWord_421605 prefixEnd_421605 96216005039523645421591 := by
  unfold tailWord_421605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15377197637604564246546269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10251465091736376164364179 15377197637604564246546269)
  ·
    refine ⟨5766449114101711592454851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15377197637604564246546269 5766449114101711592454851)
    ·
      refine ⟨8649673671152567388682277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766449114101711592454851 8649673671152567388682277)
      ·
        refine ⟨1621813813341106385377927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8649673671152567388682277 1621813813341106385377927)
        ·
          refine ⟨2432720720011659578066891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621813813341106385377927 2432720720011659578066891)
          ·
            refine ⟨3649081080017489367100337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432720720011659578066891 3649081080017489367100337)
            ·
              refine ⟨2736810810013117025325253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3649081080017489367100337 2736810810013117025325253)
              ·
                refine ⟨513152026877459442248485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2736810810013117025325253 513152026877459442248485)
                ·
                  refine ⟨96216005039523645421591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513152026877459442248485 96216005039523645421591)
                  ·
                    rfl

theorem cell21_421605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_421605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421605 prefixEnd_421605 := by exact prefixLift 421605
  have htrace : WordTrace (prefixWord ++ tailWord_421605) baseStart_421605 baseEnd_421605 := by
    simpa [prefixWord, tailWord_421605, baseEnd_421605] using wordTrace_append hprefix tailTrace_421605
  have hstable : (prefixWord ++ tailWord_421605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421605).length < 2 ^ (prefixWord ++ tailWord_421605).sum := by decide
  have hdescent : baseEnd_421605 < baseStart_421605 := by decide
  rcases family_descends (prefixWord ++ tailWord_421605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421622 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_421622 : Nat := 118140960795 + 421622 * 2 ^ 59
def prefixEnd_421622 : Nat := 4983230072969 + 3 ^ 40 * 421622 * 2
def baseEnd_421622 : Nat := 96219884671135393638223

theorem tailTrace_421622 : CollatzResearch.WordTrace tailWord_421622 prefixEnd_421622 96219884671135393638223 := by
  unfold tailWord_421622
  simp only [CollatzResearch.WordTrace]
  refine ⟨961113604908936009369695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10251878452361984099943413 961113604908936009369695)
  ·
    refine ⟨1441670407363404014054543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961113604908936009369695 1441670407363404014054543)
    ·
      refine ⟨2162505611045106021081815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441670407363404014054543 2162505611045106021081815)
      ·
        refine ⟨3243758416567659031622723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162505611045106021081815 3243758416567659031622723)
        ·
          refine ⟨4865637624851488547434085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243758416567659031622723 4865637624851488547434085)
          ·
            refine ⟨912307054659654102643891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4865637624851488547434085 912307054659654102643891)
            ·
              refine ⟨1368460581989481153965837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912307054659654102643891 1368460581989481153965837)
              ·
                refine ⟨513172718246055432737189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368460581989481153965837 513172718246055432737189)
                ·
                  refine ⟨96219884671135393638223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513172718246055432737189 96219884671135393638223)
                  ·
                    rfl

theorem cell21_421622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_421622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421622 prefixEnd_421622 := by exact prefixLift 421622
  have htrace : WordTrace (prefixWord ++ tailWord_421622) baseStart_421622 baseEnd_421622 := by
    simpa [prefixWord, tailWord_421622, baseEnd_421622] using wordTrace_append hprefix tailTrace_421622
  have hstable : (prefixWord ++ tailWord_421622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421622).length < 2 ^ (prefixWord ++ tailWord_421622).sum := by decide
  have hdescent : baseEnd_421622 < baseStart_421622 := by decide
  rcases family_descends (prefixWord ++ tailWord_421622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421681 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 4]
def baseStart_421681 : Nat := 118140960795 + 421681 * 2 ^ 59
def prefixEnd_421681 : Nat := 4983230072969 + 3 ^ 40 * 421681 * 2
def baseEnd_421681 : Nat := 96233349274964402154769

theorem tailTrace_421681 : CollatzResearch.WordTrace tailWord_421681 prefixEnd_421681 96233349274964402154769 := by
  unfold tailWord_421681
  simp only [CollatzResearch.WordTrace]
  refine ⟨15379969585329229226312897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10253313056886152817541931 15379969585329229226312897)
  ·
    refine ⟨11534977188996921919734673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15379969585329229226312897 11534977188996921919734673)
    ·
      refine ⟨8651232891747691439801005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11534977188996921919734673 8651232891747691439801005)
      ·
        refine ⟨3244212334405384289925377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8651232891747691439801005 3244212334405384289925377)
        ·
          refine ⟨2433159250804038217444033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244212334405384289925377 2433159250804038217444033)
          ·
            refine ⟨1824869438103028663083025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433159250804038217444033 1824869438103028663083025)
            ·
              refine ⟨1368652078577271497312269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824869438103028663083025 1368652078577271497312269)
              ·
                refine ⟨513244529466476811492101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368652078577271497312269 513244529466476811492101)
                ·
                  refine ⟨96233349274964402154769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513244529466476811492101 96233349274964402154769)
                  ·
                    rfl

theorem cell21_421681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_421681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421681 prefixEnd_421681 := by exact prefixLift 421681
  have htrace : WordTrace (prefixWord ++ tailWord_421681) baseStart_421681 baseEnd_421681 := by
    simpa [prefixWord, tailWord_421681, baseEnd_421681] using wordTrace_append hprefix tailTrace_421681
  have hstable : (prefixWord ++ tailWord_421681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421681).length < 2 ^ (prefixWord ++ tailWord_421681).sum := by decide
  have hdescent : baseEnd_421681 < baseStart_421681 := by decide
  rcases family_descends (prefixWord ++ tailWord_421681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421788 : List Nat := [2, 2, 3, 3, 1, 2, 2, 6]
def baseStart_421788 : Nat := 118140960795 + 421788 * 2 ^ 59
def prefixEnd_421788 : Nat := 4983230072969 + 3 ^ 40 * 421788 * 2
def baseEnd_421788 : Nat := 32085922710918664623739

theorem tailTrace_421788 : CollatzResearch.WordTrace tailWord_421788 prefixEnd_421788 32085922710918664623739 := by
  unfold tailWord_421788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691936097970793250229009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10255914797294391000305345 7691936097970793250229009)
  ·
    refine ⟨5768952073478094937671757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7691936097970793250229009 5768952073478094937671757)
    ·
      refine ⟨2163357027554285601626909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5768952073478094937671757 2163357027554285601626909)
      ·
        refine ⟨811258885332857100610091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2163357027554285601626909 811258885332857100610091)
        ·
          refine ⟨1216888327999285650915137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811258885332857100610091 1216888327999285650915137)
          ·
            refine ⟨912666245999464238186353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216888327999285650915137 912666245999464238186353)
            ·
              refine ⟨684499684499598178639765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912666245999464238186353 684499684499598178639765)
              ·
                refine ⟨32085922710918664623739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 684499684499598178639765 32085922710918664623739)
                ·
                  rfl

theorem cell21_421788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_421788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421788 prefixEnd_421788 := by exact prefixLift 421788
  have htrace : WordTrace (prefixWord ++ tailWord_421788) baseStart_421788 baseEnd_421788 := by
    simpa [prefixWord, tailWord_421788, baseEnd_421788] using wordTrace_append hprefix tailTrace_421788
  have hstable : (prefixWord ++ tailWord_421788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421788).length < 2 ^ (prefixWord ++ tailWord_421788).sum := by decide
  have hdescent : baseEnd_421788 < baseStart_421788 := by decide
  rcases family_descends (prefixWord ++ tailWord_421788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421791 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 4]
def baseStart_421791 : Nat := 118140960795 + 421791 * 2 ^ 59
def prefixEnd_421791 : Nat := 4983230072969 + 3 ^ 40 * 421791 * 2
def baseEnd_421791 : Nat := 96258452773628655321211

theorem tailTrace_421791 : CollatzResearch.WordTrace tailWord_421791 prefixEnd_421791 96258452773628655321211 := by
  unfold tailWord_421791
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383981614930718012817227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10255987743287145341878151 15383981614930718012817227)
  ·
    refine ⟨23075972422396077019225841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15383981614930718012817227 23075972422396077019225841)
    ·
      refine ⟨17306979316797057764419381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23075972422396077019225841 17306979316797057764419381)
      ·
        refine ⟨1622529310949724165414317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17306979316797057764419381 1622529310949724165414317)
        ·
          refine ⟨608448491606146562030369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1622529310949724165414317 608448491606146562030369)
          ·
            refine ⟨456336368704609921522777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608448491606146562030369 456336368704609921522777)
            ·
              refine ⟨342252276528457441142083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456336368704609921522777 342252276528457441142083)
              ·
                refine ⟨513378414792686161713125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342252276528457441142083 513378414792686161713125)
                ·
                  refine ⟨96258452773628655321211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513378414792686161713125 96258452773628655321211)
                  ·
                    rfl

theorem cell21_421791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 4].length) (baseStart_421791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421791 prefixEnd_421791 := by exact prefixLift 421791
  have htrace : WordTrace (prefixWord ++ tailWord_421791) baseStart_421791 baseEnd_421791 := by
    simpa [prefixWord, tailWord_421791, baseEnd_421791] using wordTrace_append hprefix tailTrace_421791
  have hstable : (prefixWord ++ tailWord_421791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421791).length < 2 ^ (prefixWord ++ tailWord_421791).sum := by decide
  have hdescent : baseEnd_421791 < baseStart_421791 := by decide
  rcases family_descends (prefixWord ++ tailWord_421791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421836 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_421836 : Nat := 118140960795 + 421836 * 2 ^ 59
def prefixEnd_421836 : Nat := 4983230072969 + 3 ^ 40 * 421836 * 2
def baseEnd_421836 : Nat := 96268722386718577071119

theorem tailTrace_421836 : CollatzResearch.WordTrace tailWord_421836 prefixEnd_421836 96268722386718577071119 := by
  unfold tailWord_421836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692811449883845349102681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10257081933178460465470241 7692811449883845349102681)
  ·
    refine ⟨5769608587412884011827011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7692811449883845349102681 5769608587412884011827011)
    ·
      refine ⟨8654412881119326017740517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5769608587412884011827011 8654412881119326017740517)
      ·
        refine ⟨1622702415209873628326347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8654412881119326017740517 1622702415209873628326347)
        ·
          refine ⟨2434053622814810442489521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622702415209873628326347 2434053622814810442489521)
          ·
            refine ⟨1825540217111107831867141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434053622814810442489521 1825540217111107831867141)
            ·
              refine ⟨342288790708332718475089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1825540217111107831867141 342288790708332718475089)
              ·
                refine ⟨256716593031249538856317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342288790708332718475089 256716593031249538856317)
                ·
                  refine ⟨96268722386718577071119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256716593031249538856317 96268722386718577071119)
                  ·
                    rfl

theorem cell21_421836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_421836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421836 prefixEnd_421836 := by exact prefixLift 421836
  have htrace : WordTrace (prefixWord ++ tailWord_421836) baseStart_421836 baseEnd_421836 := by
    simpa [prefixWord, tailWord_421836, baseEnd_421836] using wordTrace_append hprefix tailTrace_421836
  have hstable : (prefixWord ++ tailWord_421836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421836).length < 2 ^ (prefixWord ++ tailWord_421836).sum := by decide
  have hdescent : baseEnd_421836 < baseStart_421836 := by decide
  rcases family_descends (prefixWord ++ tailWord_421836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421895 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 3]
def baseStart_421895 : Nat := 118140960795 + 421895 * 2 ^ 59
def prefixEnd_421895 : Nat := 4983230072969 + 3 ^ 40 * 421895 * 2
def baseEnd_421895 : Nat := 96282186990547585587665

theorem tailTrace_421895 : CollatzResearch.WordTrace tailWord_421895 prefixEnd_421895 96282186990547585587665 := by
  unfold tailWord_421895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15387774806553943774603139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10258516537702629183068759 15387774806553943774603139)
  ·
    refine ⟨23081662209830915661904709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15387774806553943774603139 23081662209830915661904709)
    ·
      refine ⟨4327811664343296686607133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23081662209830915661904709 4327811664343296686607133)
      ·
        refine ⟨1622929374128736257477675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4327811664343296686607133 1622929374128736257477675)
        ·
          refine ⟨2434394061193104386216513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622929374128736257477675 2434394061193104386216513)
          ·
            refine ⟨1825795545894828289662385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434394061193104386216513 1825795545894828289662385)
            ·
              refine ⟨1369346659421121217246789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825795545894828289662385 1369346659421121217246789)
              ·
                refine ⟨256752498641460228233773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1369346659421121217246789 256752498641460228233773)
                ·
                  refine ⟨96282186990547585587665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256752498641460228233773 96282186990547585587665)
                  ·
                    rfl

theorem cell21_421895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 3].length) (baseStart_421895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421895 prefixEnd_421895 := by exact prefixLift 421895
  have htrace : WordTrace (prefixWord ++ tailWord_421895) baseStart_421895 baseEnd_421895 := by
    simpa [prefixWord, tailWord_421895, baseEnd_421895] using wordTrace_append hprefix tailTrace_421895
  have hstable : (prefixWord ++ tailWord_421895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421895).length < 2 ^ (prefixWord ++ tailWord_421895).sum := by decide
  have hdescent : baseEnd_421895 < baseStart_421895 := by decide
  rcases family_descends (prefixWord ++ tailWord_421895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421901 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 4]
def baseStart_421901 : Nat := 118140960795 + 421901 * 2 ^ 59
def prefixEnd_421901 : Nat := 4983230072969 + 3 ^ 40 * 421901 * 2
def baseEnd_421901 : Nat := 96283556272292908487653

theorem tailTrace_421901 : CollatzResearch.WordTrace tailWord_421901 prefixEnd_421901 96283556272292908487653 := by
  unfold tailWord_421901
  simp only [CollatzResearch.WordTrace]
  refine ⟨15387993644532206799321557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10258662429688137866214371 15387993644532206799321557)
  ·
    refine ⟨360656101043723596859099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15387993644532206799321557 360656101043723596859099)
    ·
      refine ⟨540984151565585395288649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360656101043723596859099 540984151565585395288649)
      ·
        refine ⟨405738113674189046466487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540984151565585395288649 405738113674189046466487)
        ·
          refine ⟨608607170511283569699731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405738113674189046466487 608607170511283569699731)
          ·
            refine ⟨912910755766925354549597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608607170511283569699731 912910755766925354549597)
            ·
              refine ⟨342341533412597007956099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 912910755766925354549597 342341533412597007956099)
              ·
                refine ⟨513512300118895511934149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342341533412597007956099 513512300118895511934149)
                ·
                  refine ⟨96283556272292908487653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513512300118895511934149 96283556272292908487653)
                  ·
                    rfl

theorem cell21_421901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_421901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_421901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_421901 prefixEnd_421901 := by exact prefixLift 421901
  have htrace : WordTrace (prefixWord ++ tailWord_421901) baseStart_421901 baseEnd_421901 := by
    simpa [prefixWord, tailWord_421901, baseEnd_421901] using wordTrace_append hprefix tailTrace_421901
  have hstable : (prefixWord ++ tailWord_421901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421901).length < 2 ^ (prefixWord ++ tailWord_421901).sum := by decide
  have hdescent : baseEnd_421901 < baseStart_421901 := by decide
  rcases family_descends (prefixWord ++ tailWord_421901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422027 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_422027 : Nat := 118140960795 + 422027 * 2 ^ 59
def prefixEnd_422027 : Nat := 4983230072969 + 3 ^ 40 * 422027 * 2
def baseEnd_422027 : Nat := 96312311188944689387395

theorem tailTrace_422027 : CollatzResearch.WordTrace tailWord_422027 prefixEnd_422027 96312311188944689387395 := by
  unfold tailWord_422027
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392589242075730318408335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10261726161383820212272223 15392589242075730318408335)
  ·
    refine ⟨23088883863113595477612503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15392589242075730318408335 23088883863113595477612503)
    ·
      refine ⟨34633325794670393216418755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23088883863113595477612503 34633325794670393216418755)
      ·
        refine ⟨51949988692005589824628133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34633325794670393216418755 51949988692005589824628133)
        ·
          refine ⟨9740622879751048092117775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51949988692005589824628133 9740622879751048092117775)
          ·
            refine ⟨14610934319626572138176663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740622879751048092117775 14610934319626572138176663)
            ·
              refine ⟨21916401479439858207264995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14610934319626572138176663 21916401479439858207264995)
              ·
                refine ⟨32874602219159787310897493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21916401479439858207264995 32874602219159787310897493)
                ·
                  refine ⟨96312311188944689387395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32874602219159787310897493 96312311188944689387395)
                  ·
                    rfl

theorem cell21_422027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_422027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422027 prefixEnd_422027 := by exact prefixLift 422027
  have htrace : WordTrace (prefixWord ++ tailWord_422027) baseStart_422027 baseEnd_422027 := by
    simpa [prefixWord, tailWord_422027, baseEnd_422027] using wordTrace_append hprefix tailTrace_422027
  have hstable : (prefixWord ++ tailWord_422027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422027).length < 2 ^ (prefixWord ++ tailWord_422027).sum := by decide
  have hdescent : baseEnd_422027 < baseStart_422027 := by decide
  rcases family_descends (prefixWord ++ tailWord_422027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422044 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_422044 : Nat := 118140960795 + 422044 * 2 ^ 59
def prefixEnd_422044 : Nat := 4983230072969 + 3 ^ 40 * 422044 * 2
def baseEnd_422044 : Nat := 96316190820556437604027

theorem tailTrace_422044 : CollatzResearch.WordTrace tailWord_422044 prefixEnd_422044 96316190820556437604027 := by
  unfold tailWord_422044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696604641507071110888593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10262139522009428147851457 7696604641507071110888593)
  ·
    refine ⟨5772453481130303333166445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7696604641507071110888593 5772453481130303333166445)
    ·
      refine ⟨2164670055423863749937417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5772453481130303333166445 2164670055423863749937417)
      ·
        refine ⟨1623502541567897812453063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2164670055423863749937417 1623502541567897812453063)
        ·
          refine ⟨2435253812351846718679595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623502541567897812453063 2435253812351846718679595)
          ·
            refine ⟨3652880718527770078019393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435253812351846718679595 3652880718527770078019393)
            ·
              refine ⟨2739660538895827558514545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652880718527770078019393 2739660538895827558514545)
              ·
                refine ⟨2054745404171870668885909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739660538895827558514545 2054745404171870668885909)
                ·
                  refine ⟨96316190820556437604027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2054745404171870668885909 96316190820556437604027)
                  ·
                    rfl

theorem cell21_422044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_422044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422044 prefixEnd_422044 := by exact prefixLift 422044
  have htrace : WordTrace (prefixWord ++ tailWord_422044) baseStart_422044 baseEnd_422044 := by
    simpa [prefixWord, tailWord_422044, baseEnd_422044] using wordTrace_append hprefix tailTrace_422044
  have hstable : (prefixWord ++ tailWord_422044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422044).length < 2 ^ (prefixWord ++ tailWord_422044).sum := by decide
  have hdescent : baseEnd_422044 < baseStart_422044 := by decide
  rcases family_descends (prefixWord ++ tailWord_422044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422047 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 3]
def baseStart_422047 : Nat := 118140960795 + 422047 * 2 ^ 59
def prefixEnd_422047 : Nat := 4983230072969 + 3 ^ 40 * 422047 * 2
def baseEnd_422047 : Nat := 96316875461429099054021

theorem tailTrace_422047 : CollatzResearch.WordTrace tailWord_422047 prefixEnd_422047 96316875461429099054021 := by
  unfold tailWord_422047
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393318702003273734136395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10262212468002182489424263 15393318702003273734136395)
  ·
    refine ⟨23089978053004910601204593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15393318702003273734136395 23089978053004910601204593)
    ·
      refine ⟨17317483539753682950903445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23089978053004910601204593 17317483539753682950903445)
      ·
        refine ⟨811757040925953888323599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17317483539753682950903445 811757040925953888323599)
        ·
          refine ⟨1217635561388930832485399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811757040925953888323599 1217635561388930832485399)
          ·
            refine ⟨1826453342083396248728099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217635561388930832485399 1826453342083396248728099)
            ·
              refine ⟨2739680013125094373092149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826453342083396248728099 2739680013125094373092149)
              ·
                refine ⟨256845001230477597477389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2739680013125094373092149 256845001230477597477389)
                ·
                  refine ⟨96316875461429099054021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256845001230477597477389 96316875461429099054021)
                  ·
                    rfl

theorem cell21_422047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 3].length) (baseStart_422047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422047 prefixEnd_422047 := by exact prefixLift 422047
  have htrace : WordTrace (prefixWord ++ tailWord_422047) baseStart_422047 baseEnd_422047 := by
    simpa [prefixWord, tailWord_422047, baseEnd_422047] using wordTrace_append hprefix tailTrace_422047
  have hstable : (prefixWord ++ tailWord_422047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422047).length < 2 ^ (prefixWord ++ tailWord_422047).sum := by decide
  have hdescent : baseEnd_422047 < baseStart_422047 := by decide
  rcases family_descends (prefixWord ++ tailWord_422047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422061 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 6]
def baseStart_422061 : Nat := 118140960795 + 422061 * 2 ^ 59
def prefixEnd_422061 : Nat := 4983230072969 + 3 ^ 40 * 422061 * 2
def baseEnd_422061 : Nat := 96320070452168185820659

theorem tailTrace_422061 : CollatzResearch.WordTrace tailWord_422061 prefixEnd_422061 96320070452168185820659 := by
  unfold tailWord_422061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393829323952554125146037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10262552882635036083430691 15393829323952554125146037)
  ·
    refine ⟨1443171499120551949232441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15393829323952554125146037 1443171499120551949232441)
    ·
      refine ⟨1082378624340413961924331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1443171499120551949232441 1082378624340413961924331)
      ·
        refine ⟨1623567936510620942886497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082378624340413961924331 1623567936510620942886497)
        ·
          refine ⟨1217675952382965707164873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1623567936510620942886497 1217675952382965707164873)
          ·
            refine ⟨913256964287224280373655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217675952382965707164873 913256964287224280373655)
            ·
              refine ⟨1369885446430836420560483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913256964287224280373655 1369885446430836420560483)
              ·
                refine ⟨2054828169646254630840725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369885446430836420560483 2054828169646254630840725)
                ·
                  refine ⟨96320070452168185820659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2054828169646254630840725 96320070452168185820659)
                  ·
                    rfl

theorem cell21_422061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_422061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422061 prefixEnd_422061 := by exact prefixLift 422061
  have htrace : WordTrace (prefixWord ++ tailWord_422061) baseStart_422061 baseEnd_422061 := by
    simpa [prefixWord, tailWord_422061, baseEnd_422061] using wordTrace_append hprefix tailTrace_422061
  have hstable : (prefixWord ++ tailWord_422061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422061).length < 2 ^ (prefixWord ++ tailWord_422061).sum := by decide
  have hdescent : baseEnd_422061 < baseStart_422061 := by decide
  rcases family_descends (prefixWord ++ tailWord_422061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422092 : List Nat := [2, 2, 1, 6, 1, 1, 1, 7]
def baseStart_422092 : Nat := 118140960795 + 422092 * 2 ^ 59
def prefixEnd_422092 : Nat := 4983230072969 + 3 ^ 40 * 422092 * 2
def baseEnd_422092 : Nat := 32109048358173006934643

theorem tailTrace_422092 : CollatzResearch.WordTrace tailWord_422092 prefixEnd_422092 32109048358173006934643 := by
  unfold tailWord_422092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697479993420123209762265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10263306657893497613016353 7697479993420123209762265)
  ·
    refine ⟨5773109995065092407321699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7697479993420123209762265 5773109995065092407321699)
    ·
      refine ⟨8659664992597638610982549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5773109995065092407321699 8659664992597638610982549)
      ·
        refine ⟨405921796528014309889807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8659664992597638610982549 405921796528014309889807)
        ·
          refine ⟨608882694792021464834711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405921796528014309889807 608882694792021464834711)
          ·
            refine ⟨913324042188032197252067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608882694792021464834711 913324042188032197252067)
            ·
              refine ⟨1369986063282048295878101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913324042188032197252067 1369986063282048295878101)
              ·
                refine ⟨32109048358173006934643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1369986063282048295878101 32109048358173006934643)
                ·
                  rfl

theorem cell21_422092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_422092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422092 prefixEnd_422092 := by exact prefixLift 422092
  have htrace : WordTrace (prefixWord ++ tailWord_422092) baseStart_422092 baseEnd_422092 := by
    simpa [prefixWord, tailWord_422092, baseEnd_422092] using wordTrace_append hprefix tailTrace_422092
  have hstable : (prefixWord ++ tailWord_422092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422092).length < 2 ^ (prefixWord ++ tailWord_422092).sum := by decide
  have hdescent : baseEnd_422092 < baseStart_422092 := by decide
  rcases family_descends (prefixWord ++ tailWord_422092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422120 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_422120 : Nat := 118140960795 + 422120 * 2 ^ 59
def prefixEnd_422120 : Nat := 4983230072969 + 3 ^ 40 * 422120 * 2
def baseEnd_422120 : Nat := 96333535055997194337205

theorem tailTrace_422120 : CollatzResearch.WordTrace tailWord_422120 prefixEnd_422120 96333535055997194337205 := by
  unfold tailWord_422120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697990615369403600771907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10263987487159204801029209 7697990615369403600771907)
  ·
    refine ⟨11546985923054105401157861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7697990615369403600771907 11546985923054105401157861)
    ·
      refine ⟨2165059860572644762717099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11546985923054105401157861 2165059860572644762717099)
      ·
        refine ⟨3247589790858967144075649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165059860572644762717099 3247589790858967144075649)
        ·
          refine ⟨2435692343144225358056737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3247589790858967144075649 2435692343144225358056737)
          ·
            refine ⟨1826769257358169018542553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435692343144225358056737 1826769257358169018542553)
            ·
              refine ⟨1370076943018626763906915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826769257358169018542553 1370076943018626763906915)
              ·
                refine ⟨2055115414527940145860373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370076943018626763906915 2055115414527940145860373)
                ·
                  refine ⟨96333535055997194337205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2055115414527940145860373 96333535055997194337205)
                  ·
                    rfl

theorem cell21_422120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_422120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422120 prefixEnd_422120 := by exact prefixLift 422120
  have htrace : WordTrace (prefixWord ++ tailWord_422120) baseStart_422120 baseEnd_422120 := by
    simpa [prefixWord, tailWord_422120, baseEnd_422120] using wordTrace_append hprefix tailTrace_422120
  have hstable : (prefixWord ++ tailWord_422120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422120).length < 2 ^ (prefixWord ++ tailWord_422120).sum := by decide
  have hdescent : baseEnd_422120 < baseStart_422120 := by decide
  rcases family_descends (prefixWord ++ tailWord_422120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422123 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 3]
def baseStart_422123 : Nat := 118140960795 + 422123 * 2 ^ 59
def prefixEnd_422123 : Nat := 4983230072969 + 3 ^ 40 * 422123 * 2
def baseEnd_422123 : Nat := 96334219696869855787199

theorem tailTrace_422123 : CollatzResearch.WordTrace tailWord_422123 prefixEnd_422123 96334219696869855787199 := by
  unfold tailWord_422123
  simp only [CollatzResearch.WordTrace]
  refine ⟨15396090649727938713903023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10264060433151959142602015 15396090649727938713903023)
  ·
    refine ⟨23094135974591908070854535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15396090649727938713903023 23094135974591908070854535)
    ·
      refine ⟨34641203961887862106281803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23094135974591908070854535 34641203961887862106281803)
      ·
        refine ⟨51961805942831793159422705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34641203961887862106281803 51961805942831793159422705)
        ·
          refine ⟨38971354457123844869567029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51961805942831793159422705 38971354457123844869567029)
          ·
            refine ⟨3653564480355360456521909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38971354457123844869567029 3653564480355360456521909)
            ·
              refine ⟨342521670033315042798929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3653564480355360456521909 342521670033315042798929)
              ·
                refine ⟨256891252524986282099197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342521670033315042798929 256891252524986282099197)
                ·
                  refine ⟨96334219696869855787199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256891252524986282099197 96334219696869855787199)
                  ·
                    rfl

theorem cell21_422123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 3].length) (baseStart_422123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422123 prefixEnd_422123 := by exact prefixLift 422123
  have htrace : WordTrace (prefixWord ++ tailWord_422123) baseStart_422123 baseEnd_422123 := by
    simpa [prefixWord, tailWord_422123, baseEnd_422123] using wordTrace_append hprefix tailTrace_422123
  have hstable : (prefixWord ++ tailWord_422123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422123).length < 2 ^ (prefixWord ++ tailWord_422123).sum := by decide
  have hdescent : baseEnd_422123 < baseStart_422123 := by decide
  rcases family_descends (prefixWord ++ tailWord_422123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422174 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_422174 : Nat := 118140960795 + 422174 * 2 ^ 59
def prefixEnd_422174 : Nat := 4983230072969 + 3 ^ 40 * 422174 * 2
def baseEnd_422174 : Nat := 96345858591705100437095

theorem tailTrace_422174 : CollatzResearch.WordTrace tailWord_422174 prefixEnd_422174 96345858591705100437095 := by
  unfold tailWord_422174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1924743846567896803001197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10265300515028782949339717 1924743846567896803001197)
  ·
    refine ⟨721778942462961301125449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1924743846567896803001197 721778942462961301125449)
    ·
      refine ⟨541334206847220975844087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 721778942462961301125449 541334206847220975844087)
      ·
        refine ⟨812001310270831463766131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541334206847220975844087 812001310270831463766131)
        ·
          refine ⟨1218001965406247195649197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812001310270831463766131 1218001965406247195649197)
          ·
            refine ⟨456750737027342698368449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218001965406247195649197 456750737027342698368449)
            ·
              refine ⟨342563052770507023776337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456750737027342698368449 342563052770507023776337)
              ·
                refine ⟨256922289577880267832253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342563052770507023776337 256922289577880267832253)
                ·
                  refine ⟨96345858591705100437095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256922289577880267832253 96345858591705100437095)
                  ·
                    rfl

theorem cell21_422174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_422174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422174 prefixEnd_422174 := by exact prefixLift 422174
  have htrace : WordTrace (prefixWord ++ tailWord_422174) baseStart_422174 baseEnd_422174 := by
    simpa [prefixWord, tailWord_422174, baseEnd_422174] using wordTrace_append hprefix tailTrace_422174
  have hstable : (prefixWord ++ tailWord_422174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422174).length < 2 ^ (prefixWord ++ tailWord_422174).sum := by decide
  have hdescent : baseEnd_422174 < baseStart_422174 := by decide
  rcases family_descends (prefixWord ++ tailWord_422174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422292 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_422292 : Nat := 118140960795 + 422292 * 2 ^ 59
def prefixEnd_422292 : Nat := 4983230072969 + 3 ^ 40 * 422292 * 2
def baseEnd_422292 : Nat := 96372787799363117470187

theorem tailTrace_422292 : CollatzResearch.WordTrace tailWord_422292 prefixEnd_422292 96372787799363117470187 := by
  unfold tailWord_422292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701127293057840288402565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10268169724077120384536753 7701127293057840288402565)
  ·
    refine ⟨1443961367448345054075481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7701127293057840288402565 1443961367448345054075481)
    ·
      refine ⟨1082971025586258790556611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1443961367448345054075481 1082971025586258790556611)
      ·
        refine ⟨1624456538379388185834917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082971025586258790556611 1624456538379388185834917)
        ·
          refine ⟨304585600946135284844047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1624456538379388185834917 304585600946135284844047)
          ·
            refine ⟨456878401419202927266071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304585600946135284844047 456878401419202927266071)
            ·
              refine ⟨685317602128804390899107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456878401419202927266071 685317602128804390899107)
              ·
                refine ⟨1027976403193206586348661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685317602128804390899107 1027976403193206586348661)
                ·
                  refine ⟨96372787799363117470187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1027976403193206586348661 96372787799363117470187)
                  ·
                    rfl

theorem cell21_422292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_422292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422292 prefixEnd_422292 := by exact prefixLift 422292
  have htrace : WordTrace (prefixWord ++ tailWord_422292) baseStart_422292 baseEnd_422292 := by
    simpa [prefixWord, tailWord_422292, baseEnd_422292] using wordTrace_append hprefix tailTrace_422292
  have hstable : (prefixWord ++ tailWord_422292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422292).length < 2 ^ (prefixWord ++ tailWord_422292).sum := by decide
  have hdescent : baseEnd_422292 < baseStart_422292 := by decide
  rcases family_descends (prefixWord ++ tailWord_422292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422337 : List Nat := [1, 2, 7, 1, 2, 8]
def baseStart_422337 : Nat := 118140960795 + 422337 * 2 ^ 59
def prefixEnd_422337 : Nat := 4983230072969 + 3 ^ 40 * 422337 * 2
def baseEnd_422337 : Nat := 3569742867127890341485

theorem tailTrace_422337 : CollatzResearch.WordTrace tailWord_422337 prefixEnd_422337 3569742867127890341485 := by
  unfold tailWord_422337
  simp only [CollatzResearch.WordTrace]
  refine ⟨15403895870952653262193265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10269263913968435508128843 15403895870952653262193265)
  ·
    refine ⟨11552921903214489946644949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15403895870952653262193265 11552921903214489946644949)
    ·
      refine ⟨270771607106589608124491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11552921903214489946644949 270771607106589608124491)
      ·
        refine ⟨406157410659884412186737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270771607106589608124491 406157410659884412186737)
        ·
          refine ⟨304618057994913309140053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406157410659884412186737 304618057994913309140053)
          ·
            refine ⟨3569742867127890341485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 304618057994913309140053 3569742867127890341485)
            ·
              rfl

theorem cell21_422337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 8].length) (baseStart_422337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422337 prefixEnd_422337 := by exact prefixLift 422337
  have htrace : WordTrace (prefixWord ++ tailWord_422337) baseStart_422337 baseEnd_422337 := by
    simpa [prefixWord, tailWord_422337, baseEnd_422337] using wordTrace_append hprefix tailTrace_422337
  have hstable : (prefixWord ++ tailWord_422337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422337).length < 2 ^ (prefixWord ++ tailWord_422337).sum := by decide
  have hdescent : baseEnd_422337 < baseStart_422337 := by decide
  rcases family_descends (prefixWord ++ tailWord_422337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422410 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_422410 : Nat := 118140960795 + 422410 * 2 ^ 59
def prefixEnd_422410 : Nat := 4983230072969 + 3 ^ 40 * 422410 * 2
def baseEnd_422410 : Nat := 96399717007021134503279

theorem tailTrace_422410 : CollatzResearch.WordTrace tailWord_422410 prefixEnd_422410 96399717007021134503279 := by
  unfold tailWord_422410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851639599922046682400171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10271038933125457819733789 3851639599922046682400171)
  ·
    refine ⟨5777459399883070023600257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3851639599922046682400171 5777459399883070023600257)
    ·
      refine ⟨4333094549912302517700193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5777459399883070023600257 4333094549912302517700193)
      ·
        refine ⟨3249820912434226888275145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4333094549912302517700193 3249820912434226888275145)
        ·
          refine ⟨2437365684325670166206359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3249820912434226888275145 2437365684325670166206359)
          ·
            refine ⟨3656048526488505249309539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437365684325670166206359 3656048526488505249309539)
            ·
              refine ⟨5484072789732757873964309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656048526488505249309539 5484072789732757873964309)
              ·
                refine ⟨257065912018723025342077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5484072789732757873964309 257065912018723025342077)
                ·
                  refine ⟨96399717007021134503279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257065912018723025342077 96399717007021134503279)
                  ·
                    rfl

theorem cell21_422410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_422410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422410 prefixEnd_422410 := by exact prefixLift 422410
  have htrace : WordTrace (prefixWord ++ tailWord_422410) baseStart_422410 baseEnd_422410 := by
    simpa [prefixWord, tailWord_422410, baseEnd_422410] using wordTrace_append hprefix tailTrace_422410
  have hstable : (prefixWord ++ tailWord_422410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422410).length < 2 ^ (prefixWord ++ tailWord_422410).sum := by decide
  have hdescent : baseEnd_422410 < baseStart_422410 := by decide
  rcases family_descends (prefixWord ++ tailWord_422410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422469 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 5]
def baseStart_422469 : Nat := 118140960795 + 422469 * 2 ^ 59
def prefixEnd_422469 : Nat := 4983230072969 + 3 ^ 40 * 422469 * 2
def baseEnd_422469 : Nat := 96413181610850143019825

theorem tailTrace_422469 : CollatzResearch.WordTrace tailWord_422469 prefixEnd_422469 96413181610850143019825 := by
  unfold tailWord_422469
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408710306474439805998461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10272473537649626537332307 15408710306474439805998461)
  ·
    refine ⟨5778266364927914927249423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15408710306474439805998461 5778266364927914927249423)
    ·
      refine ⟨8667399547391872390874135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778266364927914927249423 8667399547391872390874135)
      ·
        refine ⟨13001099321087808586311203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667399547391872390874135 13001099321087808586311203)
        ·
          refine ⟨19501648981631712879466805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001099321087808586311203 19501648981631712879466805)
          ·
            refine ⟨1828279592027973082450013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19501648981631712879466805 1828279592027973082450013)
            ·
              refine ⟨685604847010489905918755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1828279592027973082450013 685604847010489905918755)
              ·
                refine ⟨1028407270515734858878133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685604847010489905918755 1028407270515734858878133)
                ·
                  refine ⟨96413181610850143019825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028407270515734858878133 96413181610850143019825)
                  ·
                    rfl

theorem cell21_422469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_422469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422469 prefixEnd_422469 := by exact prefixLift 422469
  have htrace : WordTrace (prefixWord ++ tailWord_422469) baseStart_422469 baseEnd_422469 := by
    simpa [prefixWord, tailWord_422469, baseEnd_422469] using wordTrace_append hprefix tailTrace_422469
  have hstable : (prefixWord ++ tailWord_422469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422469).length < 2 ^ (prefixWord ++ tailWord_422469).sum := by decide
  have hdescent : baseEnd_422469 < baseStart_422469 := by decide
  rcases family_descends (prefixWord ++ tailWord_422469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422514 : List Nat := [3, 2, 1, 2, 4, 9]
def baseStart_422514 : Nat := 118140960795 + 422514 * 2 ^ 59
def prefixEnd_422514 : Nat := 4983230072969 + 3 ^ 40 * 422514 * 2
def baseEnd_422514 : Nat := 3571238934220002398879

theorem tailTrace_422514 : CollatzResearch.WordTrace tailWord_422514 prefixEnd_422514 3571238934220002398879 := by
  unfold tailWord_422514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852587897827853122846649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10273567727540941660924397 3852587897827853122846649)
  ·
    refine ⟨2889440923370889842134987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3852587897827853122846649 2889440923370889842134987)
    ·
      refine ⟨4334161385056334763202481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2889440923370889842134987 4334161385056334763202481)
      ·
        refine ⟨3250621038792251072401861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4334161385056334763202481 3250621038792251072401861)
        ·
          refine ⟨609491444773547076075349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3250621038792251072401861 609491444773547076075349)
          ·
            refine ⟨3571238934220002398879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 609491444773547076075349 3571238934220002398879)
            ·
              rfl

theorem cell21_422514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 9].length) (baseStart_422514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422514 prefixEnd_422514 := by exact prefixLift 422514
  have htrace : WordTrace (prefixWord ++ tailWord_422514) baseStart_422514 baseEnd_422514 := by
    simpa [prefixWord, tailWord_422514, baseEnd_422514] using wordTrace_append hprefix tailTrace_422514
  have hstable : (prefixWord ++ tailWord_422514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422514).length < 2 ^ (prefixWord ++ tailWord_422514).sum := by decide
  have hdescent : baseEnd_422514 < baseStart_422514 := by decide
  rcases family_descends (prefixWord ++ tailWord_422514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422548 : List Nat := [2, 4, 2, 2, 1, 2, 3, 5]
def baseStart_422548 : Nat := 118140960795 + 422548 * 2 ^ 59
def prefixEnd_422548 : Nat := 4983230072969 + 3 ^ 40 * 422548 * 2
def baseEnd_422548 : Nat := 32143736829054520400999

theorem tailTrace_422548 : CollatzResearch.WordTrace tailWord_422548 prefixEnd_422548 32143736829054520400999 := by
  unfold tailWord_422548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7705795836594118149062149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10274394448792157532082865 7705795836594118149062149)
  ·
    refine ⟨1444836719361397152949153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7705795836594118149062149 1444836719361397152949153)
    ·
      refine ⟨1083627539521047864711865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1444836719361397152949153 1083627539521047864711865)
      ·
        refine ⟨812720654640785898533899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083627539521047864711865 812720654640785898533899)
        ·
          refine ⟨1219080981961178847800849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812720654640785898533899 1219080981961178847800849)
          ·
            refine ⟨914310736470884135850637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219080981961178847800849 914310736470884135850637)
            ·
              refine ⟨342866526176581550943989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 914310736470884135850637 342866526176581550943989)
              ·
                refine ⟨32143736829054520400999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342866526176581550943989 32143736829054520400999)
                ·
                  rfl

theorem cell21_422548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_422548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422548 prefixEnd_422548 := by exact prefixLift 422548
  have htrace : WordTrace (prefixWord ++ tailWord_422548) baseStart_422548 baseEnd_422548 := by
    simpa [prefixWord, tailWord_422548, baseEnd_422548] using wordTrace_append hprefix tailTrace_422548
  have hstable : (prefixWord ++ tailWord_422548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422548).length < 2 ^ (prefixWord ++ tailWord_422548).sum := by decide
  have hdescent : baseEnd_422548 < baseStart_422548 := by decide
  rcases family_descends (prefixWord ++ tailWord_422548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422590 : List Nat := [4, 2, 1, 1, 2, 1, 2, 8]
def baseStart_422590 : Nat := 118140960795 + 422590 * 2 ^ 59
def prefixEnd_422590 : Nat := 4983230072969 + 3 ^ 40 * 422590 * 2
def baseEnd_422590 : Nat := 32146931819793607167637

theorem tailTrace_422590 : CollatzResearch.WordTrace tailWord_422590 prefixEnd_422590 32146931819793607167637 := by
  unfold tailWord_422590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926640442379509683894153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10275415692690718314102149 1926640442379509683894153)
  ·
    refine ⟨1444980331784632262920615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1926640442379509683894153 1444980331784632262920615)
    ·
      refine ⟨2167470497676948394380923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444980331784632262920615 2167470497676948394380923)
      ·
        refine ⟨3251205746515422591571385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167470497676948394380923 3251205746515422591571385)
        ·
          refine ⟨2438404309886566943678539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3251205746515422591571385 2438404309886566943678539)
          ·
            refine ⟨3657606464829850415517809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438404309886566943678539 3657606464829850415517809)
            ·
              refine ⟨2743204848622387811638357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657606464829850415517809 2743204848622387811638357)
              ·
                refine ⟨32146931819793607167637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2743204848622387811638357 32146931819793607167637)
                ·
                  rfl

theorem cell21_422590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_422590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422590 prefixEnd_422590 := by exact prefixLift 422590
  have htrace : WordTrace (prefixWord ++ tailWord_422590) baseStart_422590 baseEnd_422590 := by
    simpa [prefixWord, tailWord_422590, baseEnd_422590] using wordTrace_append hprefix tailTrace_422590
  have hstable : (prefixWord ++ tailWord_422590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422590).length < 2 ^ (prefixWord ++ tailWord_422590).sum := by decide
  have hdescent : baseEnd_422590 < baseStart_422590 := by decide
  rcases family_descends (prefixWord ++ tailWord_422590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422613 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 3]
def baseStart_422613 : Nat := 118140960795 + 422613 * 2 ^ 59
def prefixEnd_422613 : Nat := 4983230072969 + 3 ^ 40 * 422613 * 2
def baseEnd_422613 : Nat := 96446044372737892619531

theorem tailTrace_422613 : CollatzResearch.WordTrace tailWord_422613 prefixEnd_422613 96446044372737892619531 := by
  unfold tailWord_422613
  simp only [CollatzResearch.WordTrace]
  refine ⟨15413962417952752399240493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10275974945301834932826995 15413962417952752399240493)
  ·
    refine ⟨5780235906732282149715185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15413962417952752399240493 5780235906732282149715185)
    ·
      refine ⟨4335176930049211612286389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5780235906732282149715185 4335176930049211612286389)
      ·
        refine ⟨406422837192113588651849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4335176930049211612286389 406422837192113588651849)
        ·
          refine ⟨304817127894085191488887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406422837192113588651849 304817127894085191488887)
          ·
            refine ⟨457225691841127787233331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304817127894085191488887 457225691841127787233331)
            ·
              refine ⟨685838537761691680849997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457225691841127787233331 685838537761691680849997)
              ·
                refine ⟨257189451660634380318749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685838537761691680849997 257189451660634380318749)
                ·
                  refine ⟨96446044372737892619531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257189451660634380318749 96446044372737892619531)
                  ·
                    rfl

theorem cell21_422613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_422613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422613 prefixEnd_422613 := by exact prefixLift 422613
  have htrace : WordTrace (prefixWord ++ tailWord_422613) baseStart_422613 baseEnd_422613 := by
    simpa [prefixWord, tailWord_422613, baseEnd_422613] using wordTrace_append hprefix tailTrace_422613
  have hstable : (prefixWord ++ tailWord_422613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422613).length < 2 ^ (prefixWord ++ tailWord_422613).sum := by decide
  have hdescent : baseEnd_422613 < baseStart_422613 := by decide
  rcases family_descends (prefixWord ++ tailWord_422613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422635 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 4]
def baseStart_422635 : Nat := 118140960795 + 422635 * 2 ^ 59
def prefixEnd_422635 : Nat := 4983230072969 + 3 ^ 40 * 422635 * 2
def baseEnd_422635 : Nat := 96451065072470743252819

theorem tailTrace_422635 : CollatzResearch.WordTrace tailWord_422635 prefixEnd_422635 96451065072470743252819 := by
  unfold tailWord_422635
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414764823873050156541359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10276509882582033437694239 15414764823873050156541359)
  ·
    refine ⟨23122147235809575234812039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15414764823873050156541359 23122147235809575234812039)
    ·
      refine ⟨34683220853714362852218059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23122147235809575234812039 34683220853714362852218059)
      ·
        refine ⟨52024831280571544278327089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34683220853714362852218059 52024831280571544278327089)
        ·
          refine ⟨39018623460428658208745317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52024831280571544278327089 39018623460428658208745317)
          ·
            refine ⟨7315991898830373414139747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39018623460428658208745317 7315991898830373414139747)
            ·
              refine ⟨10973987848245560121209621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315991898830373414139747 10973987848245560121209621)
              ·
                refine ⟨514405680386510630681701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10973987848245560121209621 514405680386510630681701)
                ·
                  refine ⟨96451065072470743252819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514405680386510630681701 96451065072470743252819)
                  ·
                    rfl

theorem cell21_422635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_422635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422635 prefixEnd_422635 := by exact prefixLift 422635
  have htrace : WordTrace (prefixWord ++ tailWord_422635) baseStart_422635 baseEnd_422635 := by
    simpa [prefixWord, tailWord_422635, baseEnd_422635] using wordTrace_append hprefix tailTrace_422635
  have hstable : (prefixWord ++ tailWord_422635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422635).length < 2 ^ (prefixWord ++ tailWord_422635).sum := by decide
  have hdescent : baseEnd_422635 < baseStart_422635 := by decide
  rcases family_descends (prefixWord ++ tailWord_422635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422638 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_422638 : Nat := 118140960795 + 422638 * 2 ^ 59
def prefixEnd_422638 : Nat := 4983230072969 + 3 ^ 40 * 422638 * 2
def baseEnd_422638 : Nat := 96451749713343404702813

theorem tailTrace_422638 : CollatzResearch.WordTrace tailWord_422638 prefixEnd_422638 96451749713343404702813 := by
  unfold tailWord_422638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926859280357772708612571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10276582828574787779267045 1926859280357772708612571)
  ·
    refine ⟨2890288920536659062918857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926859280357772708612571 2890288920536659062918857)
    ·
      refine ⟨2167716690402494297189143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2890288920536659062918857 2167716690402494297189143)
      ·
        refine ⟨3251575035603741445783715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167716690402494297189143 3251575035603741445783715)
        ·
          refine ⟨4877362553405612168675573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251575035603741445783715 4877362553405612168675573)
          ·
            refine ⟨457252739381776140813335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4877362553405612168675573 457252739381776140813335)
            ·
              refine ⟨685879109072664211220003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457252739381776140813335 685879109072664211220003)
              ·
                refine ⟨1028818663608996316830005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685879109072664211220003 1028818663608996316830005)
                ·
                  refine ⟨96451749713343404702813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028818663608996316830005 96451749713343404702813)
                  ·
                    rfl

theorem cell21_422638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_422638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422638 prefixEnd_422638 := by exact prefixLift 422638
  have htrace : WordTrace (prefixWord ++ tailWord_422638) baseStart_422638 baseEnd_422638 := by
    simpa [prefixWord, tailWord_422638, baseEnd_422638] using wordTrace_append hprefix tailTrace_422638
  have hstable : (prefixWord ++ tailWord_422638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422638).length < 2 ^ (prefixWord ++ tailWord_422638).sum := by decide
  have hdescent : baseEnd_422638 < baseStart_422638 := by decide
  rcases family_descends (prefixWord ++ tailWord_422638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422644 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_422644 : Nat := 118140960795 + 422644 * 2 ^ 59
def prefixEnd_422644 : Nat := 4983230072969 + 3 ^ 40 * 422644 * 2
def baseEnd_422644 : Nat := 96453118995088727602801

theorem tailTrace_422644 : CollatzResearch.WordTrace tailWord_422644 prefixEnd_422644 96453118995088727602801 := by
  unfold tailWord_422644
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707546540420222346809493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10276728720560296462412657 7707546540420222346809493)
  ·
    refine ⟨361291244082197922506695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7707546540420222346809493 361291244082197922506695)
    ·
      refine ⟨541936866123296883760043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361291244082197922506695 541936866123296883760043)
      ·
        refine ⟨812905299184945325640065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541936866123296883760043 812905299184945325640065)
        ·
          refine ⟨609678974388708994230049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812905299184945325640065 609678974388708994230049)
          ·
            refine ⟨457259230791531745672537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609678974388708994230049 457259230791531745672537)
            ·
              refine ⟨342944423093648809254403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457259230791531745672537 342944423093648809254403)
              ·
                refine ⟨514416634640473213881605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342944423093648809254403 514416634640473213881605)
                ·
                  refine ⟨96453118995088727602801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514416634640473213881605 96453118995088727602801)
                  ·
                    rfl

theorem cell21_422644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_422644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422644 prefixEnd_422644 := by exact prefixLift 422644
  have htrace : WordTrace (prefixWord ++ tailWord_422644) baseStart_422644 baseEnd_422644 := by
    simpa [prefixWord, tailWord_422644, baseEnd_422644] using wordTrace_append hprefix tailTrace_422644
  have hstable : (prefixWord ++ tailWord_422644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422644).length < 2 ^ (prefixWord ++ tailWord_422644).sum := by decide
  have hdescent : baseEnd_422644 < baseStart_422644 := by decide
  rcases family_descends (prefixWord ++ tailWord_422644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422652 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_422652 : Nat := 118140960795 + 422652 * 2 ^ 59
def prefixEnd_422652 : Nat := 4983230072969 + 3 ^ 40 * 422652 * 2
def baseEnd_422652 : Nat := 96454944704082491469451

theorem tailTrace_422652 : CollatzResearch.WordTrace tailWord_422652 prefixEnd_422652 96454944704082491469451 := by
  unfold tailWord_422652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707692432405731029955105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10276923243207641373273473 7707692432405731029955105)
  ·
    refine ⟨5780769324304298272466329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7707692432405731029955105 5780769324304298272466329)
    ·
      refine ⟨4335576993228223704349747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5780769324304298272466329 4335576993228223704349747)
      ·
        refine ⟨6503365489842335556524621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335576993228223704349747 6503365489842335556524621)
        ·
          refine ⟨2438762058690875833696733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6503365489842335556524621 2438762058690875833696733)
          ·
            refine ⟨914535772009078437636275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2438762058690875833696733 914535772009078437636275)
            ·
              refine ⟨1371803658013617656454413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914535772009078437636275 1371803658013617656454413)
              ·
                refine ⟨514426371755106621170405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1371803658013617656454413 514426371755106621170405)
                ·
                  refine ⟨96454944704082491469451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514426371755106621170405 96454944704082491469451)
                  ·
                    rfl

theorem cell21_422652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_422652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422652 prefixEnd_422652 := by exact prefixLift 422652
  have htrace : WordTrace (prefixWord ++ tailWord_422652) baseStart_422652 baseEnd_422652 := by
    simpa [prefixWord, tailWord_422652, baseEnd_422652] using wordTrace_append hprefix tailTrace_422652
  have hstable : (prefixWord ++ tailWord_422652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422652).length < 2 ^ (prefixWord ++ tailWord_422652).sum := by decide
  have hdescent : baseEnd_422652 < baseStart_422652 := by decide
  rcases family_descends (prefixWord ++ tailWord_422652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422697 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 3]
def baseStart_422697 : Nat := 118140960795 + 422697 * 2 ^ 59
def prefixEnd_422697 : Nat := 4983230072969 + 3 ^ 40 * 422697 * 2
def baseEnd_422697 : Nat := 96465214317172413219359

theorem tailTrace_422697 : CollatzResearch.WordTrace tailWord_422697 prefixEnd_422697 96465214317172413219359 := by
  unfold tailWord_422697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15417026149648434745298345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10278017433098956496865563 15417026149648434745298345)
  ·
    refine ⟨11562769612236326058973759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15417026149648434745298345 11562769612236326058973759)
    ·
      refine ⟨17344154418354489088460639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11562769612236326058973759 17344154418354489088460639)
      ·
        refine ⟨26016231627531733632690959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17344154418354489088460639 26016231627531733632690959)
        ·
          refine ⟨39024347441297600449036439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26016231627531733632690959 39024347441297600449036439)
          ·
            refine ⟨58536521161946400673554659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39024347441297600449036439 58536521161946400673554659)
            ·
              refine ⟨87804781742919601010331989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58536521161946400673554659 87804781742919601010331989)
              ·
                refine ⟨257240571512459768584957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 87804781742919601010331989 257240571512459768584957)
                ·
                  refine ⟨96465214317172413219359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257240571512459768584957 96465214317172413219359)
                  ·
                    rfl

theorem cell21_422697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_422697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422697 prefixEnd_422697 := by exact prefixLift 422697
  have htrace : WordTrace (prefixWord ++ tailWord_422697) baseStart_422697 baseEnd_422697 := by
    simpa [prefixWord, tailWord_422697, baseEnd_422697] using wordTrace_append hprefix tailTrace_422697
  have hstable : (prefixWord ++ tailWord_422697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422697).length < 2 ^ (prefixWord ++ tailWord_422697).sum := by decide
  have hdescent : baseEnd_422697 < baseStart_422697 := by decide
  rcases family_descends (prefixWord ++ tailWord_422697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422711 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 4]
def baseStart_422711 : Nat := 118140960795 + 422711 * 2 ^ 59
def prefixEnd_422711 : Nat := 4983230072969 + 3 ^ 40 * 422711 * 2
def baseEnd_422711 : Nat := 96468409307911499985997

theorem tailTrace_422711 : CollatzResearch.WordTrace tailWord_422711 prefixEnd_422711 96468409307911499985997 := by
  unfold tailWord_422711
  simp only [CollatzResearch.WordTrace]
  refine ⟨15417536771597715136307987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10278357847731810090871991 15417536771597715136307987)
  ·
    refine ⟨23126305157396572704461981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15417536771597715136307987 23126305157396572704461981)
    ·
      refine ⟨8672364434023714764173243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23126305157396572704461981 8672364434023714764173243)
      ·
        refine ⟨13008546651035572146259865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8672364434023714764173243 13008546651035572146259865)
        ·
          refine ⟨9756409988276679109694899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13008546651035572146259865 9756409988276679109694899)
          ·
            refine ⟨14634614982415018664542349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9756409988276679109694899 14634614982415018664542349)
            ·
              refine ⟨5487980618405631999203381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14634614982415018664542349 5487980618405631999203381)
              ·
                refine ⟨514498182975527999925317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5487980618405631999203381 514498182975527999925317)
                ·
                  refine ⟨96468409307911499985997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514498182975527999925317 96468409307911499985997)
                  ·
                    rfl

theorem cell21_422711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_422711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422711 prefixEnd_422711 := by exact prefixLift 422711
  have htrace : WordTrace (prefixWord ++ tailWord_422711) baseStart_422711 baseEnd_422711 := by
    simpa [prefixWord, tailWord_422711, baseEnd_422711] using wordTrace_append hprefix tailTrace_422711
  have hstable : (prefixWord ++ tailWord_422711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422711).length < 2 ^ (prefixWord ++ tailWord_422711).sum := by decide
  have hdescent : baseEnd_422711 < baseStart_422711 := by decide
  rcases family_descends (prefixWord ++ tailWord_422711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422773 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_422773 : Nat := 118140960795 + 422773 * 2 ^ 59
def prefixEnd_422773 : Nat := 4983230072969 + 3 ^ 40 * 422773 * 2
def baseEnd_422773 : Nat := 96482558552613169952537

theorem tailTrace_422773 : CollatzResearch.WordTrace tailWord_422773 prefixEnd_422773 96482558552613169952537 := by
  unfold tailWord_422773
  simp only [CollatzResearch.WordTrace]
  refine ⟨15419798097373099725064973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10279865398248733150043315 15419798097373099725064973)
  ·
    refine ⟨5782424286514912396899365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15419798097373099725064973 5782424286514912396899365)
    ·
      refine ⟨1084204553721546074418631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5782424286514912396899365 1084204553721546074418631)
      ·
        refine ⟨1626306830582319111627947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084204553721546074418631 1626306830582319111627947)
        ·
          refine ⟨2439460245873478667441921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626306830582319111627947 2439460245873478667441921)
          ·
            refine ⟨1829595184405109000581441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439460245873478667441921 1829595184405109000581441)
            ·
              refine ⟨1372196388303831750436081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829595184405109000581441 1372196388303831750436081)
              ·
                refine ⟨1029147291227873812827061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372196388303831750436081 1029147291227873812827061)
                ·
                  refine ⟨96482558552613169952537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029147291227873812827061 96482558552613169952537)
                  ·
                    rfl

theorem cell21_422773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_422773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422773 prefixEnd_422773 := by exact prefixLift 422773
  have htrace : WordTrace (prefixWord ++ tailWord_422773) baseStart_422773 baseEnd_422773 := by
    simpa [prefixWord, tailWord_422773, baseEnd_422773] using wordTrace_append hprefix tailTrace_422773
  have hstable : (prefixWord ++ tailWord_422773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422773).length < 2 ^ (prefixWord ++ tailWord_422773).sum := by decide
  have hdescent : baseEnd_422773 < baseStart_422773 := by decide
  rcases family_descends (prefixWord ++ tailWord_422773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422804 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_422804 : Nat := 118140960795 + 422804 * 2 ^ 59
def prefixEnd_422804 : Nat := 4983230072969 + 3 ^ 40 * 422804 * 2
def baseEnd_422804 : Nat := 96489633174964004935807

theorem tailTrace_422804 : CollatzResearch.WordTrace tailWord_422804 prefixEnd_422804 96489633174964004935807 := by
  unfold tailWord_422804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710464380130396009721733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10280619173507194679628977 7710464380130396009721733)
  ·
    refine ⟨1445712071274449251822825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7710464380130396009721733 1445712071274449251822825)
    ·
      refine ⟨1084284053455836938867119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1445712071274449251822825 1084284053455836938867119)
      ·
        refine ⟨1626426080183755408300679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084284053455836938867119 1626426080183755408300679)
        ·
          refine ⟨2439639120275633112451019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626426080183755408300679 2439639120275633112451019)
          ·
            refine ⟨3659458680413449668676529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439639120275633112451019 3659458680413449668676529)
            ·
              refine ⟨2744594010310087251507397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3659458680413449668676529 2744594010310087251507397)
              ·
                refine ⟨514611376933141359657637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2744594010310087251507397 514611376933141359657637)
                ·
                  refine ⟨96489633174964004935807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514611376933141359657637 96489633174964004935807)
                  ·
                    rfl

theorem cell21_422804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_422804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422804 prefixEnd_422804 := by exact prefixLift 422804
  have htrace : WordTrace (prefixWord ++ tailWord_422804) baseStart_422804 baseEnd_422804 := by
    simpa [prefixWord, tailWord_422804, baseEnd_422804] using wordTrace_append hprefix tailTrace_422804
  have hstable : (prefixWord ++ tailWord_422804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422804).length < 2 ^ (prefixWord ++ tailWord_422804).sum := by decide
  have hdescent : baseEnd_422804 < baseStart_422804 := by decide
  rcases family_descends (prefixWord ++ tailWord_422804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422818 : List Nat := [3, 3, 1, 2, 2, 1, 1, 8]
def baseStart_422818 : Nat := 118140960795 + 422818 * 2 ^ 59
def prefixEnd_422818 : Nat := 4983230072969 + 3 ^ 40 * 422818 * 2
def baseEnd_422818 : Nat := 32164276055234363900815

theorem tailTrace_422818 : CollatzResearch.WordTrace tailWord_422818 prefixEnd_422818 32164276055234363900815 := by
  unfold tailWord_422818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855359845552518102613277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10280959588140048273635405 3855359845552518102613277)
  ·
    refine ⟨1445759942082194288479979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3855359845552518102613277 1445759942082194288479979)
    ·
      refine ⟨2168639913123291432719969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445759942082194288479979 2168639913123291432719969)
      ·
        refine ⟨1626479934842468574539977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2168639913123291432719969 1626479934842468574539977)
        ·
          refine ⟨1219859951131851430904983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1626479934842468574539977 1219859951131851430904983)
          ·
            refine ⟨1829789926697777146357475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219859951131851430904983 1829789926697777146357475)
            ·
              refine ⟨2744684890046665719536213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829789926697777146357475 2744684890046665719536213)
              ·
                refine ⟨32164276055234363900815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2744684890046665719536213 32164276055234363900815)
                ·
                  rfl

theorem cell21_422818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_422818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422818 prefixEnd_422818 := by exact prefixLift 422818
  have htrace : WordTrace (prefixWord ++ tailWord_422818) baseStart_422818 baseEnd_422818 := by
    simpa [prefixWord, tailWord_422818, baseEnd_422818] using wordTrace_append hprefix tailTrace_422818
  have hstable : (prefixWord ++ tailWord_422818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422818).length < 2 ^ (prefixWord ++ tailWord_422818).sum := by decide
  have hdescent : baseEnd_422818 < baseStart_422818 := by decide
  rcases family_descends (prefixWord ++ tailWord_422818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422863 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 4]
def baseStart_422863 : Nat := 118140960795 + 422863 * 2 ^ 59
def prefixEnd_422863 : Nat := 4983230072969 + 3 ^ 40 * 422863 * 2
def baseEnd_422863 : Nat := 96503097778793013452353

theorem tailTrace_422863 : CollatzResearch.WordTrace tailWord_422863 prefixEnd_422863 96503097778793013452353 := by
  unfold tailWord_422863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15423080667047045095841243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10282053778031363397227495 15423080667047045095841243)
  ·
    refine ⟨23134621000570567643761865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15423080667047045095841243 23134621000570567643761865)
    ·
      refine ⟨17350965750427925732821399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23134621000570567643761865 17350965750427925732821399)
      ·
        refine ⟨26026448625641888599232099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17350965750427925732821399 26026448625641888599232099)
        ·
          refine ⟨39039672938462832898848149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26026448625641888599232099 39039672938462832898848149)
          ·
            refine ⟨1829984668990445292133507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39039672938462832898848149 1829984668990445292133507)
            ·
              refine ⟨2744977003485667938200261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829984668990445292133507 2744977003485667938200261)
              ·
                refine ⟨514683188153562738412549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2744977003485667938200261 514683188153562738412549)
                ·
                  refine ⟨96503097778793013452353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514683188153562738412549 96503097778793013452353)
                  ·
                    rfl

theorem cell21_422863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_422863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_422863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_422863 prefixEnd_422863 := by exact prefixLift 422863
  have htrace : WordTrace (prefixWord ++ tailWord_422863) baseStart_422863 baseEnd_422863 := by
    simpa [prefixWord, tailWord_422863, baseEnd_422863] using wordTrace_append hprefix tailTrace_422863
  have hstable : (prefixWord ++ tailWord_422863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422863).length < 2 ^ (prefixWord ++ tailWord_422863).sum := by decide
  have hdescent : baseEnd_422863 < baseStart_422863 := by decide
  rcases family_descends (prefixWord ++ tailWord_422863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423038 : List Nat := [4, 2, 4, 1, 2, 1, 1, 6]
def baseStart_423038 : Nat := 118140960795 + 423038 * 2 ^ 59
def prefixEnd_423038 : Nat := 4983230072969 + 3 ^ 40 * 423038 * 2
def baseEnd_423038 : Nat := 32181011721010532678443

theorem tailTrace_423038 : CollatzResearch.WordTrace tailWord_423038 prefixEnd_423038 32181011721010532678443 := by
  unfold tailWord_423038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928682930176631247932721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10286308960942033322307845 1928682930176631247932721)
  ·
    refine ⟨1446512197632473435949541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928682930176631247932721 1446512197632473435949541)
    ·
      refine ⟨271221037056088769240539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1446512197632473435949541 271221037056088769240539)
      ·
        refine ⟨406831555584133153860809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271221037056088769240539 406831555584133153860809)
        ·
          refine ⟨305123666688099865395607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406831555584133153860809 305123666688099865395607)
          ·
            refine ⟨457685500032149798093411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305123666688099865395607 457685500032149798093411)
            ·
              refine ⟨686528250048224697140117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457685500032149798093411 686528250048224697140117)
              ·
                refine ⟨32181011721010532678443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686528250048224697140117 32181011721010532678443)
                ·
                  rfl

theorem cell21_423038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_423038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423038 prefixEnd_423038 := by exact prefixLift 423038
  have htrace : WordTrace (prefixWord ++ tailWord_423038) baseStart_423038 baseEnd_423038 := by
    simpa [prefixWord, tailWord_423038, baseEnd_423038] using wordTrace_append hprefix tailTrace_423038
  have hstable : (prefixWord ++ tailWord_423038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423038).length < 2 ^ (prefixWord ++ tailWord_423038).sum := by decide
  have hdescent : baseEnd_423038 < baseStart_423038 := by decide
  rcases family_descends (prefixWord ++ tailWord_423038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423077 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 3]
def baseStart_423077 : Nat := 118140960795 + 423077 * 2 ^ 59
def prefixEnd_423077 : Nat := 4983230072969 + 3 ^ 40 * 423077 * 2
def baseEnd_423077 : Nat := 96551935494376196885249

theorem tailTrace_423077 : CollatzResearch.WordTrace tailWord_423077 prefixEnd_423077 96551935494376196885249 := by
  unfold tailWord_423077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430885888271759644131485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10287257258847839762754323 15430885888271759644131485)
  ·
    refine ⟨5786582208101909866549307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15430885888271759644131485 5786582208101909866549307)
    ·
      refine ⟨8679873312152864799823961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786582208101909866549307 8679873312152864799823961)
      ·
        refine ⟨6509904984114648599867971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8679873312152864799823961 6509904984114648599867971)
        ·
          refine ⟨9764857476171972899801957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509904984114648599867971 9764857476171972899801957)
          ·
            refine ⟨1830910776782244918712867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9764857476171972899801957 1830910776782244918712867)
            ·
              refine ⟨2746366165173367378069301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830910776782244918712867 2746366165173367378069301)
              ·
                refine ⟨257471827985003191693997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2746366165173367378069301 257471827985003191693997)
                ·
                  refine ⟨96551935494376196885249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257471827985003191693997 96551935494376196885249)
                  ·
                    rfl

theorem cell21_423077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_423077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423077 prefixEnd_423077 := by exact prefixLift 423077
  have htrace : WordTrace (prefixWord ++ tailWord_423077) baseStart_423077 baseEnd_423077 := by
    simpa [prefixWord, tailWord_423077, baseEnd_423077] using wordTrace_append hprefix tailTrace_423077
  have hstable : (prefixWord ++ tailWord_423077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423077).length < 2 ^ (prefixWord ++ tailWord_423077).sum := by decide
  have hdescent : baseEnd_423077 < baseStart_423077 := by decide
  rcases family_descends (prefixWord ++ tailWord_423077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423091 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 4]
def baseStart_423091 : Nat := 118140960795 + 423091 * 2 ^ 59
def prefixEnd_423091 : Nat := 4983230072969 + 3 ^ 40 * 423091 * 2
def baseEnd_423091 : Nat := 96555130485115283651887

theorem tailTrace_423091 : CollatzResearch.WordTrace tailWord_423091 prefixEnd_423091 96555130485115283651887 := by
  unfold tailWord_423091
  simp only [CollatzResearch.WordTrace]
  refine ⟨15431396510221040035141127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10287597673480693356760751 15431396510221040035141127)
  ·
    refine ⟨23147094765331560052711691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15431396510221040035141127 23147094765331560052711691)
    ·
      refine ⟨34720642147997340079067537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23147094765331560052711691 34720642147997340079067537)
      ·
        refine ⟨26040481610998005059300653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34720642147997340079067537 26040481610998005059300653)
        ·
          refine ⟨9765180604124251897237745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26040481610998005059300653 9765180604124251897237745)
          ·
            refine ⟨7323885453093188922928309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9765180604124251897237745 7323885453093188922928309)
            ·
              refine ⟨686614261227486461524529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7323885453093188922928309 686614261227486461524529)
              ·
                refine ⟨514960695920614846143397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686614261227486461524529 514960695920614846143397)
                ·
                  refine ⟨96555130485115283651887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514960695920614846143397 96555130485115283651887)
                  ·
                    rfl

theorem cell21_423091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_423091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423091 prefixEnd_423091 := by exact prefixLift 423091
  have htrace : WordTrace (prefixWord ++ tailWord_423091) baseStart_423091 baseEnd_423091 := by
    simpa [prefixWord, tailWord_423091, baseEnd_423091] using wordTrace_append hprefix tailTrace_423091
  have hstable : (prefixWord ++ tailWord_423091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423091).length < 2 ^ (prefixWord ++ tailWord_423091).sum := by decide
  have hdescent : baseEnd_423091 < baseStart_423091 := by decide
  rcases family_descends (prefixWord ++ tailWord_423091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423119 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_423119 : Nat := 118140960795 + 423119 * 2 ^ 59
def prefixEnd_423119 : Nat := 4983230072969 + 3 ^ 40 * 423119 * 2
def baseEnd_423119 : Nat := 96561520466593457185163

theorem tailTrace_423119 : CollatzResearch.WordTrace tailWord_423119 prefixEnd_423119 96561520466593457185163 := by
  unfold tailWord_423119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432417754119600817160411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10288278502746400544773607 15432417754119600817160411)
  ·
    refine ⟨23148626631179401225740617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15432417754119600817160411 23148626631179401225740617)
    ·
      refine ⟨17361469973384550919305463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23148626631179401225740617 17361469973384550919305463)
      ·
        refine ⟨26042204960076826378958195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17361469973384550919305463 26042204960076826378958195)
        ·
          refine ⟨39063307440115239568437293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26042204960076826378958195 39063307440115239568437293)
          ·
            refine ⟨14648740290043214838163985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39063307440115239568437293 14648740290043214838163985)
            ·
              refine ⟨10986555217532411128622989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14648740290043214838163985 10986555217532411128622989)
              ·
                refine ⟨4119958206574654173233621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10986555217532411128622989 4119958206574654173233621)
                ·
                  refine ⟨96561520466593457185163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4119958206574654173233621 96561520466593457185163)
                  ·
                    rfl

theorem cell21_423119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_423119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423119 prefixEnd_423119 := by exact prefixLift 423119
  have htrace : WordTrace (prefixWord ++ tailWord_423119) baseStart_423119 baseEnd_423119 := by
    simpa [prefixWord, tailWord_423119, baseEnd_423119] using wordTrace_append hprefix tailTrace_423119
  have hstable : (prefixWord ++ tailWord_423119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423119).length < 2 ^ (prefixWord ++ tailWord_423119).sum := by decide
  have hdescent : baseEnd_423119 < baseStart_423119 := by decide
  rcases family_descends (prefixWord ++ tailWord_423119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423167 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 4]
def baseStart_423167 : Nat := 118140960795 + 423167 * 2 ^ 59
def prefixEnd_423167 : Nat := 4983230072969 + 3 ^ 40 * 423167 * 2
def baseEnd_423167 : Nat := 96572474720556040385065

theorem tailTrace_423167 : CollatzResearch.WordTrace tailWord_423167 prefixEnd_423167 96572474720556040385065 := by
  unfold tailWord_423167
  simp only [CollatzResearch.WordTrace]
  refine ⟨15434168457945705014907755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10289445638630470009938503 15434168457945705014907755)
  ·
    refine ⟨23151252686918557522361633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15434168457945705014907755 23151252686918557522361633)
    ·
      refine ⟨17363439515188918141771225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23151252686918557522361633 17363439515188918141771225)
      ·
        refine ⟨13022579636391688606328419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17363439515188918141771225 13022579636391688606328419)
        ·
          refine ⟨19533869454587532909492629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13022579636391688606328419 19533869454587532909492629)
          ·
            refine ⟨915650130683790605132467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19533869454587532909492629 915650130683790605132467)
            ·
              refine ⟨1373475196025685907698701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915650130683790605132467 1373475196025685907698701)
              ·
                refine ⟨515053198509632215387013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1373475196025685907698701 515053198509632215387013)
                ·
                  refine ⟨96572474720556040385065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515053198509632215387013 96572474720556040385065)
                  ·
                    rfl

theorem cell21_423167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_423167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423167 prefixEnd_423167 := by exact prefixLift 423167
  have htrace : WordTrace (prefixWord ++ tailWord_423167) baseStart_423167 baseEnd_423167 := by
    simpa [prefixWord, tailWord_423167, baseEnd_423167] using wordTrace_append hprefix tailTrace_423167
  have hstable : (prefixWord ++ tailWord_423167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423167).length < 2 ^ (prefixWord ++ tailWord_423167).sum := by decide
  have hdescent : baseEnd_423167 < baseStart_423167 := by decide
  rcases family_descends (prefixWord ++ tailWord_423167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423198 : List Nat := [4, 3, 2, 1, 11]
def baseStart_423198 : Nat := 118140960795 + 423198 * 2 ^ 59
def prefixEnd_423198 : Nat := 4983230072969 + 3 ^ 40 * 423198 * 2
def baseEnd_423198 : Nat := 1192340115344529325535

theorem tailTrace_423198 : CollatzResearch.WordTrace tailWord_423198 prefixEnd_423198 1192340115344529325535 := by
  unfold tailWord_423198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929412390104174663660781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10290199413888931539524165 1929412390104174663660781)
  ·
    refine ⟨723529646289065498872793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1929412390104174663660781 723529646289065498872793)
    ·
      refine ⟨542647234716799124154595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 723529646289065498872793 542647234716799124154595)
      ·
        refine ⟨813970852075198686231893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542647234716799124154595 813970852075198686231893)
        ·
          refine ⟨1192340115344529325535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 813970852075198686231893 1192340115344529325535)
          ·
            rfl

theorem cell21_423198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 11].length) (baseStart_423198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423198 prefixEnd_423198 := by exact prefixLift 423198
  have htrace : WordTrace (prefixWord ++ tailWord_423198) baseStart_423198 baseEnd_423198 := by
    simpa [prefixWord, tailWord_423198, baseEnd_423198] using wordTrace_append hprefix tailTrace_423198
  have hstable : (prefixWord ++ tailWord_423198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423198).length < 2 ^ (prefixWord ++ tailWord_423198).sum := by decide
  have hdescent : baseEnd_423198 < baseStart_423198 := by decide
  rcases family_descends (prefixWord ++ tailWord_423198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423322 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_423322 : Nat := 118140960795 + 423322 * 2 ^ 59
def prefixEnd_423322 : Nat := 4983230072969 + 3 ^ 40 * 423322 * 2
def baseEnd_423322 : Nat := 96607847832310215301415

theorem tailTrace_423322 : CollatzResearch.WordTrace tailWord_423322 prefixEnd_423322 96607847832310215301415 := by
  unfold tailWord_423322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859955443096041621700055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10293214514922777657866813 3859955443096041621700055)
  ·
    refine ⟨5789933164644062432550083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3859955443096041621700055 5789933164644062432550083)
    ·
      refine ⟨8684899746966093648825125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789933164644062432550083 8684899746966093648825125)
      ·
        refine ⟨1628418702556142559154711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8684899746966093648825125 1628418702556142559154711)
        ·
          refine ⟨2442628053834213838732067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628418702556142559154711 2442628053834213838732067)
          ·
            refine ⟨3663942080751320758098101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442628053834213838732067 3663942080751320758098101)
            ·
              refine ⟨343494570070436321071697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3663942080751320758098101 343494570070436321071697)
              ·
                refine ⟨257620927552827240803773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343494570070436321071697 257620927552827240803773)
                ·
                  refine ⟨96607847832310215301415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257620927552827240803773 96607847832310215301415)
                  ·
                    rfl

theorem cell21_423322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_423322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423322 prefixEnd_423322 := by exact prefixLift 423322
  have htrace : WordTrace (prefixWord ++ tailWord_423322) baseStart_423322 baseEnd_423322 := by
    simpa [prefixWord, tailWord_423322, baseEnd_423322] using wordTrace_append hprefix tailTrace_423322
  have hstable : (prefixWord ++ tailWord_423322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423322).length < 2 ^ (prefixWord ++ tailWord_423322).sum := by decide
  have hdescent : baseEnd_423322 < baseStart_423322 := by decide
  rcases family_descends (prefixWord ++ tailWord_423322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423347 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_423347 : Nat := 118140960795 + 423347 * 2 ^ 59
def prefixEnd_423347 : Nat := 4983230072969 + 3 ^ 40 * 423347 * 2
def baseEnd_423347 : Nat := 96613553172915727384697

theorem tailTrace_423347 : CollatzResearch.WordTrace tailWord_423347 prefixEnd_423347 96613553172915727384697 := by
  unfold tailWord_423347
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440733597293595756460295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10293822398195730504306863 15440733597293595756460295)
  ·
    refine ⟨23161100395940393634690443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15440733597293595756460295 23161100395940393634690443)
    ·
      refine ⟨34741650593910590452035665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23161100395940393634690443 34741650593910590452035665)
      ·
        refine ⟨26056237945432942839026749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34741650593910590452035665 26056237945432942839026749)
        ·
          refine ⟨9771089229537353564635031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26056237945432942839026749 9771089229537353564635031)
          ·
            refine ⟨14656633844306030346952547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9771089229537353564635031 14656633844306030346952547)
            ·
              refine ⟨21984950766459045520428821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14656633844306030346952547 21984950766459045520428821)
              ·
                refine ⟨1030544567177767758770101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21984950766459045520428821 1030544567177767758770101)
                ·
                  refine ⟨96613553172915727384697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1030544567177767758770101 96613553172915727384697)
                  ·
                    rfl

theorem cell21_423347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_423347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423347 prefixEnd_423347 := by exact prefixLift 423347
  have htrace : WordTrace (prefixWord ++ tailWord_423347) baseStart_423347 baseEnd_423347 := by
    simpa [prefixWord, tailWord_423347, baseEnd_423347] using wordTrace_append hprefix tailTrace_423347
  have hstable : (prefixWord ++ tailWord_423347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423347).length < 2 ^ (prefixWord ++ tailWord_423347).sum := by decide
  have hdescent : baseEnd_423347 < baseStart_423347 := by decide
  rcases family_descends (prefixWord ++ tailWord_423347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423381 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 3]
def baseStart_423381 : Nat := 118140960795 + 423381 * 2 ^ 59
def prefixEnd_423381 : Nat := 4983230072969 + 3 ^ 40 * 423381 * 2
def baseEnd_423381 : Nat := 96621312436139223817961

theorem tailTrace_423381 : CollatzResearch.WordTrace tailWord_423381 prefixEnd_423381 96621312436139223817961 := by
  unfold tailWord_423381
  simp only [CollatzResearch.WordTrace]
  refine ⟨15441973679170419563197997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10294649119446946375465331 15441973679170419563197997)
  ·
    refine ⟨5790740129688907336199249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15441973679170419563197997 5790740129688907336199249)
    ·
      refine ⟨4343055097266680502149437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5790740129688907336199249 4343055097266680502149437)
      ·
        refine ⟨1628645661475005188306039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4343055097266680502149437 1628645661475005188306039)
        ·
          refine ⟨2442968492212507782459059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628645661475005188306039 2442968492212507782459059)
          ·
            refine ⟨3664452738318761673688589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442968492212507782459059 3664452738318761673688589)
            ·
              refine ⟨1374169776869535627633221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3664452738318761673688589 1374169776869535627633221)
              ·
                refine ⟨257656833163037930181229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1374169776869535627633221 257656833163037930181229)
                ·
                  refine ⟨96621312436139223817961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257656833163037930181229 96621312436139223817961)
                  ·
                    rfl

theorem cell21_423381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_423381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423381 prefixEnd_423381 := by exact prefixLift 423381
  have htrace : WordTrace (prefixWord ++ tailWord_423381) baseStart_423381 baseEnd_423381 := by
    simpa [prefixWord, tailWord_423381, baseEnd_423381] using wordTrace_append hprefix tailTrace_423381
  have hstable : (prefixWord ++ tailWord_423381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423381).length < 2 ^ (prefixWord ++ tailWord_423381).sum := by decide
  have hdescent : baseEnd_423381 < baseStart_423381 := by decide
  rcases family_descends (prefixWord ++ tailWord_423381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423392 : List Nat := [2, 1, 1, 3, 1, 1, 2, 10]
def baseStart_423392 : Nat := 118140960795 + 423392 * 2 ^ 59
def prefixEnd_423392 : Nat := 4983230072969 + 3 ^ 40 * 423392 * 2
def baseEnd_423392 : Nat := 32207940928668549711535

theorem tailTrace_423392 : CollatzResearch.WordTrace tailWord_423392 prefixEnd_423392 32207940928668549711535 := by
  unfold tailWord_423392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721187441065284220924215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10294916588087045627898953 7721187441065284220924215)
  ·
    refine ⟨11581781161597926331386323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721187441065284220924215 11581781161597926331386323)
    ·
      refine ⟨17372671742396889497079485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11581781161597926331386323 17372671742396889497079485)
      ·
        refine ⟨6514751903398833561404807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17372671742396889497079485 6514751903398833561404807)
        ·
          refine ⟨9772127855098250342107211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6514751903398833561404807 9772127855098250342107211)
          ·
            refine ⟨14658191782647375513160817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9772127855098250342107211 14658191782647375513160817)
            ·
              refine ⟨10993643836985531634870613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14658191782647375513160817 10993643836985531634870613)
              ·
                refine ⟨32207940928668549711535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10993643836985531634870613 32207940928668549711535)
                ·
                  rfl

theorem cell21_423392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_423392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423392 prefixEnd_423392 := by exact prefixLift 423392
  have htrace : WordTrace (prefixWord ++ tailWord_423392) baseStart_423392 baseEnd_423392 := by
    simpa [prefixWord, tailWord_423392, baseEnd_423392] using wordTrace_append hprefix tailTrace_423392
  have hstable : (prefixWord ++ tailWord_423392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423392).length < 2 ^ (prefixWord ++ tailWord_423392).sum := by decide
  have hdescent : baseEnd_423392 < baseStart_423392 := by decide
  rcases family_descends (prefixWord ++ tailWord_423392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423395 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 4]
def baseStart_423395 : Nat := 118140960795 + 423395 * 2 ^ 59
def prefixEnd_423395 : Nat := 4983230072969 + 3 ^ 40 * 423395 * 2
def baseEnd_423395 : Nat := 96624507426878310584599

theorem tailTrace_423395 : CollatzResearch.WordTrace tailWord_423395 prefixEnd_423395 96624507426878310584599 := by
  unfold tailWord_423395
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442484301119699954207639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10294989534079799969471759 15442484301119699954207639)
  ·
    refine ⟨23163726451679549931311459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15442484301119699954207639 23163726451679549931311459)
    ·
      refine ⟨34745589677519324896967189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23163726451679549931311459 34745589677519324896967189)
      ·
        refine ⟨1628699516133718354545337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34745589677519324896967189 1628699516133718354545337)
        ·
          refine ⟨1221524637100288765909003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1628699516133718354545337 1221524637100288765909003)
          ·
            refine ⟨1832286955650433148863505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221524637100288765909003 1832286955650433148863505)
            ·
              refine ⟨1374215216737824861647629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832286955650433148863505 1374215216737824861647629)
              ·
                refine ⟨515330706276684323117861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1374215216737824861647629 515330706276684323117861)
                ·
                  refine ⟨96624507426878310584599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515330706276684323117861 96624507426878310584599)
                  ·
                    rfl

theorem cell21_423395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_423395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423395 prefixEnd_423395 := by exact prefixLift 423395
  have htrace : WordTrace (prefixWord ++ tailWord_423395) baseStart_423395 baseEnd_423395 := by
    simpa [prefixWord, tailWord_423395, baseEnd_423395] using wordTrace_append hprefix tailTrace_423395
  have hstable : (prefixWord ++ tailWord_423395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423395).length < 2 ^ (prefixWord ++ tailWord_423395).sum := by decide
  have hdescent : baseEnd_423395 < baseStart_423395 := by decide
  rcases family_descends (prefixWord ++ tailWord_423395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423426 : List Nat := [3, 4, 1, 2, 1, 2, 8]
def baseStart_423426 : Nat := 118140960795 + 423426 * 2 ^ 59
def prefixEnd_423426 : Nat := 4983230072969 + 3 ^ 40 * 423426 * 2
def baseEnd_423426 : Nat := 10736842449914349507541

theorem tailTrace_423426 : CollatzResearch.WordTrace tailWord_423426 prefixEnd_423426 10736842449914349507541 := by
  unfold tailWord_423426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860903741001848062146533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10295743309338261499057421 3860903741001848062146533)
  ·
    refine ⟨723919451437846511652475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3860903741001848062146533 723919451437846511652475)
    ·
      refine ⟨1085879177156769767478713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723919451437846511652475 1085879177156769767478713)
      ·
        refine ⟨814409382867577325609035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1085879177156769767478713 814409382867577325609035)
        ·
          refine ⟨1221614074301365988413553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814409382867577325609035 1221614074301365988413553)
          ·
            refine ⟨916210555726024491310165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1221614074301365988413553 916210555726024491310165)
            ·
              refine ⟨10736842449914349507541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 916210555726024491310165 10736842449914349507541)
              ·
                rfl

theorem cell21_423426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 8].length) (baseStart_423426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423426 prefixEnd_423426 := by exact prefixLift 423426
  have htrace : WordTrace (prefixWord ++ tailWord_423426) baseStart_423426 baseEnd_423426 := by
    simpa [prefixWord, tailWord_423426, baseEnd_423426] using wordTrace_append hprefix tailTrace_423426
  have hstable : (prefixWord ++ tailWord_423426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423426).length < 2 ^ (prefixWord ++ tailWord_423426).sum := by decide
  have hdescent : baseEnd_423426 < baseStart_423426 := by decide
  rcases family_descends (prefixWord ++ tailWord_423426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423575 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_423575 : Nat := 118140960795 + 423575 * 2 ^ 59
def prefixEnd_423575 : Nat := 4983230072969 + 3 ^ 40 * 423575 * 2
def baseEnd_423575 : Nat := 96665585879237997584231

theorem tailTrace_423575 : CollatzResearch.WordTrace tailWord_423575 prefixEnd_423575 96665585879237997584231 := by
  unfold tailWord_423575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15449049440467590695760179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10299366293645060463840119 15449049440467590695760179)
  ·
    refine ⟨23173574160701386043640269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15449049440467590695760179 23173574160701386043640269)
    ·
      refine ⟨8690090310263019766365101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23173574160701386043640269 8690090310263019766365101)
      ·
        refine ⟨3258783866348632412386913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8690090310263019766365101 3258783866348632412386913)
        ·
          refine ⟨2444087899761474309290185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3258783866348632412386913 2444087899761474309290185)
          ·
            refine ⟨1833065924821105731967639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444087899761474309290185 1833065924821105731967639)
            ·
              refine ⟨2749598887231658597951459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833065924821105731967639 2749598887231658597951459)
              ·
                refine ⟨4124398330847487896927189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749598887231658597951459 4124398330847487896927189)
                ·
                  refine ⟨96665585879237997584231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4124398330847487896927189 96665585879237997584231)
                  ·
                    rfl

theorem cell21_423575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_423575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423575 prefixEnd_423575 := by exact prefixLift 423575
  have htrace : WordTrace (prefixWord ++ tailWord_423575) baseStart_423575 baseEnd_423575 := by
    simpa [prefixWord, tailWord_423575, baseEnd_423575] using wordTrace_append hprefix tailTrace_423575
  have hstable : (prefixWord ++ tailWord_423575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423575).length < 2 ^ (prefixWord ++ tailWord_423575).sum := by decide
  have hdescent : baseEnd_423575 < baseStart_423575 := by decide
  rcases family_descends (prefixWord ++ tailWord_423575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423598 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_423598 : Nat := 118140960795 + 423598 * 2 ^ 59
def prefixEnd_423598 : Nat := 4983230072969 + 3 ^ 40 * 423598 * 2
def baseEnd_423598 : Nat := 96670834792595068700851

theorem tailTrace_423598 : CollatzResearch.WordTrace tailWord_423598 prefixEnd_423598 96670834792595068700851 := by
  unfold tailWord_423598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931236039923033202980931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10299925546256177082564965 1931236039923033202980931)
  ·
    refine ⟨2896854059884549804471397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1931236039923033202980931 2896854059884549804471397)
    ·
      refine ⟨543160136228353088338387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2896854059884549804471397 543160136228353088338387)
      ·
        refine ⟨814740204342529632507581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543160136228353088338387 814740204342529632507581)
        ·
          refine ⟨305527576628448612190343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814740204342529632507581 305527576628448612190343)
          ·
            refine ⟨458291364942672918285515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305527576628448612190343 458291364942672918285515)
            ·
              refine ⟨687437047414009377428273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458291364942672918285515 687437047414009377428273)
              ·
                refine ⟨515577785560507033071205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687437047414009377428273 515577785560507033071205)
                ·
                  refine ⟨96670834792595068700851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515577785560507033071205 96670834792595068700851)
                  ·
                    rfl

theorem cell21_423598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_423598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423598 prefixEnd_423598 := by exact prefixLift 423598
  have htrace : WordTrace (prefixWord ++ tailWord_423598) baseStart_423598 baseEnd_423598 := by
    simpa [prefixWord, tailWord_423598, baseEnd_423598] using wordTrace_append hprefix tailTrace_423598
  have hstable : (prefixWord ++ tailWord_423598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423598).length < 2 ^ (prefixWord ++ tailWord_423598).sum := by decide
  have hdescent : baseEnd_423598 < baseStart_423598 := by decide
  rcases family_descends (prefixWord ++ tailWord_423598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423623 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 4]
def baseStart_423623 : Nat := 118140960795 + 423623 * 2 ^ 59
def prefixEnd_423623 : Nat := 4983230072969 + 3 ^ 40 * 423623 * 2
def baseEnd_423623 : Nat := 96676540133200580784133

theorem tailTrace_423623 : CollatzResearch.WordTrace tailWord_423623 prefixEnd_423623 96676540133200580784133 := by
  unfold tailWord_423623
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450800144293694893507523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10300533429529129929005015 15450800144293694893507523)
  ·
    refine ⟨23176200216440542340261285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15450800144293694893507523 23176200216440542340261285)
    ·
      refine ⟨4345537540582601688798991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23176200216440542340261285 4345537540582601688798991)
      ·
        refine ⟨6518306310873902533198487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4345537540582601688798991 6518306310873902533198487)
        ·
          refine ⟨9777459466310853799797731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518306310873902533198487 9777459466310853799797731)
          ·
            refine ⟨14666189199466280699696597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777459466310853799797731 14666189199466280699696597)
            ·
              refine ⟨343738809362490953899139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14666189199466280699696597 343738809362490953899139)
              ·
                refine ⟨515608214043736430848709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343738809362490953899139 515608214043736430848709)
                ·
                  refine ⟨96676540133200580784133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515608214043736430848709 96676540133200580784133)
                  ·
                    rfl

theorem cell21_423623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 4].length) (baseStart_423623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423623 prefixEnd_423623 := by exact prefixLift 423623
  have htrace : WordTrace (prefixWord ++ tailWord_423623) baseStart_423623 baseEnd_423623 := by
    simpa [prefixWord, tailWord_423623, baseEnd_423623] using wordTrace_append hprefix tailTrace_423623
  have hstable : (prefixWord ++ tailWord_423623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423623).length < 2 ^ (prefixWord ++ tailWord_423623).sum := by decide
  have hdescent : baseEnd_423623 < baseStart_423623 := by decide
  rcases family_descends (prefixWord ++ tailWord_423623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423761 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 3]
def baseStart_423761 : Nat := 118140960795 + 423761 * 2 ^ 59
def prefixEnd_423761 : Nat := 4983230072969 + 3 ^ 40 * 423761 * 2
def baseEnd_423761 : Nat := 96708033613343007483851

theorem tailTrace_423761 : CollatzResearch.WordTrace tailWord_423761 prefixEnd_423761 96708033613343007483851 := by
  unfold tailWord_423761
  simp only [CollatzResearch.WordTrace]
  refine ⟨15455833417793744462031137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10303888945195829641354091 15455833417793744462031137)
  ·
    refine ⟨11591875063345308346523353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15455833417793744462031137 11591875063345308346523353)
    ·
      refine ⟨8693906297508981259892515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11591875063345308346523353 8693906297508981259892515)
      ·
        refine ⟨13040859446263471889838773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693906297508981259892515 13040859446263471889838773)
        ·
          refine ⟨1222580573087200489672385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13040859446263471889838773 1222580573087200489672385)
          ·
            refine ⟨916935429815400367254289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222580573087200489672385 916935429815400367254289)
            ·
              refine ⟨687701572361550275440717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916935429815400367254289 687701572361550275440717)
              ·
                refine ⟨257888089635581353290269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 687701572361550275440717 257888089635581353290269)
                ·
                  refine ⟨96708033613343007483851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257888089635581353290269 96708033613343007483851)
                  ·
                    rfl

theorem cell21_423761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_423761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423761 prefixEnd_423761 := by exact prefixLift 423761
  have htrace : WordTrace (prefixWord ++ tailWord_423761) baseStart_423761 baseEnd_423761 := by
    simpa [prefixWord, tailWord_423761, baseEnd_423761] using wordTrace_append hprefix tailTrace_423761
  have hstable : (prefixWord ++ tailWord_423761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423761).length < 2 ^ (prefixWord ++ tailWord_423761).sum := by decide
  have hdescent : baseEnd_423761 < baseStart_423761 := by decide
  rcases family_descends (prefixWord ++ tailWord_423761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423775 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 4]
def baseStart_423775 : Nat := 118140960795 + 423775 * 2 ^ 59
def prefixEnd_423775 : Nat := 4983230072969 + 3 ^ 40 * 423775 * 2
def baseEnd_423775 : Nat := 96711228604082094250489

theorem tailTrace_423775 : CollatzResearch.WordTrace tailWord_423775 prefixEnd_423775 96711228604082094250489 := by
  unfold tailWord_423775
  simp only [CollatzResearch.WordTrace]
  refine ⟨15456344039743024853040779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10304229359828683235360519 15456344039743024853040779)
  ·
    refine ⟨23184516059614537279561169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15456344039743024853040779 23184516059614537279561169)
    ·
      refine ⟨17388387044710902959670877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23184516059614537279561169 17388387044710902959670877)
      ·
        refine ⟨6520645141766588609876579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17388387044710902959670877 6520645141766588609876579)
        ·
          refine ⟨9780967712649882914814869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520645141766588609876579 9780967712649882914814869)
          ·
            refine ⟨458482861530463261631947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9780967712649882914814869 458482861530463261631947)
            ·
              refine ⟨687724292295694892447921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458482861530463261631947 687724292295694892447921)
              ·
                refine ⟨515793219221771169335941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687724292295694892447921 515793219221771169335941)
                ·
                  refine ⟨96711228604082094250489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515793219221771169335941 96711228604082094250489)
                  ·
                    rfl

theorem cell21_423775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].length) (baseStart_423775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423775 prefixEnd_423775 := by exact prefixLift 423775
  have htrace : WordTrace (prefixWord ++ tailWord_423775) baseStart_423775 baseEnd_423775 := by
    simpa [prefixWord, tailWord_423775, baseEnd_423775] using wordTrace_append hprefix tailTrace_423775
  have hstable : (prefixWord ++ tailWord_423775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423775).length < 2 ^ (prefixWord ++ tailWord_423775).sum := by decide
  have hdescent : baseEnd_423775 < baseStart_423775 := by decide
  rcases family_descends (prefixWord ++ tailWord_423775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423806 : List Nat := [4, 2, 3, 1, 1, 2, 1, 7]
def baseStart_423806 : Nat := 118140960795 + 423806 * 2 ^ 59
def prefixEnd_423806 : Nat := 4983230072969 + 3 ^ 40 * 423806 * 2
def baseEnd_423806 : Nat := 32239434408810976411253

theorem tailTrace_423806 : CollatzResearch.WordTrace tailWord_423806 prefixEnd_423806 32239434408810976411253 := by
  unfold tailWord_423806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932184337828839643427409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10304983135087144764946181 1932184337828839643427409)
  ·
    refine ⟨1449138253371629732570557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1932184337828839643427409 1449138253371629732570557)
    ·
      refine ⟨543426845014361149713959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1449138253371629732570557 543426845014361149713959)
      ·
        refine ⟨815140267521541724570939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543426845014361149713959 815140267521541724570939)
        ·
          refine ⟨1222710401282312586856409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815140267521541724570939 1222710401282312586856409)
          ·
            refine ⟨917032800961734440142307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222710401282312586856409 917032800961734440142307)
            ·
              refine ⟨1375549201442601660213461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917032800961734440142307 1375549201442601660213461)
              ·
                refine ⟨32239434408810976411253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1375549201442601660213461 32239434408810976411253)
                ·
                  rfl

theorem cell21_423806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_423806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423806 prefixEnd_423806 := by exact prefixLift 423806
  have htrace : WordTrace (prefixWord ++ tailWord_423806) baseStart_423806 baseEnd_423806 := by
    simpa [prefixWord, tailWord_423806, baseEnd_423806] using wordTrace_append hprefix tailTrace_423806
  have hstable : (prefixWord ++ tailWord_423806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423806).length < 2 ^ (prefixWord ++ tailWord_423806).sum := by decide
  have hdescent : baseEnd_423806 < baseStart_423806 := by decide
  rcases family_descends (prefixWord ++ tailWord_423806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423817 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_423817 : Nat := 118140960795 + 423817 * 2 ^ 59
def prefixEnd_423817 : Nat := 4983230072969 + 3 ^ 40 * 423817 * 2
def baseEnd_423817 : Nat := 96720813576299354550403

theorem tailTrace_423817 : CollatzResearch.WordTrace tailWord_423817 prefixEnd_423817 96720813576299354550403 := by
  unfold tailWord_423817
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457875905590866026069705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10305250603727244017379803 15457875905590866026069705)
  ·
    refine ⟨11593406929193149519552279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15457875905590866026069705 11593406929193149519552279)
    ·
      refine ⟨17390110393789724279328419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11593406929193149519552279 17390110393789724279328419)
      ·
        refine ⟨26085165590684586418992629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17390110393789724279328419 26085165590684586418992629)
        ·
          refine ⟨2445484274126679976780559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26085165590684586418992629 2445484274126679976780559)
          ·
            refine ⟨3668226411190019965170839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445484274126679976780559 3668226411190019965170839)
            ·
              refine ⟨5502339616785029947756259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668226411190019965170839 5502339616785029947756259)
              ·
                refine ⟨8253509425177544921634389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502339616785029947756259 8253509425177544921634389)
                ·
                  refine ⟨96720813576299354550403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8253509425177544921634389 96720813576299354550403)
                  ·
                    rfl

theorem cell21_423817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_423817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423817 prefixEnd_423817 := by exact prefixLift 423817
  have htrace : WordTrace (prefixWord ++ tailWord_423817) baseStart_423817 baseEnd_423817 := by
    simpa [prefixWord, tailWord_423817, baseEnd_423817] using wordTrace_append hprefix tailTrace_423817
  have hstable : (prefixWord ++ tailWord_423817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423817).length < 2 ^ (prefixWord ++ tailWord_423817).sum := by decide
  have hdescent : baseEnd_423817 < baseStart_423817 := by decide
  rcases family_descends (prefixWord ++ tailWord_423817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423834 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_423834 : Nat := 118140960795 + 423834 * 2 ^ 59
def prefixEnd_423834 : Nat := 4983230072969 + 3 ^ 40 * 423834 * 2
def baseEnd_423834 : Nat := 96724693207911102767035

theorem tailTrace_423834 : CollatzResearch.WordTrace tailWord_423834 prefixEnd_423834 96724693207911102767035 := by
  unfold tailWord_423834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864623986632319482359639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10305663964352851952959037 3864623986632319482359639)
  ·
    refine ⟨5796935979948479223539459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3864623986632319482359639 5796935979948479223539459)
    ·
      refine ⟨8695403969922718835309189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796935979948479223539459 8695403969922718835309189)
      ·
        refine ⟨1630388244360509781620473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8695403969922718835309189 1630388244360509781620473)
        ·
          refine ⟨1222791183270382336215355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630388244360509781620473 1222791183270382336215355)
          ·
            refine ⟨1834186774905573504323033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222791183270382336215355 1834186774905573504323033)
            ·
              refine ⟨1375640081179180128242275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834186774905573504323033 1375640081179180128242275)
              ·
                refine ⟨2063460121768770192363413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375640081179180128242275 2063460121768770192363413)
                ·
                  refine ⟨96724693207911102767035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2063460121768770192363413 96724693207911102767035)
                  ·
                    rfl

theorem cell21_423834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_423834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423834 prefixEnd_423834 := by exact prefixLift 423834
  have htrace : WordTrace (prefixWord ++ tailWord_423834) baseStart_423834 baseEnd_423834 := by
    simpa [prefixWord, tailWord_423834, baseEnd_423834] using wordTrace_append hprefix tailTrace_423834
  have hstable : (prefixWord ++ tailWord_423834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423834).length < 2 ^ (prefixWord ++ tailWord_423834).sum := by decide
  have hdescent : baseEnd_423834 < baseStart_423834 := by decide
  rcases family_descends (prefixWord ++ tailWord_423834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423896 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_423896 : Nat := 118140960795 + 423896 * 2 ^ 59
def prefixEnd_423896 : Nat := 4983230072969 + 3 ^ 40 * 423896 * 2
def baseEnd_423896 : Nat := 96738842452612772733575

theorem tailTrace_423896 : CollatzResearch.WordTrace tailWord_423896 prefixEnd_423896 96738842452612772733575 := by
  unfold tailWord_423896
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730378636152331259097771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10307171514869775012130361 7730378636152331259097771)
  ·
    refine ⟨11595567954228496888646657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7730378636152331259097771 11595567954228496888646657)
    ·
      refine ⟨8696675965671372666484993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11595567954228496888646657 8696675965671372666484993)
      ·
        refine ⟨6522506974253529499863745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8696675965671372666484993 6522506974253529499863745)
        ·
          refine ⟨4891880230690147124897809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522506974253529499863745 4891880230690147124897809)
          ·
            refine ⟨3668910173017610343673357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4891880230690147124897809 3668910173017610343673357)
            ·
              refine ⟨1375841314881603878877509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3668910173017610343673357 1375841314881603878877509)
              ·
                refine ⟨257970246540300727289533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1375841314881603878877509 257970246540300727289533)
                ·
                  refine ⟨96738842452612772733575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257970246540300727289533 96738842452612772733575)
                  ·
                    rfl

theorem cell21_423896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_423896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423896 prefixEnd_423896 := by exact prefixLift 423896
  have htrace : WordTrace (prefixWord ++ tailWord_423896) baseStart_423896 baseEnd_423896 := by
    simpa [prefixWord, tailWord_423896, baseEnd_423896] using wordTrace_append hprefix tailTrace_423896
  have hstable : (prefixWord ++ tailWord_423896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423896).length < 2 ^ (prefixWord ++ tailWord_423896).sum := by decide
  have hdescent : baseEnd_423896 < baseStart_423896 := by decide
  rcases family_descends (prefixWord ++ tailWord_423896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423975 : List Nat := [1, 1, 7, 1, 2, 2, 2, 5]
def baseStart_423975 : Nat := 118140960795 + 423975 * 2 ^ 59
def prefixEnd_423975 : Nat := 4983230072969 + 3 ^ 40 * 423975 * 2
def baseEnd_423975 : Nat := 32252290442975396972249

theorem tailTrace_423975 : CollatzResearch.WordTrace tailWord_423975 prefixEnd_423975 32252290442975396972249 := by
  unfold tailWord_423975
  simp only [CollatzResearch.WordTrace]
  refine ⟨15463638639018459010321379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10309092426012306006880919 15463638639018459010321379)
  ·
    refine ⟨23195457958527688515482069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15463638639018459010321379 23195457958527688515482069)
    ·
      refine ⟨543643545902992699581611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23195457958527688515482069 543643545902992699581611)
      ·
        refine ⟨815465318854489049372417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543643545902992699581611 815465318854489049372417)
        ·
          refine ⟨611598989140866787029313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815465318854489049372417 611598989140866787029313)
          ·
            refine ⟨458699241855650090271985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611598989140866787029313 458699241855650090271985)
            ·
              refine ⟨344024431391737567703989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458699241855650090271985 344024431391737567703989)
              ·
                refine ⟨32252290442975396972249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344024431391737567703989 32252290442975396972249)
                ·
                  rfl

theorem cell21_423975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 5].length) (baseStart_423975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_423975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_423975 prefixEnd_423975 := by exact prefixLift 423975
  have htrace : WordTrace (prefixWord ++ tailWord_423975) baseStart_423975 baseEnd_423975 := by
    simpa [prefixWord, tailWord_423975, baseEnd_423975] using wordTrace_append hprefix tailTrace_423975
  have hstable : (prefixWord ++ tailWord_423975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423975).length < 2 ^ (prefixWord ++ tailWord_423975).sum := by decide
  have hdescent : baseEnd_423975 < baseStart_423975 := by decide
  rcases family_descends (prefixWord ++ tailWord_423975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424000 : List Nat := [2, 1, 1, 2, 2, 6, 7]
def baseStart_424000 : Nat := 118140960795 + 424000 * 2 ^ 59
def prefixEnd_424000 : Nat := 4983230072969 + 3 ^ 40 * 424000 * 2
def baseEnd_424000 : Nat := 10751397407725744777781

theorem tailTrace_424000 : CollatzResearch.WordTrace tailWord_424000 prefixEnd_424000 10751397407725744777781 := by
  unfold tailWord_424000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732275231963944139990727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10309700309285258853320969 7732275231963944139990727)
  ·
    refine ⟨11598412847945916209986091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7732275231963944139990727 11598412847945916209986091)
    ·
      refine ⟨17397619271918874314979137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11598412847945916209986091 17397619271918874314979137)
      ·
        refine ⟨13048214453939155736234353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17397619271918874314979137 13048214453939155736234353)
        ·
          refine ⟨9786160840454366802175765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13048214453939155736234353 9786160840454366802175765)
          ·
            refine ⟨458726289396298443851989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9786160840454366802175765 458726289396298443851989)
            ·
              refine ⟨10751397407725744777781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 458726289396298443851989 10751397407725744777781)
              ·
                rfl

theorem cell21_424000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 7].length) (baseStart_424000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424000 prefixEnd_424000 := by exact prefixLift 424000
  have htrace : WordTrace (prefixWord ++ tailWord_424000) baseStart_424000 baseEnd_424000 := by
    simpa [prefixWord, tailWord_424000, baseEnd_424000] using wordTrace_append hprefix tailTrace_424000
  have hstable : (prefixWord ++ tailWord_424000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424000).length < 2 ^ (prefixWord ++ tailWord_424000).sum := by decide
  have hdescent : baseEnd_424000 < baseStart_424000 := by decide
  rcases family_descends (prefixWord ++ tailWord_424000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424065 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 3]
def baseStart_424065 : Nat := 118140960795 + 424065 * 2 ^ 59
def prefixEnd_424065 : Nat := 4983230072969 + 3 ^ 40 * 424065 * 2
def baseEnd_424065 : Nat := 96777410555106034416563

theorem tailTrace_424065 : CollatzResearch.WordTrace tailWord_424065 prefixEnd_424065 96777410555106034416563 := by
  unfold tailWord_424065
  simp only [CollatzResearch.WordTrace]
  refine ⟨15466921208692404381097649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10311280805794936254065099 15466921208692404381097649)
  ·
    refine ⟨11600190906519303285823237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15466921208692404381097649 11600190906519303285823237)
    ·
      refine ⟨2175035794972369366091857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11600190906519303285823237 2175035794972369366091857)
      ·
        refine ⟨1631276846229277024568893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2175035794972369366091857 1631276846229277024568893)
        ·
          refine ⟨611728817335978884213335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1631276846229277024568893 611728817335978884213335)
          ·
            refine ⟨917593226003968326320003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611728817335978884213335 917593226003968326320003)
            ·
              refine ⟨1376389839005952489480005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917593226003968326320003 1376389839005952489480005)
              ·
                refine ⟨258073094813616091777501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1376389839005952489480005 258073094813616091777501)
                ·
                  refine ⟨96777410555106034416563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258073094813616091777501 96777410555106034416563)
                  ·
                    rfl

theorem cell21_424065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_424065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424065 prefixEnd_424065 := by exact prefixLift 424065
  have htrace : WordTrace (prefixWord ++ tailWord_424065) baseStart_424065 baseEnd_424065 := by
    simpa [prefixWord, tailWord_424065, baseEnd_424065] using wordTrace_append hprefix tailTrace_424065
  have hstable : (prefixWord ++ tailWord_424065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424065).length < 2 ^ (prefixWord ++ tailWord_424065).sum := by decide
  have hdescent : baseEnd_424065 < baseStart_424065 := by decide
  rcases family_descends (prefixWord ++ tailWord_424065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
