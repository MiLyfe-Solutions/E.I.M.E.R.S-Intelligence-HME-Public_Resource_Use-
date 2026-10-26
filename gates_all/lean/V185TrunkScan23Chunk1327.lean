import V185TrunkScan23Chunk1326

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7860426 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_7860426 : Nat := 118140960795 + 7860426 * 2 ^ 59
def prefixEnd_7860426 : Nat := 4983230072969 + 3 ^ 40 * 7860426 * 2
def baseEnd_7860426 : Nat := 4036176687098168280825565

theorem tailTrace_7860426 : CollatzResearch.WordTrace tailWord_7860426 prefixEnd_7860426 4036176687098168280825565 := by
  unfold tailWord_7860426
  simp only [CollatzResearch.WordTrace]
  refine ⟨71673322255256632681924283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191128859347351020485131421 71673322255256632681924283)
  ·
    refine ⟨107509983382884949022886425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71673322255256632681924283 107509983382884949022886425)
    ·
      refine ⟨80632487537163711767164819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107509983382884949022886425 80632487537163711767164819)
      ·
        refine ⟨120948731305745567650747229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80632487537163711767164819 120948731305745567650747229)
        ·
          refine ⟨45355774239654587869030211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120948731305745567650747229 45355774239654587869030211)
          ·
            refine ⟨68033661359481881803545317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45355774239654587869030211 68033661359481881803545317)
            ·
              refine ⟨12756311504902852838164747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68033661359481881803545317 12756311504902852838164747)
              ·
                refine ⟨19134467257354279257247121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12756311504902852838164747 19134467257354279257247121)
                ·
                  refine ⟨14350850443015709442935341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19134467257354279257247121 14350850443015709442935341)
                  ·
                    refine ⟨5381568916130891041100753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14350850443015709442935341 5381568916130891041100753)
                    ·
                      refine ⟨4036176687098168280825565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381568916130891041100753 4036176687098168280825565)
                      ·
                        rfl

theorem cell23_7860426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_7860426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860426 prefixEnd_7860426 := by exact prefixLift 7860426
  have htrace : WordTrace (prefixWord ++ tailWord_7860426) baseStart_7860426 baseEnd_7860426 := by
    simpa [prefixWord, tailWord_7860426, baseEnd_7860426] using wordTrace_append hprefix tailTrace_7860426
  have hstable : (prefixWord ++ tailWord_7860426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860426).length < 2 ^ (prefixWord ++ tailWord_7860426).sum := by decide
  have hdescent : baseEnd_7860426 < baseStart_7860426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860444 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7860444 : Nat := 118140960795 + 7860444 * 2 ^ 59
def prefixEnd_7860444 : Nat := 4983230072969 + 3 ^ 40 * 7860444 * 2
def baseEnd_7860444 : Nat := 1345395309916649736800161

theorem tailTrace_7860444 : CollatzResearch.WordTrace tailWord_7860444 prefixEnd_7860444 1345395309916649736800161 := by
  unfold tailWord_7860444
  simp only [CollatzResearch.WordTrace]
  refine ⟨143346972767480659900926193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191129297023307546534568257 143346972767480659900926193)
  ·
    refine ⟨107510229575610494925694645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143346972767480659900926193 107510229575610494925694645)
    ·
      refine ⟨10079084022713483899283873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107510229575610494925694645 10079084022713483899283873)
      ·
        refine ⟨7559313017035112924462905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10079084022713483899283873 7559313017035112924462905)
        ·
          refine ⟨5669484762776334693347179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7559313017035112924462905 5669484762776334693347179)
          ·
            refine ⟨8504227144164502040020769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669484762776334693347179 8504227144164502040020769)
            ·
              refine ⟨6378170358123376530015577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8504227144164502040020769 6378170358123376530015577)
              ·
                refine ⟨4783627768592532397511683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378170358123376530015577 4783627768592532397511683)
                ·
                  refine ⟨7175441652888798596267525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783627768592532397511683 7175441652888798596267525)
                  ·
                    refine ⟨1345395309916649736800161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175441652888798596267525 1345395309916649736800161)
                    ·
                      rfl

theorem cell23_7860444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7860444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860444 prefixEnd_7860444 := by exact prefixLift 7860444
  have htrace : WordTrace (prefixWord ++ tailWord_7860444) baseStart_7860444 baseEnd_7860444 := by
    simpa [prefixWord, tailWord_7860444, baseEnd_7860444] using wordTrace_append hprefix tailTrace_7860444
  have hstable : (prefixWord ++ tailWord_7860444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860444).length < 2 ^ (prefixWord ++ tailWord_7860444).sum := by decide
  have hdescent : baseEnd_7860444 < baseStart_7860444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860452 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7860452 : Nat := 118140960795 + 7860452 * 2 ^ 59
def prefixEnd_7860452 : Nat := 4983230072969 + 3 ^ 40 * 7860452 * 2
def baseEnd_7860452 : Nat := 4036190037595185179100445

theorem tailTrace_7860452 : CollatzResearch.WordTrace tailWord_7860452 prefixEnd_7860452 4036190037595185179100445 := by
  unfold tailWord_7860452
  simp only [CollatzResearch.WordTrace]
  refine ⟨143347118659466168584071805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191129491545954891445429073 143347118659466168584071805)
  ·
    refine ⟨53755169497299813219026927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143347118659466168584071805 53755169497299813219026927)
    ·
      refine ⟨80632754245949719828540391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53755169497299813219026927 80632754245949719828540391)
      ·
        refine ⟨120949131368924579742810587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80632754245949719828540391 120949131368924579742810587)
        ·
          refine ⟨181423697053386869614215881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120949131368924579742810587 181423697053386869614215881)
          ·
            refine ⟨136067772790040152210661911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181423697053386869614215881 136067772790040152210661911)
            ·
              refine ⟨204101659185060228315992867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136067772790040152210661911 204101659185060228315992867)
              ·
                refine ⟨306152488777590342473989301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204101659185060228315992867 306152488777590342473989301)
                ·
                  refine ⟨28701795822899094606936497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306152488777590342473989301 28701795822899094606936497)
                  ·
                    refine ⟨21526346867174320955202373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28701795822899094606936497 21526346867174320955202373)
                    ·
                      refine ⟨4036190037595185179100445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21526346867174320955202373 4036190037595185179100445)
                      ·
                        rfl

theorem cell23_7860452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7860452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860452 prefixEnd_7860452 := by exact prefixLift 7860452
  have htrace : WordTrace (prefixWord ++ tailWord_7860452) baseStart_7860452 baseEnd_7860452 := by
    simpa [prefixWord, tailWord_7860452, baseEnd_7860452] using wordTrace_append hprefix tailTrace_7860452
  have hstable : (prefixWord ++ tailWord_7860452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860452).length < 2 ^ (prefixWord ++ tailWord_7860452).sum := by decide
  have hdescent : baseEnd_7860452 < baseStart_7860452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860466 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_7860466 : Nat := 118140960795 + 7860466 * 2 ^ 59
def prefixEnd_7860466 : Nat := 4983230072969 + 3 ^ 40 * 7860466 * 2
def baseEnd_7860466 : Nat := 1345399075441449374775127

theorem tailTrace_7860466 : CollatzResearch.WordTrace tailWord_7860466 prefixEnd_7860466 1345399075441449374775127 := by
  unfold tailWord_7860466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71673686985220404389788313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191129831960587745039435501 71673686985220404389788313)
  ·
    refine ⟨53755265238915303292341235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71673686985220404389788313 53755265238915303292341235)
    ·
      refine ⟨80632897858372954938511853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53755265238915303292341235 80632897858372954938511853)
      ·
        refine ⟨30237336696889858101941945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80632897858372954938511853 30237336696889858101941945)
        ·
          refine ⟨22678002522667393576456459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30237336696889858101941945 22678002522667393576456459)
          ·
            refine ⟨34017003784001090364684689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22678002522667393576456459 34017003784001090364684689)
            ·
              refine ⟨25512752838000817773513517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34017003784001090364684689 25512752838000817773513517)
              ·
                refine ⟨9567282314250306665067569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25512752838000817773513517 9567282314250306665067569)
                ·
                  refine ⟨7175461735687729998800677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9567282314250306665067569 7175461735687729998800677)
                  ·
                    refine ⟨1345399075441449374775127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175461735687729998800677 1345399075441449374775127)
                    ·
                      rfl

theorem cell23_7860466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_7860466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860466 prefixEnd_7860466 := by exact prefixLift 7860466
  have htrace : WordTrace (prefixWord ++ tailWord_7860466) baseStart_7860466 baseEnd_7860466 := by
    simpa [prefixWord, tailWord_7860466, baseEnd_7860466] using wordTrace_append hprefix tailTrace_7860466
  have hstable : (prefixWord ++ tailWord_7860466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860466).length < 2 ^ (prefixWord ++ tailWord_7860466).sum := by decide
  have hdescent : baseEnd_7860466 < baseStart_7860466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860489 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_7860489 : Nat := 118140960795 + 7860489 * 2 ^ 59
def prefixEnd_7860489 : Nat := 4983230072969 + 3 ^ 40 * 7860489 * 2
def baseEnd_7860489 : Nat := 4036209036379401534337775

theorem tailTrace_7860489 : CollatzResearch.WordTrace tailWord_7860489 prefixEnd_7860489 4036209036379401534337775 := by
  unfold tailWord_7860489
  simp only [CollatzResearch.WordTrace]
  refine ⟨286695586819798292487240521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191130391213198861658160347 286695586819798292487240521)
  ·
    refine ⟨215021690114848719365430391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286695586819798292487240521 215021690114848719365430391)
    ·
      refine ⟨322532535172273079048145587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215021690114848719365430391 322532535172273079048145587)
      ·
        refine ⟨483798802758409618572218381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322532535172273079048145587 483798802758409618572218381)
        ·
          refine ⟨181424551034403606964581893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483798802758409618572218381 181424551034403606964581893)
          ·
            refine ⟨34017103318950676305859105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181424551034403606964581893 34017103318950676305859105)
            ·
              refine ⟨25512827489213007229394329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34017103318950676305859105 25512827489213007229394329)
              ·
                refine ⟨19134620616909755422045747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25512827489213007229394329 19134620616909755422045747)
                ·
                  refine ⟨28701930925364633133068621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19134620616909755422045747 28701930925364633133068621)
                  ·
                    refine ⟨10763224097011737424900733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28701930925364633133068621 10763224097011737424900733)
                    ·
                      refine ⟨4036209036379401534337775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763224097011737424900733 4036209036379401534337775)
                      ·
                        rfl

theorem cell23_7860489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_7860489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860489 prefixEnd_7860489 := by exact prefixLift 7860489
  have htrace : WordTrace (prefixWord ++ tailWord_7860489) baseStart_7860489 baseEnd_7860489 := by
    simpa [prefixWord, tailWord_7860489, baseEnd_7860489] using wordTrace_append hprefix tailTrace_7860489
  have hstable : (prefixWord ++ tailWord_7860489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860489).length < 2 ^ (prefixWord ++ tailWord_7860489).sum := by decide
  have hdescent : baseEnd_7860489 < baseStart_7860489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860533 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_7860533 : Nat := 118140960795 + 7860533 * 2 ^ 59
def prefixEnd_7860533 : Nat := 4983230072969 + 3 ^ 40 * 7860533 * 2
def baseEnd_7860533 : Nat := 4036231629528199362187573

theorem tailTrace_7860533 : CollatzResearch.WordTrace tailWord_7860533 prefixEnd_7860533 4036231629528199362187573 := by
  unfold tailWord_7860533
  simp only [CollatzResearch.WordTrace]
  refine ⟨286697191631638888001842253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191131461087759258667894835 286697191631638888001842253)
  ·
    refine ⟨107511446861864583000690845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286697191631638888001842253 107511446861864583000690845)
    ·
      refine ⟨40316792573199218625259067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107511446861864583000690845 40316792573199218625259067)
      ·
        refine ⟨60475188859798827937888601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40316792573199218625259067 60475188859798827937888601)
        ·
          refine ⟨45356391644849120953416451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60475188859798827937888601 45356391644849120953416451)
          ·
            refine ⟨68034587467273681430124677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45356391644849120953416451 68034587467273681430124677)
            ·
              refine ⟨12756485150113815268148377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68034587467273681430124677 12756485150113815268148377)
              ·
                refine ⟨9567363862585361451111283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12756485150113815268148377 9567363862585361451111283)
                ·
                  refine ⟨14351045793878042176666925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9567363862585361451111283 14351045793878042176666925)
                  ·
                    refine ⟨5381642172704265816250097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14351045793878042176666925 5381642172704265816250097)
                    ·
                      refine ⟨4036231629528199362187573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381642172704265816250097 4036231629528199362187573)
                      ·
                        rfl

theorem cell23_7860533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_7860533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860533 prefixEnd_7860533 := by exact prefixLift 7860533
  have htrace : WordTrace (prefixWord ++ tailWord_7860533) baseStart_7860533 baseEnd_7860533 := by
    simpa [prefixWord, tailWord_7860533, baseEnd_7860533] using wordTrace_append hprefix tailTrace_7860533
  have hstable : (prefixWord ++ tailWord_7860533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860533).length < 2 ^ (prefixWord ++ tailWord_7860533).sum := by decide
  have hdescent : baseEnd_7860533 < baseStart_7860533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860552 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 9]
def baseStart_7860552 : Nat := 118140960795 + 7860552 * 2 ^ 59
def prefixEnd_7860552 : Nat := 4983230072969 + 3 ^ 40 * 7860552 * 2
def baseEnd_7860552 : Nat := 448471265073403865316665

theorem tailTrace_7860552 : CollatzResearch.WordTrace tailWord_7860552 prefixEnd_7860552 448471265073403865316665 := by
  unfold tailWord_7860552
  simp only [CollatzResearch.WordTrace]
  refine ⟨143348942309285027123391955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191131923079046702831189273 143348942309285027123391955)
  ·
    refine ⟨215023413463927540685087933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143348942309285027123391955 215023413463927540685087933)
    ·
      refine ⟨80633780048972827756907975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215023413463927540685087933 80633780048972827756907975)
      ·
        refine ⟨120950670073459241635361963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80633780048972827756907975 120950670073459241635361963)
        ·
          refine ⟨181426005110188862453042945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120950670073459241635361963 181426005110188862453042945)
          ·
            refine ⟨136069503832641646839782209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181426005110188862453042945 136069503832641646839782209)
            ·
              refine ⟨102052127874481235129836657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136069503832641646839782209 102052127874481235129836657)
              ·
                refine ⟨76539095905860926347377493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102052127874481235129836657 76539095905860926347377493)
                ·
                  refine ⟨448471265073403865316665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76539095905860926347377493 448471265073403865316665)
                  ·
                    rfl

theorem cell23_7860552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_7860552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860552 prefixEnd_7860552 := by exact prefixLift 7860552
  have htrace : WordTrace (prefixWord ++ tailWord_7860552) baseStart_7860552 baseEnd_7860552 := by
    simpa [prefixWord, tailWord_7860552, baseEnd_7860552] using wordTrace_append hprefix tailTrace_7860552
  have hstable : (prefixWord ++ tailWord_7860552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860552).length < 2 ^ (prefixWord ++ tailWord_7860552).sum := by decide
  have hdescent : baseEnd_7860552 < baseStart_7860552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860579 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 3]
def baseStart_7860579 : Nat := 118140960795 + 7860579 * 2 ^ 59
def prefixEnd_7860579 : Nat := 4983230072969 + 3 ^ 40 * 7860579 * 2
def baseEnd_7860579 : Nat := 4036255249638306182212361

theorem tailTrace_7860579 : CollatzResearch.WordTrace tailWord_7860579 prefixEnd_7860579 4036255249638306182212361 := by
  unfold tailWord_7860579
  simp only [CollatzResearch.WordTrace]
  refine ⟨286698869389472237858016791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191132579592981491905344527 286698869389472237858016791)
  ·
    refine ⟨430048304084208356787025187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286698869389472237858016791 430048304084208356787025187)
    ·
      refine ⟨645072456126312535180537781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430048304084208356787025187 645072456126312535180537781)
      ·
        refine ⟨60475542761841800173175417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 645072456126312535180537781 60475542761841800173175417)
        ·
          refine ⟨45356657071381350129881563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60475542761841800173175417 45356657071381350129881563)
          ·
            refine ⟨68034985607072025194822345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45356657071381350129881563 68034985607072025194822345)
            ·
              refine ⟨51026239205304018896116759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68034985607072025194822345 51026239205304018896116759)
              ·
                refine ⟨76539358807956028344175139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51026239205304018896116759 76539358807956028344175139)
                ·
                  refine ⟨114809038211934042516262709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76539358807956028344175139 114809038211934042516262709)
                  ·
                    refine ⟨10763347332368816485899629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114809038211934042516262709 10763347332368816485899629)
                    ·
                      refine ⟨4036255249638306182212361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763347332368816485899629 4036255249638306182212361)
                      ·
                        rfl

theorem cell23_7860579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_7860579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860579 prefixEnd_7860579 := by exact prefixLift 7860579
  have htrace : WordTrace (prefixWord ++ tailWord_7860579) baseStart_7860579 baseEnd_7860579 := by
    simpa [prefixWord, tailWord_7860579, baseEnd_7860579] using wordTrace_append hprefix tailTrace_7860579
  have hstable : (prefixWord ++ tailWord_7860579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860579).length < 2 ^ (prefixWord ++ tailWord_7860579).sum := by decide
  have hdescent : baseEnd_7860579 < baseStart_7860579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860650 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7860650 : Nat := 118140960795 + 7860650 * 2 ^ 59
def prefixEnd_7860650 : Nat := 4983230072969 + 3 ^ 40 * 7860650 * 2
def baseEnd_7860650 : Nat := 1345430568921591801474845

theorem tailTrace_7860650 : CollatzResearch.WordTrace tailWord_7860650 prefixEnd_7860650 1345430568921591801474845 := by
  unfold tailWord_7860650
  simp only [CollatzResearch.WordTrace]
  refine ⟨71675364743053754245962851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191134305981476677989234269 71675364743053754245962851)
  ·
    refine ⟨107513047114580631368944277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71675364743053754245962851 107513047114580631368944277)
    ·
      refine ⟨5039674083495967095419263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107513047114580631368944277 5039674083495967095419263)
      ·
        refine ⟨7559511125243950643128895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5039674083495967095419263 7559511125243950643128895)
        ·
          refine ⟨11339266687865925964693343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559511125243950643128895 11339266687865925964693343)
          ·
            refine ⟨17008900031798888947040015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339266687865925964693343 17008900031798888947040015)
            ·
              refine ⟨25513350047698333420560023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17008900031798888947040015 25513350047698333420560023)
              ·
                refine ⟨38270025071547500130840035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25513350047698333420560023 38270025071547500130840035)
                ·
                  refine ⟨57405037607321250196260053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38270025071547500130840035 57405037607321250196260053)
                  ·
                    refine ⟨1345430568921591801474845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57405037607321250196260053 1345430568921591801474845)
                    ·
                      rfl

theorem cell23_7860650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7860650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860650 prefixEnd_7860650 := by exact prefixLift 7860650
  have htrace : WordTrace (prefixWord ++ tailWord_7860650) baseStart_7860650 baseEnd_7860650 := by
    simpa [prefixWord, tailWord_7860650, baseEnd_7860650] using wordTrace_append hprefix tailTrace_7860650
  have hstable : (prefixWord ++ tailWord_7860650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860650).length < 2 ^ (prefixWord ++ tailWord_7860650).sum := by decide
  have hdescent : baseEnd_7860650 < baseStart_7860650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860653 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7860653 : Nat := 118140960795 + 7860653 * 2 ^ 59
def prefixEnd_7860653 : Nat := 4983230072969 + 3 ^ 40 * 7860653 * 2
def baseEnd_7860653 : Nat := 4036293247206738892687021

theorem tailTrace_7860653 : CollatzResearch.WordTrace tailWord_7860653 prefixEnd_7860653 4036293247206738892687021 := by
  unfold tailWord_7860653
  simp only [CollatzResearch.WordTrace]
  refine ⟨286701568391204148496210613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191134378927469432330807075 286701568391204148496210613)
  ·
    refine ⟨26878272036675388921519745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286701568391204148496210613 26878272036675388921519745)
    ·
      refine ⟨20158704027506541691139809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26878272036675388921519745 20158704027506541691139809)
      ·
        refine ⟨15119028020629906268354857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20158704027506541691139809 15119028020629906268354857)
        ·
          refine ⟨11339271015472429701266143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15119028020629906268354857 11339271015472429701266143)
          ·
            refine ⟨17008906523208644551899215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339271015472429701266143 17008906523208644551899215)
            ·
              refine ⟨25513359784812966827848823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17008906523208644551899215 25513359784812966827848823)
              ·
                refine ⟨38270039677219450241773235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25513359784812966827848823 38270039677219450241773235)
                ·
                  refine ⟨57405059515829175362659853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38270039677219450241773235 57405059515829175362659853)
                  ·
                    refine ⟨21526897318435940760997445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57405059515829175362659853 21526897318435940760997445)
                    ·
                      refine ⟨4036293247206738892687021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21526897318435940760997445 4036293247206738892687021)
                      ·
                        rfl

theorem cell23_7860653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7860653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860653 prefixEnd_7860653 := by exact prefixLift 7860653
  have htrace : WordTrace (prefixWord ++ tailWord_7860653) baseStart_7860653 baseEnd_7860653 := by
    simpa [prefixWord, tailWord_7860653, baseEnd_7860653] using wordTrace_append hprefix tailTrace_7860653
  have hstable : (prefixWord ++ tailWord_7860653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860653).length < 2 ^ (prefixWord ++ tailWord_7860653).sum := by decide
  have hdescent : baseEnd_7860653 < baseStart_7860653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860663 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 1, 4]
def baseStart_7860663 : Nat := 118140960795 + 7860663 * 2 ^ 59
def prefixEnd_7860663 : Nat := 4983230072969 + 3 ^ 40 * 7860663 * 2
def baseEnd_7860663 : Nat := 1345432794004427951187325

theorem tailTrace_7860663 : CollatzResearch.WordTrace tailWord_7860663 prefixEnd_7860663 1345432794004427951187325 := by
  unfold tailWord_7860663
  simp only [CollatzResearch.WordTrace]
  refine ⟨286701933121167920204074643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191134622080778613469383095 286701933121167920204074643)
  ·
    refine ⟨430052899681751880306111965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286701933121167920204074643 430052899681751880306111965)
    ·
      refine ⟨161269837380656955114791987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430052899681751880306111965 161269837380656955114791987)
      ·
        refine ⟨241904756070985432672187981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161269837380656955114791987 241904756070985432672187981)
        ·
          refine ⟨90714283526619537252070493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241904756070985432672187981 90714283526619537252070493)
          ·
            refine ⟨34017856322482326469526435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90714283526619537252070493 34017856322482326469526435)
            ·
              refine ⟨51026784483723489704289653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34017856322482326469526435 51026784483723489704289653)
              ·
                refine ⟨4783761045349077159777155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51026784483723489704289653 4783761045349077159777155)
                ·
                  refine ⟨7175641568023615739665733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783761045349077159777155 7175641568023615739665733)
                  ·
                    refine ⟨1345432794004427951187325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175641568023615739665733 1345432794004427951187325)
                    ·
                      rfl

theorem cell23_7860663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_7860663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860663 prefixEnd_7860663 := by exact prefixLift 7860663
  have htrace : WordTrace (prefixWord ++ tailWord_7860663) baseStart_7860663 baseEnd_7860663 := by
    simpa [prefixWord, tailWord_7860663, baseEnd_7860663] using wordTrace_append hprefix tailTrace_7860663
  have hstable : (prefixWord ++ tailWord_7860663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860663).length < 2 ^ (prefixWord ++ tailWord_7860663).sum := by decide
  have hdescent : baseEnd_7860663 < baseStart_7860663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860679 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_7860679 : Nat := 118140960795 + 7860679 * 2 ^ 59
def prefixEnd_7860679 : Nat := 4983230072969 + 3 ^ 40 * 7860679 * 2
def baseEnd_7860679 : Nat := 4036306597703755790961901

theorem tailTrace_7860679 : CollatzResearch.WordTrace tailWord_7860679 prefixEnd_7860679 4036306597703755790961901 := by
  unfold tailWord_7860679
  simp only [CollatzResearch.WordTrace]
  refine ⟨286702516689109954936657091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191135011126073303291104727 286702516689109954936657091)
  ·
    refine ⟨430053775033664932404985637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286702516689109954936657091 430053775033664932404985637)
    ·
      refine ⟨80635082818812174825934807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430053775033664932404985637 80635082818812174825934807)
      ·
        refine ⟨120952624228218262238902211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80635082818812174825934807 120952624228218262238902211)
        ·
          refine ⟨181428936342327393358353317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120952624228218262238902211 181428936342327393358353317)
          ·
            refine ⟨34017925564186386254691247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181428936342327393358353317 34017925564186386254691247)
            ·
              refine ⟨51026888346279579382036871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34017925564186386254691247 51026888346279579382036871)
              ·
                refine ⟨76540332519419369073055307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51026888346279579382036871 76540332519419369073055307)
                ·
                  refine ⟨114810498779129053609582961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76540332519419369073055307 114810498779129053609582961)
                  ·
                    refine ⟨86107874084346790207187221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114810498779129053609582961 86107874084346790207187221)
                    ·
                      refine ⟨4036306597703755790961901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86107874084346790207187221 4036306597703755790961901)
                      ·
                        rfl

theorem cell23_7860679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_7860679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860679 prefixEnd_7860679 := by exact prefixLift 7860679
  have htrace : WordTrace (prefixWord ++ tailWord_7860679) baseStart_7860679 baseEnd_7860679 := by
    simpa [prefixWord, tailWord_7860679, baseEnd_7860679] using wordTrace_append hprefix tailTrace_7860679
  have hstable : (prefixWord ++ tailWord_7860679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860679).length < 2 ^ (prefixWord ++ tailWord_7860679).sum := by decide
  have hdescent : baseEnd_7860679 < baseStart_7860679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860689 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_7860689 : Nat := 118140960795 + 7860689 * 2 ^ 59
def prefixEnd_7860689 : Nat := 4983230072969 + 3 ^ 40 * 7860689 * 2
def baseEnd_7860689 : Nat := 1345437244170100250612285

theorem tailTrace_7860689 : CollatzResearch.WordTrace tailWord_7860689 prefixEnd_7860689 1345437244170100250612285 := by
  unfold tailWord_7860689
  simp only [CollatzResearch.WordTrace]
  refine ⟨286702881419073726644521121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191135254279382484429680747 286702881419073726644521121)
  ·
    refine ⟨215027161064305294983390841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286702881419073726644521121 215027161064305294983390841)
    ·
      refine ⟨161270370798228971237543131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215027161064305294983390841 161270370798228971237543131)
      ·
        refine ⟨241905556197343456856314697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161270370798228971237543131 241905556197343456856314697)
        ·
          refine ⟨181429167148007592642236023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241905556197343456856314697 181429167148007592642236023)
          ·
            refine ⟨272143750722011388963354035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181429167148007592642236023 272143750722011388963354035)
            ·
              refine ⟨408215626083017083445031053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272143750722011388963354035 408215626083017083445031053)
              ·
                refine ⟨153080859781131406291886645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408215626083017083445031053 153080859781131406291886645)
                ·
                  refine ⟨14351330604481069339864373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153080859781131406291886645 14351330604481069339864373)
                  ·
                    refine ⟨1345437244170100250612285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14351330604481069339864373 1345437244170100250612285)
                    ·
                      rfl

theorem cell23_7860689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_7860689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860689 prefixEnd_7860689 := by exact prefixLift 7860689
  have htrace : WordTrace (prefixWord ++ tailWord_7860689) baseStart_7860689 baseEnd_7860689 := by
    simpa [prefixWord, tailWord_7860689, baseEnd_7860689] using wordTrace_append hprefix tailTrace_7860689
  have hstable : (prefixWord ++ tailWord_7860689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860689).length < 2 ^ (prefixWord ++ tailWord_7860689).sum := by decide
  have hdescent : baseEnd_7860689 < baseStart_7860689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860693 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 6]
def baseStart_7860693 : Nat := 118140960795 + 7860693 * 2 ^ 59
def prefixEnd_7860693 : Nat := 4983230072969 + 3 ^ 40 * 7860693 * 2
def baseEnd_7860693 : Nat := 448479309603657637354093

theorem tailTrace_7860693 : CollatzResearch.WordTrace tailWord_7860693 prefixEnd_7860693 448479309603657637354093 := by
  unfold tailWord_7860693
  simp only [CollatzResearch.WordTrace]
  refine ⟨286703027311059235327666733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191135351540706156885111155 286703027311059235327666733)
  ·
    refine ⟨107513635241647213247875025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286703027311059235327666733 107513635241647213247875025)
    ·
      refine ⟨80635226431235409935906269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107513635241647213247875025 80635226431235409935906269)
      ·
        refine ⟨30238209911713278725964851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80635226431235409935906269 30238209911713278725964851)
        ·
          refine ⟨45357314867569918088947277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30238209911713278725964851 45357314867569918088947277)
          ·
            refine ⟨17008993075338719283355229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45357314867569918088947277 17008993075338719283355229)
            ·
              refine ⟨6378372403252019731258211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17008993075338719283355229 6378372403252019731258211)
              ·
                refine ⟨9567558604878029596887317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378372403252019731258211 9567558604878029596887317)
                ·
                  refine ⟨448479309603657637354093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9567558604878029596887317 448479309603657637354093)
                  ·
                    rfl

theorem cell23_7860693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_7860693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860693 prefixEnd_7860693 := by exact prefixLift 7860693
  have htrace : WordTrace (prefixWord ++ tailWord_7860693) baseStart_7860693 baseEnd_7860693 := by
    simpa [prefixWord, tailWord_7860693, baseEnd_7860693] using wordTrace_append hprefix tailTrace_7860693
  have hstable : (prefixWord ++ tailWord_7860693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860693).length < 2 ^ (prefixWord ++ tailWord_7860693).sum := by decide
  have hdescent : baseEnd_7860693 < baseStart_7860693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860703 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 3]
def baseStart_7860703 : Nat := 118140960795 + 7860703 * 2 ^ 59
def prefixEnd_7860703 : Nat := 4983230072969 + 3 ^ 40 * 7860703 * 2
def baseEnd_7860703 : Nat := 4036318921239463697061791

theorem tailTrace_7860703 : CollatzResearch.WordTrace tailWord_7860703 prefixEnd_7860703 4036318921239463697061791 := by
  unfold tailWord_7860703
  simp only [CollatzResearch.WordTrace]
  refine ⟨286703392041023007035530763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191135594694015338023687175 286703392041023007035530763)
  ·
    refine ⟨430055088061534510553296145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286703392041023007035530763 430055088061534510553296145)
    ·
      refine ⟨322541316046150882914972109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430055088061534510553296145 322541316046150882914972109)
      ·
        refine ⟨120952993517306581093114541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322541316046150882914972109 120952993517306581093114541)
        ·
          refine ⟨45357372568989967909917953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120952993517306581093114541 45357372568989967909917953)
          ·
            refine ⟨34018029426742475932438465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45357372568989967909917953 34018029426742475932438465)
            ·
              refine ⟨25513522070056856949328849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34018029426742475932438465 25513522070056856949328849)
              ·
                refine ⟨19135141552542642711996637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25513522070056856949328849 19135141552542642711996637)
                ·
                  refine ⟨7175678082203491016998739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19135141552542642711996637 7175678082203491016998739)
                  ·
                    refine ⟨10763517123305236525498109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175678082203491016998739 10763517123305236525498109)
                    ·
                      refine ⟨4036318921239463697061791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763517123305236525498109 4036318921239463697061791)
                      ·
                        rfl

theorem cell23_7860703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_7860703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860703 prefixEnd_7860703 := by exact prefixLift 7860703
  have htrace : WordTrace (prefixWord ++ tailWord_7860703) baseStart_7860703 baseEnd_7860703 := by
    simpa [prefixWord, tailWord_7860703, baseEnd_7860703] using wordTrace_append hprefix tailTrace_7860703
  have hstable : (prefixWord ++ tailWord_7860703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860703).length < 2 ^ (prefixWord ++ tailWord_7860703).sum := by decide
  have hdescent : baseEnd_7860703 < baseStart_7860703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860719 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 3, 6]
def baseStart_7860719 : Nat := 118140960795 + 7860719 * 2 ^ 59
def prefixEnd_7860719 : Nat := 4983230072969 + 3 ^ 40 * 7860719 * 2
def baseEnd_7860719 : Nat := 1345442378976645211487239

theorem tailTrace_7860719 : CollatzResearch.WordTrace tailWord_7860719 prefixEnd_7860719 1345442378976645211487239 := by
  unfold tailWord_7860719
  simp only [CollatzResearch.WordTrace]
  refine ⟨286703975608965041768113211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191135983739310027845408807 286703975608965041768113211)
  ·
    refine ⟨430055963413447562652169817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286703975608965041768113211 430055963413447562652169817)
    ·
      refine ⟨322541972560085671989127363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430055963413447562652169817 322541972560085671989127363)
      ·
        refine ⟨483812958840128507983691045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322541972560085671989127363 483812958840128507983691045)
        ·
          refine ⟨90714929782524095246942071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483812958840128507983691045 90714929782524095246942071)
          ·
            refine ⟨136072394673786142870413107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90714929782524095246942071 136072394673786142870413107)
            ·
              refine ⟨204108592010679214305619661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136072394673786142870413107 204108592010679214305619661)
              ·
                refine ⟨76540722004004705364607373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204108592010679214305619661 76540722004004705364607373)
                ·
                  refine ⟨28702770751501764511727765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76540722004004705364607373 28702770751501764511727765)
                  ·
                    refine ⟨1345442378976645211487239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28702770751501764511727765 1345442378976645211487239)
                    ·
                      rfl

theorem cell23_7860719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_7860719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860719 prefixEnd_7860719 := by exact prefixLift 7860719
  have htrace : WordTrace (prefixWord ++ tailWord_7860719) baseStart_7860719 baseEnd_7860719 := by
    simpa [prefixWord, tailWord_7860719, baseEnd_7860719] using wordTrace_append hprefix tailTrace_7860719
  have hstable : (prefixWord ++ tailWord_7860719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860719).length < 2 ^ (prefixWord ++ tailWord_7860719).sum := by decide
  have hdescent : baseEnd_7860719 < baseStart_7860719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860739 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_7860739 : Nat := 118140960795 + 7860739 * 2 ^ 59
def prefixEnd_7860739 : Nat := 4983230072969 + 3 ^ 40 * 7860739 * 2
def baseEnd_7860739 : Nat := 4036337406543025556211625

theorem tailTrace_7860739 : CollatzResearch.WordTrace tailWord_7860739 prefixEnd_7860739 4036337406543025556211625 := by
  unfold tailWord_7860739
  simp only [CollatzResearch.WordTrace]
  refine ⟨286704705068892585183841271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191136470045928390122560847 286704705068892585183841271)
  ·
    refine ⟨430057057603338877775761907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286704705068892585183841271 430057057603338877775761907)
    ·
      refine ⟨645085586405008316663642861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430057057603338877775761907 645085586405008316663642861)
      ·
        refine ⟨241907094901878118748866073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645085586405008316663642861 241907094901878118748866073)
        ·
          refine ⟨181430321176408589061649555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241907094901878118748866073 181430321176408589061649555)
          ·
            refine ⟨272145481764612883592474333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181430321176408589061649555 272145481764612883592474333)
            ·
              refine ⟨102054555661729831347177875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272145481764612883592474333 102054555661729831347177875)
              ·
                refine ⟨153081833492594747020766813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102054555661729831347177875 153081833492594747020766813)
                ·
                  refine ⟨57405687559723030132787555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153081833492594747020766813 57405687559723030132787555)
                  ·
                    refine ⟨86108531339584545199181333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57405687559723030132787555 86108531339584545199181333)
                    ·
                      refine ⟨4036337406543025556211625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86108531339584545199181333 4036337406543025556211625)
                      ·
                        rfl

theorem cell23_7860739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_7860739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860739 prefixEnd_7860739 := by exact prefixLift 7860739
  have htrace : WordTrace (prefixWord ++ tailWord_7860739) baseStart_7860739 baseEnd_7860739 := by
    simpa [prefixWord, tailWord_7860739, baseEnd_7860739] using wordTrace_append hprefix tailTrace_7860739
  have hstable : (prefixWord ++ tailWord_7860739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860739).length < 2 ^ (prefixWord ++ tailWord_7860739).sum := by decide
  have hdescent : baseEnd_7860739 < baseStart_7860739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860746 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7860746 : Nat := 118140960795 + 7860746 * 2 ^ 59
def prefixEnd_7860746 : Nat := 4983230072969 + 3 ^ 40 * 7860746 * 2
def baseEnd_7860746 : Nat := 4036341000907607028824093

theorem tailTrace_7860746 : CollatzResearch.WordTrace tailWord_7860746 prefixEnd_7860746 4036341000907607028824093 := by
  unfold tailWord_7860746
  simp only [CollatzResearch.WordTrace]
  refine ⟨71676240094966806344836523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191136640253244816919564061 71676240094966806344836523)
  ·
    refine ⟨107514360142450209517254785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71676240094966806344836523 107514360142450209517254785)
    ·
      refine ⟨80635770106837657137941089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107514360142450209517254785 80635770106837657137941089)
      ·
        refine ⟨60476827580128242853455817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80635770106837657137941089 60476827580128242853455817)
        ·
          refine ⟨45357620685096182140091863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60476827580128242853455817 45357620685096182140091863)
          ·
            refine ⟨68036431027644273210137795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45357620685096182140091863 68036431027644273210137795)
            ·
              refine ⟨102054646541466409815206693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68036431027644273210137795 102054646541466409815206693)
              ·
                refine ⟨19135246226524951840351255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102054646541466409815206693 19135246226524951840351255)
                ·
                  refine ⟨28702869339787427760526883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19135246226524951840351255 28702869339787427760526883)
                  ·
                    refine ⟨43054304009681141640790325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28702869339787427760526883 43054304009681141640790325)
                    ·
                      refine ⟨4036341000907607028824093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43054304009681141640790325 4036341000907607028824093)
                      ·
                        rfl

theorem cell23_7860746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7860746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860746 prefixEnd_7860746 := by exact prefixLift 7860746
  have htrace : WordTrace (prefixWord ++ tailWord_7860746) baseStart_7860746 baseEnd_7860746 := by
    simpa [prefixWord, tailWord_7860746, baseEnd_7860746] using wordTrace_append hprefix tailTrace_7860746
  have hstable : (prefixWord ++ tailWord_7860746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860746).length < 2 ^ (prefixWord ++ tailWord_7860746).sum := by decide
  have hdescent : baseEnd_7860746 < baseStart_7860746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860760 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_7860760 : Nat := 118140960795 + 7860760 * 2 ^ 59
def prefixEnd_7860760 : Nat := 4983230072969 + 3 ^ 40 * 7860760 * 2
def baseEnd_7860760 : Nat := 4036348189636769974049029

theorem tailTrace_7860760 : CollatzResearch.WordTrace tailWord_7860760 prefixEnd_7860760 4036348189636769974049029 := by
  unfold tailWord_7860760
  simp only [CollatzResearch.WordTrace]
  refine ⟨143352735500908252885177867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191136980667877670513570489 143352735500908252885177867)
  ·
    refine ⟨215029103251362379327766801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143352735500908252885177867 215029103251362379327766801)
    ·
      refine ⟨161271827438521784495825101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215029103251362379327766801 161271827438521784495825101)
      ·
        refine ⟨60476935289445669185934413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161271827438521784495825101 60476935289445669185934413)
        ·
          refine ⟨22678850733542125944725405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60476935289445669185934413 22678850733542125944725405)
          ·
            refine ⟨8504569025078297229272027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22678850733542125944725405 8504569025078297229272027)
            ·
              refine ⟨12756853537617445843908041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8504569025078297229272027 12756853537617445843908041)
              ·
                refine ⟨9567640153213084382931031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12756853537617445843908041 9567640153213084382931031)
                ·
                  refine ⟨14351460229819626574396547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9567640153213084382931031 14351460229819626574396547)
                  ·
                    refine ⟨21527190344729439861594821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14351460229819626574396547 21527190344729439861594821)
                    ·
                      refine ⟨4036348189636769974049029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21527190344729439861594821 4036348189636769974049029)
                      ·
                        rfl

theorem cell23_7860760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_7860760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860760 prefixEnd_7860760 := by exact prefixLift 7860760
  have htrace : WordTrace (prefixWord ++ tailWord_7860760) baseStart_7860760 baseEnd_7860760 := by
    simpa [prefixWord, tailWord_7860760, baseEnd_7860760] using wordTrace_append hprefix tailTrace_7860760
  have hstable : (prefixWord ++ tailWord_7860760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860760).length < 2 ^ (prefixWord ++ tailWord_7860760).sum := by decide
  have hdescent : baseEnd_7860760 < baseStart_7860760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860779 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 4, 7]
def baseStart_7860779 : Nat := 118140960795 + 7860779 * 2 ^ 59
def prefixEnd_7860779 : Nat := 4983230072969 + 3 ^ 40 * 7860779 * 2
def baseEnd_7860779 : Nat := 1345452648589735133237147

theorem tailTrace_7860779 : CollatzResearch.WordTrace tailWord_7860779 prefixEnd_7860779 1345452648589735133237147 := by
  unfold tailWord_7860779
  simp only [CollatzResearch.WordTrace]
  refine ⟨286706163988747672015297391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191137442659165114676864927 286706163988747672015297391)
  ·
    refine ⟨430059245983121508022946087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286706163988747672015297391 430059245983121508022946087)
    ·
      refine ⟨645088868974682262034419131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430059245983121508022946087 645088868974682262034419131)
      ·
        refine ⟨967633303462023393051628697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645088868974682262034419131 967633303462023393051628697)
        ·
          refine ⟨725724977596517544788721523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967633303462023393051628697 725724977596517544788721523)
          ·
            refine ⟨1088587466394776317183082285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725724977596517544788721523 1088587466394776317183082285)
            ·
              refine ⟨408220299898041118943655857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1088587466394776317183082285 408220299898041118943655857)
              ·
                refine ⟨306165224923530839207741893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408220299898041118943655857 306165224923530839207741893)
                ·
                  refine ⟨57405979673162032351451605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306165224923530839207741893 57405979673162032351451605)
                  ·
                    refine ⟨1345452648589735133237147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57405979673162032351451605 1345452648589735133237147)
                    ·
                      rfl

theorem cell23_7860779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_7860779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860779 prefixEnd_7860779 := by exact prefixLift 7860779
  have htrace : WordTrace (prefixWord ++ tailWord_7860779) baseStart_7860779 baseEnd_7860779 := by
    simpa [prefixWord, tailWord_7860779, baseEnd_7860779] using wordTrace_append hprefix tailTrace_7860779
  have hstable : (prefixWord ++ tailWord_7860779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860779).length < 2 ^ (prefixWord ++ tailWord_7860779).sum := by decide
  have hdescent : baseEnd_7860779 < baseStart_7860779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860788 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7860788 : Nat := 118140960795 + 7860788 * 2 ^ 59
def prefixEnd_7860788 : Nat := 4983230072969 + 3 ^ 40 * 7860788 * 2
def baseEnd_7860788 : Nat := 4036362567095095864498901

theorem tailTrace_7860788 : CollatzResearch.WordTrace tailWord_7860788 prefixEnd_7860788 4036362567095095864498901 := by
  unfold tailWord_7860788
  simp only [CollatzResearch.WordTrace]
  refine ⟨143353246122857533276187509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191137661497143377701583345 143353246122857533276187509)
  ·
    refine ⟨13439366824017893744642579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143353246122857533276187509 13439366824017893744642579)
    ·
      refine ⟨20159050236026840616963869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439366824017893744642579 20159050236026840616963869)
      ·
        refine ⟨7559643838510065231361451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20159050236026840616963869 7559643838510065231361451)
        ·
          refine ⟨11339465757765097847042177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559643838510065231361451 11339465757765097847042177)
          ·
            refine ⟨8504599318323823385281633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11339465757765097847042177 8504599318323823385281633)
            ·
              refine ⟨6378449488742867538961225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8504599318323823385281633 6378449488742867538961225)
              ·
                refine ⟨4783837116557150654220919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378449488742867538961225 4783837116557150654220919)
                ·
                  refine ⟨7175755674835725981331379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783837116557150654220919 7175755674835725981331379)
                  ·
                    refine ⟨10763633512253588971997069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175755674835725981331379 10763633512253588971997069)
                    ·
                      refine ⟨4036362567095095864498901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763633512253588971997069 4036362567095095864498901)
                      ·
                        rfl

theorem cell23_7860788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7860788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860788 prefixEnd_7860788 := by exact prefixLift 7860788
  have htrace : WordTrace (prefixWord ++ tailWord_7860788) baseStart_7860788 baseEnd_7860788 := by
    simpa [prefixWord, tailWord_7860788, baseEnd_7860788] using wordTrace_append hprefix tailTrace_7860788
  have hstable : (prefixWord ++ tailWord_7860788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860788).length < 2 ^ (prefixWord ++ tailWord_7860788).sum := by decide
  have hdescent : baseEnd_7860788 < baseStart_7860788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860794 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2]
def baseStart_7860794 : Nat := 118140960795 + 7860794 * 2 ^ 59
def prefixEnd_7860794 : Nat := 4983230072969 + 3 ^ 40 * 7860794 * 2
def baseEnd_7860794 : Nat := 4036365647979022841023873

theorem tailTrace_7860794 : CollatzResearch.WordTrace tailWord_7860794 prefixEnd_7860794 4036365647979022841023873 := by
  unfold tailWord_7860794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71676677770923332394273359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191137807389128886384728957 71676677770923332394273359)
  ·
    refine ⟨107515016656384998591410039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71676677770923332394273359 107515016656384998591410039)
    ·
      refine ⟨161272524984577497887115059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107515016656384998591410039 161272524984577497887115059)
      ·
        refine ⟨241908787476866246830672589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161272524984577497887115059 241908787476866246830672589)
        ·
          refine ⟨90715795303824842561502221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241908787476866246830672589 90715795303824842561502221)
          ·
            refine ⟨34018423238934315960563333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90715795303824842561502221 34018423238934315960563333)
            ·
              refine ⟨6378454357300184242605625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34018423238934315960563333 6378454357300184242605625)
              ·
                refine ⟨4783840767975138181954219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378454357300184242605625 4783840767975138181954219)
                ·
                  refine ⟨7175761151962707272931329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783840767975138181954219 7175761151962707272931329)
                  ·
                    refine ⟨5381820863972030454698497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7175761151962707272931329 5381820863972030454698497)
                    ·
                      refine ⟨4036365647979022841023873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381820863972030454698497 4036365647979022841023873)
                      ·
                        rfl

theorem cell23_7860794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_7860794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860794 prefixEnd_7860794 := by exact prefixLift 7860794
  have htrace : WordTrace (prefixWord ++ tailWord_7860794) baseStart_7860794 baseEnd_7860794 := by
    simpa [prefixWord, tailWord_7860794, baseEnd_7860794] using wordTrace_append hprefix tailTrace_7860794
  have hstable : (prefixWord ++ tailWord_7860794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860794).length < 2 ^ (prefixWord ++ tailWord_7860794).sum := by decide
  have hdescent : baseEnd_7860794 < baseStart_7860794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860796 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_7860796 : Nat := 118140960795 + 7860796 * 2 ^ 59
def prefixEnd_7860796 : Nat := 4983230072969 + 3 ^ 40 * 7860796 * 2
def baseEnd_7860796 : Nat := 1345455558313443944399621

theorem tailTrace_7860796 : CollatzResearch.WordTrace tailWord_7860796 prefixEnd_7860796 1345455558313443944399621 := by
  unfold tailWord_7860796
  simp only [CollatzResearch.WordTrace]
  refine ⟨143353392014843041959333121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191137856019790722612444161 143353392014843041959333121)
  ·
    refine ⟨107515044011132281469499841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143353392014843041959333121 107515044011132281469499841)
    ·
      refine ⟨80636283008349211102124881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107515044011132281469499841 80636283008349211102124881)
      ·
        refine ⟨60477212256261908326593661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80636283008349211102124881 60477212256261908326593661)
        ·
          refine ⟨22678954596098215622472623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60477212256261908326593661 22678954596098215622472623)
          ·
            refine ⟨34018431894147323433708935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22678954596098215622472623 34018431894147323433708935)
            ·
              refine ⟨51027647841220985150563403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34018431894147323433708935 51027647841220985150563403)
              ·
                refine ⟨76541471761831477725845105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51027647841220985150563403 76541471761831477725845105)
                ·
                  refine ⟨57406103821373608294383829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76541471761831477725845105 57406103821373608294383829)
                  ·
                    refine ⟨1345455558313443944399621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57406103821373608294383829 1345455558313443944399621)
                    ·
                      rfl

theorem cell23_7860796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_7860796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860796 prefixEnd_7860796 := by exact prefixLift 7860796
  have htrace : WordTrace (prefixWord ++ tailWord_7860796) baseStart_7860796 baseEnd_7860796 := by
    simpa [prefixWord, tailWord_7860796, baseEnd_7860796] using wordTrace_append hprefix tailTrace_7860796
  have hstable : (prefixWord ++ tailWord_7860796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860796).length < 2 ^ (prefixWord ++ tailWord_7860796).sum := by decide
  have hdescent : baseEnd_7860796 < baseStart_7860796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860810 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_7860810 : Nat := 118140960795 + 7860810 * 2 ^ 59
def prefixEnd_7860810 : Nat := 4983230072969 + 3 ^ 40 * 7860810 * 2
def baseEnd_7860810 : Nat := 4036373863669494778423799

theorem tailTrace_7860810 : CollatzResearch.WordTrace tailWord_7860810 prefixEnd_7860810 4036373863669494778423799 := by
  unfold tailWord_7860810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71676823662908841077418971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191138196434423576206450589 71676823662908841077418971)
  ·
    refine ⟨107515235494363261616128457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71676823662908841077418971 107515235494363261616128457)
    ·
      refine ⟨80636426620772446212096343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107515235494363261616128457 80636426620772446212096343)
      ·
        refine ⟨120954639931158669318144515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80636426620772446212096343 120954639931158669318144515)
        ·
          refine ⟨181431959896738003977216773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120954639931158669318144515 181431959896738003977216773)
          ·
            refine ⟨34018492480638375745728145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181431959896738003977216773 34018492480638375745728145)
            ·
              refine ⟨25513869360478781809296109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34018492480638375745728145 25513869360478781809296109)
              ·
                refine ⟨9567701010179543178486041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25513869360478781809296109 9567701010179543178486041)
                ·
                  refine ⟨7175775757634657383864531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9567701010179543178486041 7175775757634657383864531)
                  ·
                    refine ⟨10763663636451986075796797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175775757634657383864531 10763663636451986075796797)
                    ·
                      refine ⟨4036373863669494778423799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763663636451986075796797 4036373863669494778423799)
                      ·
                        rfl

theorem cell23_7860810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_7860810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860810 prefixEnd_7860810 := by exact prefixLift 7860810
  have htrace : WordTrace (prefixWord ++ tailWord_7860810) baseStart_7860810 baseEnd_7860810 := by
    simpa [prefixWord, tailWord_7860810, baseEnd_7860810] using wordTrace_append hprefix tailTrace_7860810
  have hstable : (prefixWord ++ tailWord_7860810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860810).length < 2 ^ (prefixWord ++ tailWord_7860810).sum := by decide
  have hdescent : baseEnd_7860810 < baseStart_7860810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860820 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_7860820 : Nat := 118140960795 + 7860820 * 2 ^ 59
def prefixEnd_7860820 : Nat := 4983230072969 + 3 ^ 40 * 7860820 * 2
def baseEnd_7860820 : Nat := 4036378998476039739298753

theorem tailTrace_7860820 : CollatzResearch.WordTrace tailWord_7860820 prefixEnd_7860820 4036378998476039739298753 := by
  unfold tailWord_7860820
  simp only [CollatzResearch.WordTrace]
  refine ⟨143353829690799568008769957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191138439587732757345026609 143353829690799568008769957)
  ·
    refine ⟨26878843067024919001644367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143353829690799568008769957 26878843067024919001644367)
    ·
      refine ⟨40318264600537378502466551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26878843067024919001644367 40318264600537378502466551)
      ·
        refine ⟨60477396900806067753699827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40318264600537378502466551 60477396900806067753699827)
        ·
          refine ⟨90716095351209101630549741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60477396900806067753699827 90716095351209101630549741)
          ·
            refine ⟨34018535756703413111456153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90716095351209101630549741 34018535756703413111456153)
            ·
              refine ⟨25513901817527559833592115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34018535756703413111456153 25513901817527559833592115)
              ·
                refine ⟨38270852726291339750388173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25513901817527559833592115 38270852726291339750388173)
                ·
                  refine ⟨14351569772359252406395565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38270852726291339750388173 14351569772359252406395565)
                  ·
                    refine ⟨5381838664634719652398337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14351569772359252406395565 5381838664634719652398337)
                    ·
                      refine ⟨4036378998476039739298753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381838664634719652398337 4036378998476039739298753)
                      ·
                        rfl

theorem cell23_7860820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_7860820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860820 prefixEnd_7860820 := by exact prefixLift 7860820
  have htrace : WordTrace (prefixWord ++ tailWord_7860820) baseStart_7860820 baseEnd_7860820 := by
    simpa [prefixWord, tailWord_7860820, baseEnd_7860820] using wordTrace_append hprefix tailTrace_7860820
  have hstable : (prefixWord ++ tailWord_7860820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860820).length < 2 ^ (prefixWord ++ tailWord_7860820).sum := by decide
  have hdescent : baseEnd_7860820 < baseStart_7860820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860836 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7860836 : Nat := 118140960795 + 7860836 * 2 ^ 59
def prefixEnd_7860836 : Nat := 4983230072969 + 3 ^ 40 * 7860836 * 2
def baseEnd_7860836 : Nat := 4036387214166511676698679

theorem tailTrace_7860836 : CollatzResearch.WordTrace tailWord_7860836 prefixEnd_7860836 4036387214166511676698679 := by
  unfold tailWord_7860836
  simp only [CollatzResearch.WordTrace]
  refine ⟨143354121474770585375061181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191138828633027447166748241 143354121474770585375061181)
  ·
    refine ⟨53757795553038969515647943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143354121474770585375061181 53757795553038969515647943)
    ·
      refine ⟨80636693329558454273471915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53757795553038969515647943 80636693329558454273471915)
      ·
        refine ⟨120955039994337681410207873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80636693329558454273471915 120955039994337681410207873)
        ·
          refine ⟨90716279995753261057655905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120955039994337681410207873 90716279995753261057655905)
          ·
            refine ⟨68037209996814945793241929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90716279995753261057655905 68037209996814945793241929)
            ·
              refine ⟨51027907497611209344931447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68037209996814945793241929 51027907497611209344931447)
              ·
                refine ⟨76541861246416814017397171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51027907497611209344931447 76541861246416814017397171)
                ·
                  refine ⟨114812791869625221026095757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76541861246416814017397171 114812791869625221026095757)
                  ·
                    refine ⟨43054796951109457884785909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114812791869625221026095757 43054796951109457884785909)
                    ·
                      refine ⟨4036387214166511676698679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43054796951109457884785909 4036387214166511676698679)
                      ·
                        rfl

theorem cell23_7860836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7860836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860836 prefixEnd_7860836 := by exact prefixLift 7860836
  have htrace : WordTrace (prefixWord ++ tailWord_7860836) baseStart_7860836 baseEnd_7860836 := by
    simpa [prefixWord, tailWord_7860836, baseEnd_7860836] using wordTrace_append hprefix tailTrace_7860836
  have hstable : (prefixWord ++ tailWord_7860836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860836).length < 2 ^ (prefixWord ++ tailWord_7860836).sum := by decide
  have hdescent : baseEnd_7860836 < baseStart_7860836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860837 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 1, 3, 2]
def baseStart_7860837 : Nat := 118140960795 + 7860837 * 2 ^ 59
def prefixEnd_7860837 : Nat := 4983230072969 + 3 ^ 40 * 7860837 * 2
def baseEnd_7860837 : Nat := 4036387727647166172786175

theorem tailTrace_7860837 : CollatzResearch.WordTrace tailWord_7860837 prefixEnd_7860837 4036387727647166172786175 := by
  unfold tailWord_7860837
  simp only [CollatzResearch.WordTrace]
  refine ⟨286708279422537547920908765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191138852948358365280605843 286708279422537547920908765)
  ·
    refine ⟨107515604783451580470340787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286708279422537547920908765 107515604783451580470340787)
    ·
      refine ⟨161273407175177370705511181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107515604783451580470340787 161273407175177370705511181)
      ·
        refine ⟨60477527690691514014566693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161273407175177370705511181 60477527690691514014566693)
        ·
          refine ⟨11339536442004658877731255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60477527690691514014566693 11339536442004658877731255)
          ·
            refine ⟨17009304663006988316596883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339536442004658877731255 17009304663006988316596883)
            ·
              refine ⟨25513956994510482474895325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17009304663006988316596883 25513956994510482474895325)
              ·
                refine ⟨9567733872941430928085747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25513956994510482474895325 9567733872941430928085747)
                ·
                  refine ⟨14351600809412146392128621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9567733872941430928085747 14351600809412146392128621)
                  ·
                    refine ⟨5381850303529554897048233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14351600809412146392128621 5381850303529554897048233)
                    ·
                      refine ⟨4036387727647166172786175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381850303529554897048233 4036387727647166172786175)
                      ·
                        rfl

theorem cell23_7860837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_7860837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860837 prefixEnd_7860837 := by exact prefixLift 7860837
  have htrace : WordTrace (prefixWord ++ tailWord_7860837) baseStart_7860837 baseEnd_7860837 := by
    simpa [prefixWord, tailWord_7860837, baseEnd_7860837] using wordTrace_append hprefix tailTrace_7860837
  have hstable : (prefixWord ++ tailWord_7860837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860837).length < 2 ^ (prefixWord ++ tailWord_7860837).sum := by decide
  have hdescent : baseEnd_7860837 < baseStart_7860837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860940 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7860940 : Nat := 118140960795 + 7860940 * 2 ^ 59
def prefixEnd_7860940 : Nat := 4983230072969 + 3 ^ 40 * 7860940 * 2
def baseEnd_7860940 : Nat := 4036440616154579269798201

theorem tailTrace_7860940 : CollatzResearch.WordTrace tailWord_7860940 prefixEnd_7860940 4036440616154579269798201 := by
  unfold tailWord_7860940
  simp only [CollatzResearch.WordTrace]
  refine ⟨143356018070582198255954137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191141357427442931007938849 143356018070582198255954137)
  ·
    refine ⟨107517013552936648691965603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143356018070582198255954137 107517013552936648691965603)
    ·
      refine ⟨161275520329404973037948405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107517013552936648691965603 161275520329404973037948405)
      ·
        refine ⟨15119580030881716222307663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161275520329404973037948405 15119580030881716222307663)
        ·
          refine ⟨22679370046322574333461495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15119580030881716222307663 22679370046322574333461495)
          ·
            refine ⟨34019055069483861500192243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22679370046322574333461495 34019055069483861500192243)
            ·
              refine ⟨51028582604225792250288365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34019055069483861500192243 51028582604225792250288365)
              ·
                refine ⟨19135718476584672093858137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51028582604225792250288365 19135718476584672093858137)
                ·
                  refine ⟨14351788857438504070393603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19135718476584672093858137 14351788857438504070393603)
                  ·
                    refine ⟨21527683286157756105590405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14351788857438504070393603 21527683286157756105590405)
                    ·
                      refine ⟨4036440616154579269798201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21527683286157756105590405 4036440616154579269798201)
                      ·
                        rfl

theorem cell23_7860940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7860940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860940 prefixEnd_7860940 := by exact prefixLift 7860940
  have htrace : WordTrace (prefixWord ++ tailWord_7860940) baseStart_7860940 baseEnd_7860940 := by
    simpa [prefixWord, tailWord_7860940, baseEnd_7860940] using wordTrace_append hprefix tailTrace_7860940
  have hstable : (prefixWord ++ tailWord_7860940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860940).length < 2 ^ (prefixWord ++ tailWord_7860940).sum := by decide
  have hdescent : baseEnd_7860940 < baseStart_7860940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860994 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_7860994 : Nat := 118140960795 + 7860994 * 2 ^ 59
def prefixEnd_7860994 : Nat := 4983230072969 + 3 ^ 40 * 7860994 * 2
def baseEnd_7860994 : Nat := 4036468344109922058522953

theorem tailTrace_7860994 : CollatzResearch.WordTrace tailWord_7860994 prefixEnd_7860994 4036468344109922058522953 := by
  unfold tailWord_7860994
  simp only [CollatzResearch.WordTrace]
  refine ⟨71678501420742190933593509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191142670455312509156249357 71678501420742190933593509)
  ·
    refine ⟨13439719016389160800048783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71678501420742190933593509 13439719016389160800048783)
    ·
      refine ⟨20159578524583741200073175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439719016389160800048783 20159578524583741200073175)
      ·
        refine ⟨30239367786875611800109763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20159578524583741200073175 30239367786875611800109763)
        ·
          refine ⟨45359051680313417700164645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30239367786875611800109763 45359051680313417700164645)
          ·
            refine ⟨8504822190058765818780871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45359051680313417700164645 8504822190058765818780871)
            ·
              refine ⟨12757233285088148728171307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8504822190058765818780871 12757233285088148728171307)
              ·
                refine ⟨19135849927632223092256961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12757233285088148728171307 19135849927632223092256961)
                ·
                  refine ⟨14351887445724167319192721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19135849927632223092256961 14351887445724167319192721)
                  ·
                    refine ⟨10763915584293125489394541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14351887445724167319192721 10763915584293125489394541)
                    ·
                      refine ⟨4036468344109922058522953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763915584293125489394541 4036468344109922058522953)
                      ·
                        rfl

theorem cell23_7860994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_7860994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860994 prefixEnd_7860994 := by exact prefixLift 7860994
  have htrace : WordTrace (prefixWord ++ tailWord_7860994) baseStart_7860994 baseEnd_7860994 := by
    simpa [prefixWord, tailWord_7860994, baseEnd_7860994] using wordTrace_append hprefix tailTrace_7860994
  have hstable : (prefixWord ++ tailWord_7860994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860994).length < 2 ^ (prefixWord ++ tailWord_7860994).sum := by decide
  have hdescent : baseEnd_7860994 < baseStart_7860994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861024 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7861024 : Nat := 118140960795 + 7861024 * 2 ^ 59
def prefixEnd_7861024 : Nat := 4983230072969 + 3 ^ 40 * 7861024 * 2
def baseEnd_7861024 : Nat := 4036483748529556941147815

theorem tailTrace_7861024 : CollatzResearch.WordTrace tailWord_7861024 prefixEnd_7861024 4036483748529556941147815 := by
  unfold tailWord_7861024
  simp only [CollatzResearch.WordTrace]
  refine ⟨143357549936430039428983063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191143399915240052571977417 143357549936430039428983063)
  ·
    refine ⟨215036324904645059143474595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143357549936430039428983063 215036324904645059143474595)
    ·
      refine ⟨322554487356967588715211893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215036324904645059143474595 322554487356967588715211893)
      ·
        refine ⟨30239483189715711442051115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322554487356967588715211893 30239483189715711442051115)
        ·
          refine ⟨45359224784573567163076673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30239483189715711442051115 45359224784573567163076673)
          ·
            refine ⟨34019418588430175372307505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45359224784573567163076673 34019418588430175372307505)
            ·
              refine ⟨25514563941322631529230629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34019418588430175372307505 25514563941322631529230629)
              ·
                refine ⟨4783980738997993411730743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25514563941322631529230629 4783980738997993411730743)
                ·
                  refine ⟨7175971108496990117596115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783980738997993411730743 7175971108496990117596115)
                  ·
                    refine ⟨10763956662745485176394173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175971108496990117596115 10763956662745485176394173)
                    ·
                      refine ⟨4036483748529556941147815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763956662745485176394173 4036483748529556941147815)
                      ·
                        rfl

theorem cell23_7861024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7861024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861024 prefixEnd_7861024 := by exact prefixLift 7861024
  have htrace : WordTrace (prefixWord ++ tailWord_7861024) baseStart_7861024 baseEnd_7861024 := by
    simpa [prefixWord, tailWord_7861024, baseEnd_7861024] using wordTrace_append hprefix tailTrace_7861024
  have hstable : (prefixWord ++ tailWord_7861024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861024).length < 2 ^ (prefixWord ++ tailWord_7861024).sum := by decide
  have hdescent : baseEnd_7861024 < baseStart_7861024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861033 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_7861033 : Nat := 118140960795 + 7861033 * 2 ^ 59
def prefixEnd_7861033 : Nat := 4983230072969 + 3 ^ 40 * 7861033 * 2
def baseEnd_7861033 : Nat := 4036488369855447405935273

theorem tailTrace_7861033 : CollatzResearch.WordTrace tailWord_7861033 prefixEnd_7861033 4036488369855447405935273 := by
  unfold tailWord_7861033
  simp only [CollatzResearch.WordTrace]
  refine ⟨286715428129827473395043753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191143618753218315596695835 286715428129827473395043753)
  ·
    refine ⟨215036571097370605046282815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286715428129827473395043753 215036571097370605046282815)
    ·
      refine ⟨322554856646055907569424223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215036571097370605046282815 322554856646055907569424223)
      ·
        refine ⟨483832284969083861354136335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322554856646055907569424223 483832284969083861354136335)
        ·
          refine ⟨725748427453625792031204503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483832284969083861354136335 725748427453625792031204503)
          ·
            refine ⟨1088622641180438688046806755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725748427453625792031204503 1088622641180438688046806755)
            ·
              refine ⟨1632933961770658032070210133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088622641180438688046806755 1632933961770658032070210133)
              ·
                refine ⟨19135944864499898813322775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1632933961770658032070210133 19135944864499898813322775)
                ·
                  refine ⟨28703917296749848219984163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19135944864499898813322775 28703917296749848219984163)
                  ·
                    refine ⟨43055875945124772329976245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28703917296749848219984163 43055875945124772329976245)
                    ·
                      refine ⟨4036488369855447405935273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43055875945124772329976245 4036488369855447405935273)
                      ·
                        rfl

theorem cell23_7861033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_7861033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861033 prefixEnd_7861033 := by exact prefixLift 7861033
  have htrace : WordTrace (prefixWord ++ tailWord_7861033) baseStart_7861033 baseEnd_7861033 := by
    simpa [prefixWord, tailWord_7861033, baseEnd_7861033] using wordTrace_append hprefix tailTrace_7861033
  have hstable : (prefixWord ++ tailWord_7861033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861033).length < 2 ^ (prefixWord ++ tailWord_7861033).sum := by decide
  have hdescent : baseEnd_7861033 < baseStart_7861033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861040 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 2, 4]
def baseStart_7861040 : Nat := 118140960795 + 7861040 * 2 ^ 59
def prefixEnd_7861040 : Nat := 4983230072969 + 3 ^ 40 * 7861040 * 2
def baseEnd_7861040 : Nat := 1345497321406676292849247

theorem tailTrace_7861040 : CollatzResearch.WordTrace tailWord_7861040 prefixEnd_7861040 1345497321406676292849247 := by
  unfold tailWord_7861040
  simp only [CollatzResearch.WordTrace]
  refine ⟨143357841720401056795274287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191143788960534742393699049 143357841720401056795274287)
  ·
    refine ⟨215036762580601585192911431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143357841720401056795274287 215036762580601585192911431)
    ·
      refine ⟨322555143870902377789367147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215036762580601585192911431 322555143870902377789367147)
      ·
        refine ⟨483832715806353566684050721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322555143870902377789367147 483832715806353566684050721)
        ·
          refine ⟨362874536854765175013038041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483832715806353566684050721 362874536854765175013038041)
          ·
            refine ⟨272155902641073881259778531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362874536854765175013038041 272155902641073881259778531)
            ·
              refine ⟨408233853961610821889667797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272155902641073881259778531 408233853961610821889667797)
              ·
                refine ⟨9567980952225253638039089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 408233853961610821889667797 9567980952225253638039089)
                ·
                  refine ⟨7175985714168940228529317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9567980952225253638039089 7175985714168940228529317)
                  ·
                    refine ⟨1345497321406676292849247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175985714168940228529317 1345497321406676292849247)
                    ·
                      rfl

theorem cell23_7861040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_7861040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861040 prefixEnd_7861040 := by exact prefixLift 7861040
  have htrace : WordTrace (prefixWord ++ tailWord_7861040) baseStart_7861040 baseEnd_7861040 := by
    simpa [prefixWord, tailWord_7861040, baseEnd_7861040] using wordTrace_append hprefix tailTrace_7861040
  have hstable : (prefixWord ++ tailWord_7861040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861040).length < 2 ^ (prefixWord ++ tailWord_7861040).sum := by decide
  have hdescent : baseEnd_7861040 < baseStart_7861040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861044 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_7861044 : Nat := 118140960795 + 7861044 * 2 ^ 59
def prefixEnd_7861044 : Nat := 4983230072969 + 3 ^ 40 * 7861044 * 2
def baseEnd_7861044 : Nat := 1345498006047548954299241

theorem tailTrace_7861044 : CollatzResearch.WordTrace tailWord_7861044 prefixEnd_7861044 1345498006047548954299241 := by
  unfold tailWord_7861044
  simp only [CollatzResearch.WordTrace]
  refine ⟨143357914666393811136847093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191143886221858414849129457 143357914666393811136847093)
  ·
    refine ⟨13439804499974419794079415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143357914666393811136847093 13439804499974419794079415)
    ·
      refine ⟨20159706749961629691119123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439804499974419794079415 20159706749961629691119123)
      ·
        refine ⟨30239560124942444536678685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20159706749961629691119123 30239560124942444536678685)
        ·
          refine ⟨11339835046853416701254507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30239560124942444536678685 11339835046853416701254507)
          ·
            refine ⟨17009752570280125051881761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339835046853416701254507 17009752570280125051881761)
            ·
              refine ⟨12757314427710093788911321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17009752570280125051881761 12757314427710093788911321)
              ·
                refine ⟨9567985820782570341683491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12757314427710093788911321 9567985820782570341683491)
                ·
                  refine ⟨14351978731173855512525237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9567985820782570341683491 14351978731173855512525237)
                  ·
                    refine ⟨1345498006047548954299241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14351978731173855512525237 1345498006047548954299241)
                    ·
                      rfl

theorem cell23_7861044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_7861044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861044 prefixEnd_7861044 := by exact prefixLift 7861044
  have htrace : WordTrace (prefixWord ++ tailWord_7861044) baseStart_7861044 baseEnd_7861044 := by
    simpa [prefixWord, tailWord_7861044, baseEnd_7861044] using wordTrace_append hprefix tailTrace_7861044
  have hstable : (prefixWord ++ tailWord_7861044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861044).length < 2 ^ (prefixWord ++ tailWord_7861044).sum := by decide
  have hdescent : baseEnd_7861044 < baseStart_7861044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861047 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 3, 2, 2]
def baseStart_7861047 : Nat := 118140960795 + 7861047 * 2 ^ 59
def prefixEnd_7861047 : Nat := 4983230072969 + 3 ^ 40 * 7861047 * 2
def baseEnd_7861047 : Nat := 4036495558584610351160209

theorem tailTrace_7861047 : CollatzResearch.WordTrace tailWord_7861047 prefixEnd_7861047 4036495558584610351160209 := by
  unfold tailWord_7861047
  simp only [CollatzResearch.WordTrace]
  refine ⟨286715938751776753786053395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191143959167851169190702263 286715938751776753786053395)
  ·
    refine ⟨430073908127665130679080093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286715938751776753786053395 430073908127665130679080093)
    ·
      refine ⟨161277715547874424004655035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430073908127665130679080093 161277715547874424004655035)
      ·
        refine ⟨241916573321811636006982553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161277715547874424004655035 241916573321811636006982553)
        ·
          refine ⟨181437429991358727005236915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241916573321811636006982553 181437429991358727005236915)
          ·
            refine ⟨272156144987038090507855373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181437429991358727005236915 272156144987038090507855373)
            ·
              refine ⟨102058554370139283940445765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272156144987038090507855373 102058554370139283940445765)
              ·
                refine ⟨19135978944401115738833581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102058554370139283940445765 19135978944401115738833581)
                ·
                  refine ⟨7175992104150418402062593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19135978944401115738833581 7175992104150418402062593)
                  ·
                    refine ⟨5381994078112813801546945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7175992104150418402062593 5381994078112813801546945)
                    ·
                      refine ⟨4036495558584610351160209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381994078112813801546945 4036495558584610351160209)
                      ·
                        rfl

theorem cell23_7861047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_7861047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861047 prefixEnd_7861047 := by exact prefixLift 7861047
  have htrace : WordTrace (prefixWord ++ tailWord_7861047) baseStart_7861047 baseEnd_7861047 := by
    simpa [prefixWord, tailWord_7861047, baseEnd_7861047] using wordTrace_append hprefix tailTrace_7861047
  have hstable : (prefixWord ++ tailWord_7861047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861047).length < 2 ^ (prefixWord ++ tailWord_7861047).sum := by decide
  have hdescent : baseEnd_7861047 < baseStart_7861047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861118 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7861118 : Nat := 118140960795 + 7861118 * 2 ^ 59
def prefixEnd_7861118 : Nat := 4983230072969 + 3 ^ 40 * 7861118 * 2
def baseEnd_7861118 : Nat := 4036532015711079573372383

theorem tailTrace_7861118 : CollatzResearch.WordTrace tailWord_7861118 prefixEnd_7861118 4036532015711079573372383 := by
  unfold tailWord_7861118
  simp only [CollatzResearch.WordTrace]
  refine ⟨35839816041814941613986001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191145685556346355274592005 35839816041814941613986001)
  ·
    refine ⟨26879862031361206210489501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35839816041814941613986001 26879862031361206210489501)
    ·
      refine ⟨10079948261760452328933563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26879862031361206210489501 10079948261760452328933563)
      ·
        refine ⟨15119922392640678493400345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10079948261760452328933563 15119922392640678493400345)
        ·
          refine ⟨11339941794480508870050259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15119922392640678493400345 11339941794480508870050259)
          ·
            refine ⟨17009912691720763305075389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339941794480508870050259 17009912691720763305075389)
            ·
              refine ⟨6378717259395286239403271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17009912691720763305075389 6378717259395286239403271)
              ·
                refine ⟨9568075889092929359104907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378717259395286239403271 9568075889092929359104907)
                ·
                  refine ⟨14352113833639394038657361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9568075889092929359104907 14352113833639394038657361)
                  ·
                    refine ⟨10764085375229545528993021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14352113833639394038657361 10764085375229545528993021)
                    ·
                      refine ⟨4036532015711079573372383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10764085375229545528993021 4036532015711079573372383)
                      ·
                        rfl

theorem cell23_7861118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7861118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861118 prefixEnd_7861118 := by exact prefixLift 7861118
  have htrace : WordTrace (prefixWord ++ tailWord_7861118) baseStart_7861118 baseEnd_7861118 := by
    simpa [prefixWord, tailWord_7861118, baseEnd_7861118] using wordTrace_append hprefix tailTrace_7861118
  have hstable : (prefixWord ++ tailWord_7861118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861118).length < 2 ^ (prefixWord ++ tailWord_7861118).sum := by decide
  have hdescent : baseEnd_7861118 < baseStart_7861118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861154 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7861154 : Nat := 118140960795 + 7861154 * 2 ^ 59
def prefixEnd_7861154 : Nat := 4983230072969 + 3 ^ 40 * 7861154 * 2
def baseEnd_7861154 : Nat := 4036550501014641432522217

theorem tailTrace_7861154 : CollatzResearch.WordTrace tailWord_7861154 prefixEnd_7861154 4036550501014641432522217 := by
  unfold tailWord_7861154
  simp only [CollatzResearch.WordTrace]
  refine ⟨71679960340597277765049629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191146560908259407373465677 71679960340597277765049629)
  ·
    refine ⟨26879985127723979161893611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71679960340597277765049629 26879985127723979161893611)
    ·
      refine ⟨40319977691585968742840417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26879985127723979161893611 40319977691585968742840417)
      ·
        refine ⟨30239983268689476557130313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40319977691585968742840417 30239983268689476557130313)
        ·
          refine ⟨22679987451517107417847735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30239983268689476557130313 22679987451517107417847735)
          ·
            refine ⟨34019981177275661126771603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22679987451517107417847735 34019981177275661126771603)
            ·
              refine ⟨51029971765913491690157405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34019981177275661126771603 51029971765913491690157405)
              ·
                refine ⟨19136239412217559383809027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51029971765913491690157405 19136239412217559383809027)
                ·
                  refine ⟨28704359118326339075713541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19136239412217559383809027 28704359118326339075713541)
                  ·
                    refine ⟨5382067334686188576696289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28704359118326339075713541 5382067334686188576696289)
                    ·
                      refine ⟨4036550501014641432522217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382067334686188576696289 4036550501014641432522217)
                      ·
                        rfl

theorem cell23_7861154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7861154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861154 prefixEnd_7861154 := by exact prefixLift 7861154
  have htrace : WordTrace (prefixWord ++ tailWord_7861154) baseStart_7861154 baseEnd_7861154 := by
    simpa [prefixWord, tailWord_7861154, baseEnd_7861154] using wordTrace_append hprefix tailTrace_7861154
  have hstable : (prefixWord ++ tailWord_7861154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861154).length < 2 ^ (prefixWord ++ tailWord_7861154).sum := by decide
  have hdescent : baseEnd_7861154 < baseStart_7861154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_7861163 : Nat := 118140960795 + 7861163 * 2 ^ 59
def prefixEnd_7861163 : Nat := 4983230072969 + 3 ^ 40 * 7861163 * 2
def baseEnd_7861163 : Nat := 4036555122340531897309675

theorem tailTrace_7861163 : CollatzResearch.WordTrace tailWord_7861163 prefixEnd_7861163 4036555122340531897309675 := by
  unfold tailWord_7861163
  simp only [CollatzResearch.WordTrace]
  refine ⟨286720169619356505597276143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191146779746237670398184095 286720169619356505597276143)
  ·
    refine ⟨430080254429034758395914215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286720169619356505597276143 430080254429034758395914215)
    ·
      refine ⟨645120381643552137593871323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430080254429034758395914215 645120381643552137593871323)
      ·
        refine ⟨967680572465328206390806985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645120381643552137593871323 967680572465328206390806985)
        ·
          refine ⟨725760429348996154793105239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967680572465328206390806985 725760429348996154793105239)
          ·
            refine ⟨1088640644023494232189657859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725760429348996154793105239 1088640644023494232189657859)
            ·
              refine ⟨1632960966035241348284486789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088640644023494232189657859 1632960966035241348284486789)
              ·
                refine ⟨306180181131607752803341273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1632960966035241348284486789 306180181131607752803341273)
                ·
                  refine ⟨229635135848705814602505955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306180181131607752803341273 229635135848705814602505955)
                  ·
                    refine ⟨344452703773058721903758933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229635135848705814602505955 344452703773058721903758933)
                    ·
                      refine ⟨4036555122340531897309675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 344452703773058721903758933 4036555122340531897309675)
                      ·
                        rfl

theorem cell23_7861163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_7861163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861163 prefixEnd_7861163 := by exact prefixLift 7861163
  have htrace : WordTrace (prefixWord ++ tailWord_7861163) baseStart_7861163 baseEnd_7861163 := by
    simpa [prefixWord, tailWord_7861163, baseEnd_7861163] using wordTrace_append hprefix tailTrace_7861163
  have hstable : (prefixWord ++ tailWord_7861163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861163).length < 2 ^ (prefixWord ++ tailWord_7861163).sum := by decide
  have hdescent : baseEnd_7861163 < baseStart_7861163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861177 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 5]
def baseStart_7861177 : Nat := 118140960795 + 7861177 * 2 ^ 59
def prefixEnd_7861177 : Nat := 4983230072969 + 3 ^ 40 * 7861177 * 2
def baseEnd_7861177 : Nat := 448506923452188315837179

theorem tailTrace_7861177 : CollatzResearch.WordTrace tailWord_7861177 prefixEnd_7861177 448506923452188315837179 := by
  unfold tailWord_7861177
  simp only [CollatzResearch.WordTrace]
  refine ⟨286720680241305785988285785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191147120160870523992190523 286720680241305785988285785)
  ·
    refine ⟨215040510180979339491214339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286720680241305785988285785 215040510180979339491214339)
    ·
      refine ⟨322560765271469009236821509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215040510180979339491214339 322560765271469009236821509)
      ·
        refine ⟨60480143488400439231904033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322560765271469009236821509 60480143488400439231904033)
        ·
          refine ⟨45360107616300329423928025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60480143488400439231904033 45360107616300329423928025)
          ·
            refine ⟨34020080712225247067946019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45360107616300329423928025 34020080712225247067946019)
            ·
              refine ⟨51030121068337870601919029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34020080712225247067946019 51030121068337870601919029)
              ·
                refine ⟨4784073850156675368929909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51030121068337870601919029 4784073850156675368929909)
                ·
                  refine ⟨448506923452188315837179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4784073850156675368929909 448506923452188315837179)
                  ·
                    rfl

theorem cell23_7861177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 5].length) (baseStart_7861177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861177 prefixEnd_7861177 := by exact prefixLift 7861177
  have htrace : WordTrace (prefixWord ++ tailWord_7861177) baseStart_7861177 baseEnd_7861177 := by
    simpa [prefixWord, tailWord_7861177, baseEnd_7861177] using wordTrace_append hprefix tailTrace_7861177
  have hstable : (prefixWord ++ tailWord_7861177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861177).length < 2 ^ (prefixWord ++ tailWord_7861177).sum := by decide
  have hdescent : baseEnd_7861177 < baseStart_7861177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861188 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7861188 : Nat := 118140960795 + 7861188 * 2 ^ 59
def prefixEnd_7861188 : Nat := 4983230072969 + 3 ^ 40 * 7861188 * 2
def baseEnd_7861188 : Nat := 4036567959356894299497061

theorem tailTrace_7861188 : CollatzResearch.WordTrace tailWord_7861188 prefixEnd_7861188 4036567959356894299497061 := by
  unfold tailWord_7861188
  simp only [CollatzResearch.WordTrace]
  refine ⟨143360540722132967433468109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191147387629510623244624145 143360540722132967433468109)
  ·
    refine ⟨53760202770799862787550541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143360540722132967433468109 53760202770799862787550541)
    ·
      refine ⟨20160076039049948545331453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53760202770799862787550541 20160076039049948545331453)
      ·
        refine ⟨7560028514643730704499295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20160076039049948545331453 7560028514643730704499295)
        ·
          refine ⟨11340042771965596056748943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7560028514643730704499295 11340042771965596056748943)
          ·
            refine ⟨17010064157948394085123415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11340042771965596056748943 17010064157948394085123415)
            ·
              refine ⟨25515096236922591127685123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17010064157948394085123415 25515096236922591127685123)
              ·
                refine ⟨38272644355383886691527685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25515096236922591127685123 38272644355383886691527685)
                ·
                  refine ⟨7176120816634478754661441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38272644355383886691527685 7176120816634478754661441)
                  ·
                    refine ⟨5382090612475859065996081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7176120816634478754661441 5382090612475859065996081)
                    ·
                      refine ⟨4036567959356894299497061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382090612475859065996081 4036567959356894299497061)
                      ·
                        rfl

theorem cell23_7861188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7861188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861188 prefixEnd_7861188 := by exact prefixLift 7861188
  have htrace : WordTrace (prefixWord ++ tailWord_7861188) baseStart_7861188 baseEnd_7861188 := by
    simpa [prefixWord, tailWord_7861188, baseEnd_7861188] using wordTrace_append hprefix tailTrace_7861188
  have hstable : (prefixWord ++ tailWord_7861188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861188).length < 2 ^ (prefixWord ++ tailWord_7861188).sum := by decide
  have hdescent : baseEnd_7861188 < baseStart_7861188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861317 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_7861317 : Nat := 118140960795 + 7861317 * 2 ^ 59
def prefixEnd_7861317 : Nat := 4983230072969 + 3 ^ 40 * 7861317 * 2
def baseEnd_7861317 : Nat := 4036634198361324294783967

theorem tailTrace_7861317 : CollatzResearch.WordTrace tailWord_7861317 prefixEnd_7861317 4036634198361324294783967 := by
  unfold tailWord_7861317
  simp only [CollatzResearch.WordTrace]
  refine ⟨286725786460798589898382205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191150524307199059932254803 286725786460798589898382205)
  ·
    refine ⟨107522169922799471211893327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286725786460798589898382205 107522169922799471211893327)
    ·
      refine ⟨161283254884199206817839991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107522169922799471211893327 161283254884199206817839991)
      ·
        refine ⟨241924882326298810226759987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161283254884199206817839991 241924882326298810226759987)
        ·
          refine ⟨362887323489448215340139981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241924882326298810226759987 362887323489448215340139981)
          ·
            refine ⟨136082746308543080752552493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362887323489448215340139981 136082746308543080752552493)
            ·
              refine ⟨51031029865703655282207185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136082746308543080752552493 51031029865703655282207185)
              ·
                refine ⟨38273272399277741461655389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51031029865703655282207185 38273272399277741461655389)
                ·
                  refine ⟨14352477149729153048120771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38273272399277741461655389 14352477149729153048120771)
                  ·
                    refine ⟨21528715724593729572181157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14352477149729153048120771 21528715724593729572181157)
                    ·
                      refine ⟨4036634198361324294783967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21528715724593729572181157 4036634198361324294783967)
                      ·
                        rfl

theorem cell23_7861317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_7861317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861317 prefixEnd_7861317 := by exact prefixLift 7861317
  have htrace : WordTrace (prefixWord ++ tailWord_7861317) baseStart_7861317 baseEnd_7861317 := by
    simpa [prefixWord, tailWord_7861317, baseEnd_7861317] using wordTrace_append hprefix tailTrace_7861317
  have hstable : (prefixWord ++ tailWord_7861317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861317).length < 2 ^ (prefixWord ++ tailWord_7861317).sum := by decide
  have hdescent : baseEnd_7861317 < baseStart_7861317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861351 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_7861351 : Nat := 118140960795 + 7861351 * 2 ^ 59
def prefixEnd_7861351 : Nat := 4983230072969 + 3 ^ 40 * 7861351 * 2
def baseEnd_7861351 : Nat := 4036651656703577161758811

theorem tailTrace_7861351 : CollatzResearch.WordTrace tailWord_7861351 prefixEnd_7861351 4036651656703577161758811 := by
  unfold tailWord_7861351
  simp only [CollatzResearch.WordTrace]
  refine ⟨286727026542675413705119907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191151351028450275803413271 286727026542675413705119907)
  ·
    refine ⟨430090539814013120557679861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286727026542675413705119907 430090539814013120557679861)
    ·
      refine ⟨40320988107563730052282487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430090539814013120557679861 40320988107563730052282487)
      ·
        refine ⟨60481482161345595078423731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40320988107563730052282487 60481482161345595078423731)
        ·
          refine ⟨90722223242018392617635597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60481482161345595078423731 90722223242018392617635597)
          ·
            refine ⟨34020833715756897231613349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90722223242018392617635597 34020833715756897231613349)
            ·
              refine ⟨6378906321704418230927503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34020833715756897231613349 6378906321704418230927503)
              ·
                refine ⟨9568359482556627346391255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378906321704418230927503 9568359482556627346391255)
                ·
                  refine ⟨14352539223834941019586883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9568359482556627346391255 14352539223834941019586883)
                  ·
                    refine ⟨21528808835752411529380325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14352539223834941019586883 21528808835752411529380325)
                    ·
                      refine ⟨4036651656703577161758811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21528808835752411529380325 4036651656703577161758811)
                      ·
                        rfl

theorem cell23_7861351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_7861351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861351 prefixEnd_7861351 := by exact prefixLift 7861351
  have htrace : WordTrace (prefixWord ++ tailWord_7861351) baseStart_7861351 baseEnd_7861351 := by
    simpa [prefixWord, tailWord_7861351, baseEnd_7861351] using wordTrace_append hprefix tailTrace_7861351
  have hstable : (prefixWord ++ tailWord_7861351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861351).length < 2 ^ (prefixWord ++ tailWord_7861351).sum := by decide
  have hdescent : baseEnd_7861351 < baseStart_7861351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861357 : List Nat := [1, 5, 1, 1, 2, 3, 10]
def baseStart_7861357 : Nat := 118140960795 + 7861357 * 2 ^ 59
def prefixEnd_7861357 : Nat := 4983230072969 + 3 ^ 40 * 7861357 * 2
def baseEnd_7861357 : Nat := 49835243673919804176343

theorem tailTrace_7861357 : CollatzResearch.WordTrace tailWord_7861357 prefixEnd_7861357 49835243673919804176343 := by
  unfold tailWord_7861357
  simp only [CollatzResearch.WordTrace]
  refine ⟨286727245380653676729838325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191151496920435784486558883 286727245380653676729838325)
  ·
    refine ⟨26880679254436282193422343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286727245380653676729838325 26880679254436282193422343)
    ·
      refine ⟨40321018881654423290133515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26880679254436282193422343 40321018881654423290133515)
      ·
        refine ⟨60481528322481634935200273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40321018881654423290133515 60481528322481634935200273)
        ·
          refine ⟨45361146241861226201400205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60481528322481634935200273 45361146241861226201400205)
          ·
            refine ⟨17010429840697959825525077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45361146241861226201400205 17010429840697959825525077)
            ·
              refine ⟨49835243673919804176343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17010429840697959825525077 49835243673919804176343)
              ·
                rfl

theorem cell23_7861357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 10].length) (baseStart_7861357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861357 prefixEnd_7861357 := by exact prefixLift 7861357
  have htrace : WordTrace (prefixWord ++ tailWord_7861357) baseStart_7861357 baseEnd_7861357 := by
    simpa [prefixWord, tailWord_7861357, baseEnd_7861357] using wordTrace_append hprefix tailTrace_7861357
  have hstable : (prefixWord ++ tailWord_7861357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861357).length < 2 ^ (prefixWord ++ tailWord_7861357).sum := by decide
  have hdescent : baseEnd_7861357 < baseStart_7861357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861368 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 1, 2, 2]
def baseStart_7861368 : Nat := 118140960795 + 7861368 * 2 ^ 59
def prefixEnd_7861368 : Nat := 4983230072969 + 3 ^ 40 * 7861368 * 2
def baseEnd_7861368 : Nat := 4036660385874703595246233

theorem tailTrace_7861368 : CollatzResearch.WordTrace tailWord_7861368 prefixEnd_7861368 4036660385874703595246233 := by
  unfold tailWord_7861368
  simp only [CollatzResearch.WordTrace]
  refine ⟨143363823291806912804244379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191151764389075883738992505 143363823291806912804244379)
  ·
    refine ⟨215045734937710369206366569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143363823291806912804244379 215045734937710369206366569)
    ·
      refine ⟨161284301203282776904774927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215045734937710369206366569 161284301203282776904774927)
      ·
        refine ⟨241926451804924165357162391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161284301203282776904774927 241926451804924165357162391)
        ·
          refine ⟨362889677707386248035743587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241926451804924165357162391 362889677707386248035743587)
          ·
            refine ⟨544334516561079372053615381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362889677707386248035743587 544334516561079372053615381)
            ·
              refine ⟨25515680463800595565013221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 544334516561079372053615381 25515680463800595565013221)
              ·
                refine ⟨4784190086962611668439979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25515680463800595565013221 4784190086962611668439979)
                ·
                  refine ⟨7176285130443917502659969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784190086962611668439979 7176285130443917502659969)
                  ·
                    refine ⟨5382213847832938126994977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7176285130443917502659969 5382213847832938126994977)
                    ·
                      refine ⟨4036660385874703595246233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382213847832938126994977 4036660385874703595246233)
                      ·
                        rfl

theorem cell23_7861368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_7861368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861368 prefixEnd_7861368 := by exact prefixLift 7861368
  have htrace : WordTrace (prefixWord ++ tailWord_7861368) baseStart_7861368 baseEnd_7861368 := by
    simpa [prefixWord, tailWord_7861368, baseEnd_7861368] using wordTrace_append hprefix tailTrace_7861368
  have hstable : (prefixWord ++ tailWord_7861368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861368).length < 2 ^ (prefixWord ++ tailWord_7861368).sum := by decide
  have hdescent : baseEnd_7861368 < baseStart_7861368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861381 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_7861381 : Nat := 118140960795 + 7861381 * 2 ^ 59
def prefixEnd_7861381 : Nat := 4983230072969 + 3 ^ 40 * 7861381 * 2
def baseEnd_7861381 : Nat := 4036667061123212044383673

theorem tailTrace_7861381 : CollatzResearch.WordTrace tailWord_7861381 prefixEnd_7861381 4036667061123212044383673 := by
  unfold tailWord_7861381
  simp only [CollatzResearch.WordTrace]
  refine ⟨286728120732566728828711997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191152080488377819219141331 286728120732566728828711997)
  ·
    refine ⟨107523045274712523310766999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286728120732566728828711997 107523045274712523310766999)
    ·
      refine ⟨161284567912068784966150499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107523045274712523310766999 161284567912068784966150499)
      ·
        refine ⟨241926851868103177449225749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161284567912068784966150499 241926851868103177449225749)
        ·
          refine ⟨11340321181317336442932457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241926851868103177449225749 11340321181317336442932457)
          ·
            refine ⟨8505240885988002332199343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11340321181317336442932457 8505240885988002332199343)
            ·
              refine ⟨12757861328982003498299015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505240885988002332199343 12757861328982003498299015)
              ·
                refine ⟨19136791993473005247448523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12757861328982003498299015 19136791993473005247448523)
                ·
                  refine ⟨28705187990209507871172785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19136791993473005247448523 28705187990209507871172785)
                  ·
                    refine ⟨21528890992657130903379589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28705187990209507871172785 21528890992657130903379589)
                    ·
                      refine ⟨4036667061123212044383673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21528890992657130903379589 4036667061123212044383673)
                      ·
                        rfl

theorem cell23_7861381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_7861381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861381 prefixEnd_7861381 := by exact prefixLift 7861381
  have htrace : WordTrace (prefixWord ++ tailWord_7861381) baseStart_7861381 baseEnd_7861381 := by
    simpa [prefixWord, tailWord_7861381, baseEnd_7861381] using wordTrace_append hprefix tailTrace_7861381
  have hstable : (prefixWord ++ tailWord_7861381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861381).length < 2 ^ (prefixWord ++ tailWord_7861381).sum := by decide
  have hdescent : baseEnd_7861381 < baseStart_7861381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861402 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7861402 : Nat := 118140960795 + 7861402 * 2 ^ 59
def prefixEnd_7861402 : Nat := 4983230072969 + 3 ^ 40 * 7861402 * 2
def baseEnd_7861402 : Nat := 4036677844216956462221077

theorem tailTrace_7861402 : CollatzResearch.WordTrace tailWord_7861402 prefixEnd_7861402 4036677844216956462221077 := by
  unfold tailWord_7861402
  simp only [CollatzResearch.WordTrace]
  refine ⟨71682221666372662353806615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191152591110327099610150973 71682221666372662353806615)
  ·
    refine ⟨107523332499558993530709923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71682221666372662353806615 107523332499558993530709923)
    ·
      refine ⟨161284998749338490296064885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107523332499558993530709923 161284998749338490296064885)
      ·
        refine ⟨15120468632750483465256083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161284998749338490296064885 15120468632750483465256083)
        ·
          refine ⟨22680702949125725197884125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15120468632750483465256083 22680702949125725197884125)
          ·
            refine ⟨8505263605922146949206547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22680702949125725197884125 8505263605922146949206547)
            ·
              refine ⟨12757895408883220423809821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505263605922146949206547 12757895408883220423809821)
              ·
                refine ⟨4784210778331207658928683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12757895408883220423809821 4784210778331207658928683)
                ·
                  refine ⟨7176316167496811488393025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784210778331207658928683 7176316167496811488393025)
                  ·
                    refine ⟨5382237125622608616294769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7176316167496811488393025 5382237125622608616294769)
                    ·
                      refine ⟨4036677844216956462221077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382237125622608616294769 4036677844216956462221077)
                      ·
                        rfl

theorem cell23_7861402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7861402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861402 prefixEnd_7861402 := by exact prefixLift 7861402
  have htrace : WordTrace (prefixWord ++ tailWord_7861402) baseStart_7861402 baseEnd_7861402 := by
    simpa [prefixWord, tailWord_7861402, baseEnd_7861402] using wordTrace_append hprefix tailTrace_7861402
  have hstable : (prefixWord ++ tailWord_7861402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861402).length < 2 ^ (prefixWord ++ tailWord_7861402).sum := by decide
  have hdescent : baseEnd_7861402 < baseStart_7861402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861418 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7861418 : Nat := 118140960795 + 7861418 * 2 ^ 59
def prefixEnd_7861418 : Nat := 4983230072969 + 3 ^ 40 * 7861418 * 2
def baseEnd_7861418 : Nat := 4036686059907428399621003

theorem tailTrace_7861418 : CollatzResearch.WordTrace tailWord_7861418 prefixEnd_7861418 4036686059907428399621003 := by
  unfold tailWord_7861418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71682367558358171036952227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191152980155621789431872605 71682367558358171036952227)
  ·
    refine ⟨107523551337537256555428341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71682367558358171036952227 107523551337537256555428341)
    ·
      refine ⟨10080332937894117802071407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107523551337537256555428341 10080332937894117802071407)
      ·
        refine ⟨15120499406841176703107111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10080332937894117802071407 15120499406841176703107111)
        ·
          refine ⟨22680749110261765054660667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15120499406841176703107111 22680749110261765054660667)
          ·
            refine ⟨34021123665392647581991001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22680749110261765054660667 34021123665392647581991001)
            ·
              refine ⟨25515842749044485686493251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34021123665392647581991001 25515842749044485686493251)
              ·
                refine ⟨38273764123566728529739877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25515842749044485686493251 38273764123566728529739877)
                ·
                  refine ⟨7176330773168761599326227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38273764123566728529739877 7176330773168761599326227)
                  ·
                    refine ⟨10764496159753142398989341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7176330773168761599326227 10764496159753142398989341)
                    ·
                      refine ⟨4036686059907428399621003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10764496159753142398989341 4036686059907428399621003)
                      ·
                        rfl

theorem cell23_7861418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7861418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861418 prefixEnd_7861418 := by exact prefixLift 7861418
  have htrace : WordTrace (prefixWord ++ tailWord_7861418) baseStart_7861418 baseEnd_7861418 := by
    simpa [prefixWord, tailWord_7861418, baseEnd_7861418] using wordTrace_append hprefix tailTrace_7861418
  have hstable : (prefixWord ++ tailWord_7861418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861418).length < 2 ^ (prefixWord ++ tailWord_7861418).sum := by decide
  have hdescent : baseEnd_7861418 < baseStart_7861418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861424 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 3, 4, 2]
def baseStart_7861424 : Nat := 118140960795 + 7861424 * 2 ^ 59
def prefixEnd_7861424 : Nat := 4983230072969 + 3 ^ 40 * 7861424 * 2
def baseEnd_7861424 : Nat := 4036689140791355376145975

theorem tailTrace_7861424 : CollatzResearch.WordTrace tailWord_7861424 prefixEnd_7861424 4036689140791355376145975 := by
  unfold tailWord_7861424
  simp only [CollatzResearch.WordTrace]
  refine ⟨143364844535705473586263663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191153126047607298115018217 143364844535705473586263663)
  ·
    refine ⟨215047266803558210379395495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143364844535705473586263663 215047266803558210379395495)
    ·
      refine ⟨322570900205337315569093243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215047266803558210379395495 322570900205337315569093243)
      ·
        refine ⟨483856350308005973353639865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322570900205337315569093243 483856350308005973353639865)
        ·
          refine ⟨362892262731004480015229899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483856350308005973353639865 362892262731004480015229899)
          ·
            refine ⟨544338394096506720022844849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362892262731004480015229899 544338394096506720022844849)
            ·
              refine ⟨408253795572380040017133637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544338394096506720022844849 408253795572380040017133637)
              ·
                refine ⟨76547586669821257503212557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408253795572380040017133637 76547586669821257503212557)
                ·
                  refine ⟨28705345001182971563704709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76547586669821257503212557 28705345001182971563704709)
                  ·
                    refine ⟨5382252187721807168194633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28705345001182971563704709 5382252187721807168194633)
                    ·
                      refine ⟨4036689140791355376145975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382252187721807168194633 4036689140791355376145975)
                      ·
                        rfl

theorem cell23_7861424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 4, 2].length) (baseStart_7861424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861424 prefixEnd_7861424 := by exact prefixLift 7861424
  have htrace : WordTrace (prefixWord ++ tailWord_7861424) baseStart_7861424 baseEnd_7861424 := by
    simpa [prefixWord, tailWord_7861424, baseEnd_7861424] using wordTrace_append hprefix tailTrace_7861424
  have hstable : (prefixWord ++ tailWord_7861424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861424).length < 2 ^ (prefixWord ++ tailWord_7861424).sum := by decide
  have hdescent : baseEnd_7861424 < baseStart_7861424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861447 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 7]
def baseStart_7861447 : Nat := 118140960795 + 7861447 * 2 ^ 59
def prefixEnd_7861447 : Nat := 4983230072969 + 3 ^ 40 * 7861447 * 2
def baseEnd_7861447 : Nat := 448522327871823198462041

theorem tailTrace_7861447 : CollatzResearch.WordTrace tailWord_7861447 prefixEnd_7861447 448522327871823198462041 := by
  unfold tailWord_7861447
  simp only [CollatzResearch.WordTrace]
  refine ⟨286730527950327622100614595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191153685300218414733743063 286730527950327622100614595)
  ·
    refine ⟨430095791925491433150921893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286730527950327622100614595 430095791925491433150921893)
    ·
      refine ⟨80642960986029643715797855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430095791925491433150921893 80642960986029643715797855)
      ·
        refine ⟨120964441479044465573696783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80642960986029643715797855 120964441479044465573696783)
        ·
          refine ⟨181446662218566698360545175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120964441479044465573696783 181446662218566698360545175)
          ·
            refine ⟨272169993327850047540817763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181446662218566698360545175 272169993327850047540817763)
            ·
              refine ⟨408254989991775071311226645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272169993327850047540817763 408254989991775071311226645)
              ·
                refine ⟨19136952655864456467713749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408254989991775071311226645 19136952655864456467713749)
                ·
                  refine ⟨448522327871823198462041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19136952655864456467713749 448522327871823198462041)
                  ·
                    rfl

theorem cell23_7861447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 7].length) (baseStart_7861447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861447 prefixEnd_7861447 := by exact prefixLift 7861447
  have htrace : WordTrace (prefixWord ++ tailWord_7861447) baseStart_7861447 baseEnd_7861447 := by
    simpa [prefixWord, tailWord_7861447, baseEnd_7861447] using wordTrace_append hprefix tailTrace_7861447
  have hstable : (prefixWord ++ tailWord_7861447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861447).length < 2 ^ (prefixWord ++ tailWord_7861447).sum := by decide
  have hdescent : baseEnd_7861447 < baseStart_7861447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861494 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_7861494 : Nat := 118140960795 + 7861494 * 2 ^ 59
def prefixEnd_7861494 : Nat := 4983230072969 + 3 ^ 40 * 7861494 * 2
def baseEnd_7861494 : Nat := 1345575028145723367423551

theorem tailTrace_7861494 : CollatzResearch.WordTrace tailWord_7861494 prefixEnd_7861494 1345575028145723367423551 := by
  unfold tailWord_7861494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920765136322334320473471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191154828120771566085050357 17920765136322334320473471)
  ·
    refine ⟨26881147704483501480710207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17920765136322334320473471 26881147704483501480710207)
    ·
      refine ⟨40321721556725252221065311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26881147704483501480710207 40321721556725252221065311)
      ·
        refine ⟨60482582335087878331597967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40321721556725252221065311 60482582335087878331597967)
        ·
          refine ⟨90723873502631817497396951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60482582335087878331597967 90723873502631817497396951)
          ·
            refine ⟨136085810253947726246095427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90723873502631817497396951 136085810253947726246095427)
            ·
              refine ⟨204128715380921589369143141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136085810253947726246095427 204128715380921589369143141)
              ·
                refine ⟨38274134133922798006714339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204128715380921589369143141 38274134133922798006714339)
                ·
                  refine ⟨57411201200884197010071509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38274134133922798006714339 57411201200884197010071509)
                  ·
                    refine ⟨1345575028145723367423551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57411201200884197010071509 1345575028145723367423551)
                    ·
                      rfl

theorem cell23_7861494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_7861494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861494 prefixEnd_7861494 := by exact prefixLift 7861494
  have htrace : WordTrace (prefixWord ++ tailWord_7861494) baseStart_7861494 baseEnd_7861494 := by
    simpa [prefixWord, tailWord_7861494, baseEnd_7861494] using wordTrace_append hprefix tailTrace_7861494
  have hstable : (prefixWord ++ tailWord_7861494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861494).length < 2 ^ (prefixWord ++ tailWord_7861494).sum := by decide
  have hdescent : baseEnd_7861494 < baseStart_7861494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861541 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_7861541 : Nat := 118140960795 + 7861541 * 2 ^ 59
def prefixEnd_7861541 : Nat := 4983230072969 + 3 ^ 40 * 7861541 * 2
def baseEnd_7861541 : Nat := 1345583072675977139460979

theorem tailTrace_7861541 : CollatzResearch.WordTrace tailWord_7861541 prefixEnd_7861541 1345583072675977139460979 := by
  unfold tailWord_7861541
  simp only [CollatzResearch.WordTrace]
  refine ⟨286733956411987076154536477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191155970941324717436357651 286733956411987076154536477)
  ·
    refine ⟨107525233654495153557951179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286733956411987076154536477 107525233654495153557951179)
    ·
      refine ⟨161287850481742730336926769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107525233654495153557951179 161287850481742730336926769)
      ·
        refine ⟨120965887861307047752695077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161287850481742730336926769 120965887861307047752695077)
        ·
          refine ⟨22681103973995071453630327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120965887861307047752695077 22681103973995071453630327)
          ·
            refine ⟨34021655960992607180445491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22681103973995071453630327 34021655960992607180445491)
            ·
              refine ⟨51032483941488910770668237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34021655960992607180445491 51032483941488910770668237)
              ·
                refine ⟨19137181478058341539000589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51032483941488910770668237 19137181478058341539000589)
                ·
                  refine ⟨7176443054271878077125221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19137181478058341539000589 7176443054271878077125221)
                  ·
                    refine ⟨1345583072675977139460979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7176443054271878077125221 1345583072675977139460979)
                    ·
                      rfl

theorem cell23_7861541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_7861541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861541 prefixEnd_7861541 := by exact prefixLift 7861541
  have htrace : WordTrace (prefixWord ++ tailWord_7861541) baseStart_7861541 baseEnd_7861541 := by
    simpa [prefixWord, tailWord_7861541, baseEnd_7861541] using wordTrace_append hprefix tailTrace_7861541
  have hstable : (prefixWord ++ tailWord_7861541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861541).length < 2 ^ (prefixWord ++ tailWord_7861541).sum := by decide
  have hdescent : baseEnd_7861541 < baseStart_7861541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861575 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 1, 4]
def baseStart_7861575 : Nat := 118140960795 + 7861575 * 2 ^ 59
def prefixEnd_7861575 : Nat := 4983230072969 + 3 ^ 40 * 7861575 * 2
def baseEnd_7861575 : Nat := 1345588892123394761785927

theorem tailTrace_7861575 : CollatzResearch.WordTrace tailWord_7861575 prefixEnd_7861575 1345588892123394761785927 := by
  unfold tailWord_7861575
  simp only [CollatzResearch.WordTrace]
  refine ⟨286735196493863899961274179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191156797662575933307516119 286735196493863899961274179)
  ·
    refine ⟨430102794740795849941911269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286735196493863899961274179 430102794740795849941911269)
    ·
      refine ⟨80644274013899221864108363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430102794740795849941911269 80644274013899221864108363)
      ·
        refine ⟨120966411020848832796162545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80644274013899221864108363 120966411020848832796162545)
        ·
          refine ⟨90724808265636624597121909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120966411020848832796162545 90724808265636624597121909)
          ·
            refine ⟨8505450774903433555980179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90724808265636624597121909 8505450774903433555980179)
            ·
              refine ⟨12758176162355150333970269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505450774903433555980179 12758176162355150333970269)
              ·
                refine ⟨4784316060883181375238851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12758176162355150333970269 4784316060883181375238851)
                ·
                  refine ⟨7176474091324772062858277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784316060883181375238851 7176474091324772062858277)
                  ·
                    refine ⟨1345588892123394761785927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7176474091324772062858277 1345588892123394761785927)
                    ·
                      rfl

theorem cell23_7861575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_7861575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861575 prefixEnd_7861575 := by exact prefixLift 7861575
  have htrace : WordTrace (prefixWord ++ tailWord_7861575) baseStart_7861575 baseEnd_7861575 := by
    simpa [prefixWord, tailWord_7861575, baseEnd_7861575] using wordTrace_append hprefix tailTrace_7861575
  have hstable : (prefixWord ++ tailWord_7861575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861575).length < 2 ^ (prefixWord ++ tailWord_7861575).sum := by decide
  have hdescent : baseEnd_7861575 < baseStart_7861575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861661 : List Nat := [1, 4, 2, 1, 3, 1, 3, 8]
def baseStart_7861661 : Nat := 118140960795 + 7861661 * 2 ^ 59
def prefixEnd_7861661 : Nat := 4983230072969 + 3 ^ 40 * 7861661 * 2
def baseEnd_7861661 : Nat := 149511512433572998106755

theorem tailTrace_7861661 : CollatzResearch.WordTrace tailWord_7861661 prefixEnd_7861661 149511512433572998106755 := by
  unfold tailWord_7861661
  simp only [CollatzResearch.WordTrace]
  refine ⟨286738333171552336648904837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191158888781034891099269891 286738333171552336648904837)
  ·
    refine ⟨53763437469666063121669657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286738333171552336648904837 53763437469666063121669657)
    ·
      refine ⟨40322578102249547341252243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53763437469666063121669657 40322578102249547341252243)
      ·
        refine ⟨60483867153374321011878365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40322578102249547341252243 60483867153374321011878365)
        ·
          refine ⟨22681450182515370379454387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60483867153374321011878365 22681450182515370379454387)
          ·
            refine ⟨34022175273773055569181581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22681450182515370379454387 34022175273773055569181581)
            ·
              refine ⟨12758315727664895838443093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34022175273773055569181581 12758315727664895838443093)
              ·
                refine ⟨149511512433572998106755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12758315727664895838443093 149511512433572998106755)
                ·
                  rfl

theorem cell23_7861661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 8].length) (baseStart_7861661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861661 prefixEnd_7861661 := by exact prefixLift 7861661
  have htrace : WordTrace (prefixWord ++ tailWord_7861661) baseStart_7861661 baseEnd_7861661 := by
    simpa [prefixWord, tailWord_7861661, baseEnd_7861661] using wordTrace_append hprefix tailTrace_7861661
  have hstable : (prefixWord ++ tailWord_7861661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861661).length < 2 ^ (prefixWord ++ tailWord_7861661).sum := by decide
  have hdescent : baseEnd_7861661 < baseStart_7861661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861689 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 1, 2, 2]
def baseStart_7861689 : Nat := 118140960795 + 7861689 * 2 ^ 59
def prefixEnd_7861689 : Nat := 4983230072969 + 3 ^ 40 * 7861689 * 2
def baseEnd_7861689 : Nat := 4036825213164796839332257

theorem tailTrace_7861689 : CollatzResearch.WordTrace tailWord_7861689 prefixEnd_7861689 4036825213164796839332257 := by
  unfold tailWord_7861689
  simp only [CollatzResearch.WordTrace]
  refine ⟨286739354415450897430924121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191159569610300598287282747 286739354415450897430924121)
  ·
    refine ⟨215054515811588173073193091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286739354415450897430924121 215054515811588173073193091)
    ·
      refine ⟨322581773717382259609789637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215054515811588173073193091 322581773717382259609789637)
      ·
        refine ⟨60484082572009173676835557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322581773717382259609789637 60484082572009173676835557)
        ·
          refine ⟨11340765482251720064406667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60484082572009173676835557 11340765482251720064406667)
          ·
            refine ⟨17011148223377580096610001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11340765482251720064406667 17011148223377580096610001)
            ·
              refine ⟨12758361167533185072457501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17011148223377580096610001 12758361167533185072457501)
              ·
                refine ⟨4784385437824944402171563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12758361167533185072457501 4784385437824944402171563)
                ·
                  refine ⟨7176578156737416603257345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784385437824944402171563 7176578156737416603257345)
                  ·
                    refine ⟨5382433617553062452443009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7176578156737416603257345 5382433617553062452443009)
                    ·
                      refine ⟨4036825213164796839332257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382433617553062452443009 4036825213164796839332257)
                      ·
                        rfl

theorem cell23_7861689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_7861689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861689 prefixEnd_7861689 := by exact prefixLift 7861689
  have htrace : WordTrace (prefixWord ++ tailWord_7861689) baseStart_7861689 baseEnd_7861689 := by
    simpa [prefixWord, tailWord_7861689, baseEnd_7861689] using wordTrace_append hprefix tailTrace_7861689
  have hstable : (prefixWord ++ tailWord_7861689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861689).length < 2 ^ (prefixWord ++ tailWord_7861689).sum := by decide
  have hdescent : baseEnd_7861689 < baseStart_7861689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861721 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_7861721 : Nat := 118140960795 + 7861721 * 2 ^ 59
def prefixEnd_7861721 : Nat := 4983230072969 + 3 ^ 40 * 7861721 * 2
def baseEnd_7861721 : Nat := 1345613881515246904710703

theorem tailTrace_7861721 : CollatzResearch.WordTrace tailWord_7861721 prefixEnd_7861721 1345613881515246904710703 := by
  unfold tailWord_7861721
  simp only [CollatzResearch.WordTrace]
  refine ⟨286740521551334966896089017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191160347700889977930726011 286740521551334966896089017)
  ·
    refine ⟨215055391163501225172066763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286740521551334966896089017 215055391163501225172066763)
    ·
      refine ⟨322583086745251837758100145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215055391163501225172066763 322583086745251837758100145)
      ·
        refine ⟨241937315058938878318575109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322583086745251837758100145 241937315058938878318575109)
        ·
          refine ⟨45363246573551039684732833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241937315058938878318575109 45363246573551039684732833)
          ·
            refine ⟨34022434930163279763549625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45363246573551039684732833 34022434930163279763549625)
            ·
              refine ⟨25516826197622459822662219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34022434930163279763549625 25516826197622459822662219)
              ·
                refine ⟨38275239296433689733993329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25516826197622459822662219 38275239296433689733993329)
                ·
                  refine ⟨28706429472325267300494997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38275239296433689733993329 28706429472325267300494997)
                  ·
                    refine ⟨1345613881515246904710703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28706429472325267300494997 1345613881515246904710703)
                    ·
                      rfl

theorem cell23_7861721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_7861721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861721 prefixEnd_7861721 := by exact prefixLift 7861721
  have htrace : WordTrace (prefixWord ++ tailWord_7861721) baseStart_7861721 baseEnd_7861721 := by
    simpa [prefixWord, tailWord_7861721, baseEnd_7861721] using wordTrace_append hprefix tailTrace_7861721
  have hstable : (prefixWord ++ tailWord_7861721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861721).length < 2 ^ (prefixWord ++ tailWord_7861721).sum := by decide
  have hdescent : baseEnd_7861721 < baseStart_7861721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861722 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3]
def baseStart_7861722 : Nat := 118140960795 + 7861722 * 2 ^ 59
def prefixEnd_7861722 : Nat := 4983230072969 + 3 ^ 40 * 7861722 * 2
def baseEnd_7861722 : Nat := 4036842158026395210219605

theorem tailTrace_7861722 : CollatzResearch.WordTrace tailWord_7861722 prefixEnd_7861722 4036842158026395210219605 := by
  unfold tailWord_7861722
  simp only [CollatzResearch.WordTrace]
  refine ⟨71685139506082836016718855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191160372016220896044583613 71685139506082836016718855)
  ·
    refine ⟨107527709259124254025078283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71685139506082836016718855 107527709259124254025078283)
    ·
      refine ⟨161291563888686381037617425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107527709259124254025078283 161291563888686381037617425)
      ·
        refine ⟨120968672916514785778213069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161291563888686381037617425 120968672916514785778213069)
        ·
          refine ⟨45363252343693044666829901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120968672916514785778213069 45363252343693044666829901)
          ·
            refine ⟨17011219628884891750061213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45363252343693044666829901 17011219628884891750061213)
            ·
              refine ⟨6379207360831834406272955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17011219628884891750061213 6379207360831834406272955)
              ·
                refine ⟨9568811041247751609409433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379207360831834406272955 9568811041247751609409433)
                ·
                  refine ⟨7176608280935813707057075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9568811041247751609409433 7176608280935813707057075)
                  ·
                    refine ⟨10764912421403720560585613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7176608280935813707057075 10764912421403720560585613)
                    ·
                      refine ⟨4036842158026395210219605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10764912421403720560585613 4036842158026395210219605)
                      ·
                        rfl

theorem cell23_7861722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_7861722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861722 prefixEnd_7861722 := by exact prefixLift 7861722
  have htrace : WordTrace (prefixWord ++ tailWord_7861722) baseStart_7861722 baseEnd_7861722 := by
    simpa [prefixWord, tailWord_7861722, baseEnd_7861722] using wordTrace_append hprefix tailTrace_7861722
  have hstable : (prefixWord ++ tailWord_7861722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861722).length < 2 ^ (prefixWord ++ tailWord_7861722).sum := by decide
  have hdescent : baseEnd_7861722 < baseStart_7861722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861728 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 1, 4, 2]
def baseStart_7861728 : Nat := 118140960795 + 7861728 * 2 ^ 59
def prefixEnd_7861728 : Nat := 4983230072969 + 3 ^ 40 * 7861728 * 2
def baseEnd_7861728 : Nat := 4036845238910322186744577

theorem tailTrace_7861728 : CollatzResearch.WordTrace tailWord_7861728 prefixEnd_7861728 4036845238910322186744577 := by
  unfold tailWord_7861728
  simp only [CollatzResearch.WordTrace]
  refine ⟨143370388431154803545796919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191160517908206404727729225 143370388431154803545796919)
  ·
    refine ⟨215055582646732205318695379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143370388431154803545796919 215055582646732205318695379)
    ·
      refine ⟨322583373970098307978043069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215055582646732205318695379 322583373970098307978043069)
      ·
        refine ⟨120968765238786865491766151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322583373970098307978043069 120968765238786865491766151)
        ·
          refine ⟨181453147858180298237649227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120968765238786865491766151 181453147858180298237649227)
          ·
            refine ⟨272179721787270447356473841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181453147858180298237649227 272179721787270447356473841)
            ·
              refine ⟨204134791340452835517355381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272179721787270447356473841 204134791340452835517355381)
              ·
                refine ⟨19137636688167453329752067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204134791340452835517355381 19137636688167453329752067)
                ·
                  refine ⟨28706455032251179994628101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19137636688167453329752067 28706455032251179994628101)
                  ·
                    refine ⟨5382460318547096248992769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28706455032251179994628101 5382460318547096248992769)
                    ·
                      refine ⟨4036845238910322186744577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382460318547096248992769 4036845238910322186744577)
                      ·
                        rfl

theorem cell23_7861728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_7861728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861728 prefixEnd_7861728 := by exact prefixLift 7861728
  have htrace : WordTrace (prefixWord ++ tailWord_7861728) baseStart_7861728 baseEnd_7861728 := by
    simpa [prefixWord, tailWord_7861728, baseEnd_7861728] using wordTrace_append hprefix tailTrace_7861728
  have hstable : (prefixWord ++ tailWord_7861728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861728).length < 2 ^ (prefixWord ++ tailWord_7861728).sum := by decide
  have hdescent : baseEnd_7861728 < baseStart_7861728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861745 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 4, 2, 2]
def baseStart_7861745 : Nat := 118140960795 + 7861745 * 2 ^ 59
def prefixEnd_7861745 : Nat := 4983230072969 + 3 ^ 40 * 7861745 * 2
def baseEnd_7861745 : Nat := 4036853968081448620231999

theorem tailTrace_7861745 : CollatzResearch.WordTrace tailWord_7861745 prefixEnd_7861745 4036853968081448620231999 := by
  unfold tailWord_7861745
  simp only [CollatzResearch.WordTrace]
  refine ⟨286741396903248018994962689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191160931268832012663308459 286741396903248018994962689)
  ·
    refine ⟨215056047677436014246222017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286741396903248018994962689 215056047677436014246222017)
    ·
      refine ⟨161292035758077010684666513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215056047677436014246222017 161292035758077010684666513)
      ·
        refine ⟨120969026818557758013499885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161292035758077010684666513 120969026818557758013499885)
        ·
          refine ⟨45363385056959159255062457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120969026818557758013499885 45363385056959159255062457)
          ·
            refine ⟨34022538792719369441296843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45363385056959159255062457 34022538792719369441296843)
            ·
              refine ⟨51033808189079054161945265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34022538792719369441296843 51033808189079054161945265)
              ·
                refine ⟨38275356141809290621458949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51033808189079054161945265 38275356141809290621458949)
                ·
                  refine ⟨7176629276589241991523553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38275356141809290621458949 7176629276589241991523553)
                  ·
                    refine ⟨5382471957441931493642665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7176629276589241991523553 5382471957441931493642665)
                    ·
                      refine ⟨4036853968081448620231999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382471957441931493642665 4036853968081448620231999)
                      ·
                        rfl

theorem cell23_7861745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_7861745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861745 prefixEnd_7861745 := by exact prefixLift 7861745
  have htrace : WordTrace (prefixWord ++ tailWord_7861745) baseStart_7861745 baseEnd_7861745 := by
    simpa [prefixWord, tailWord_7861745, baseEnd_7861745] using wordTrace_append hprefix tailTrace_7861745
  have hstable : (prefixWord ++ tailWord_7861745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861745).length < 2 ^ (prefixWord ++ tailWord_7861745).sum := by decide
  have hdescent : baseEnd_7861745 < baseStart_7861745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861768 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 5]
def baseStart_7861768 : Nat := 118140960795 + 7861768 * 2 ^ 59
def prefixEnd_7861768 : Nat := 4983230072969 + 3 ^ 40 * 7861768 * 2
def baseEnd_7861768 : Nat := 448540642015166892249377

theorem tailTrace_7861768 : CollatzResearch.WordTrace tailWord_7861768 prefixEnd_7861768 448540642015166892249377 := by
  unfold tailWord_7861768
  simp only [CollatzResearch.WordTrace]
  refine ⟨143371117891082346961524979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191161490521443129282033305 143371117891082346961524979)
  ·
    refine ⟨215056676836623520442287469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143371117891082346961524979 215056676836623520442287469)
    ·
      refine ⟨80646253813733820165857801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215056676836623520442287469 80646253813733820165857801)
      ·
        refine ⟨60484690360300365124393351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80646253813733820165857801 60484690360300365124393351)
        ·
          refine ⟨90727035540450547686590027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60484690360300365124393351 90727035540450547686590027)
          ·
            refine ⟨136090553310675821529885041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90727035540450547686590027 136090553310675821529885041)
            ·
              refine ⟨102067914983006866147413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136090553310675821529885041 102067914983006866147413781)
              ·
                refine ⟨4784433514828446850660021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102067914983006866147413781 4784433514828446850660021)
                ·
                  refine ⟨448540642015166892249377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4784433514828446850660021 448540642015166892249377)
                  ·
                    rfl

theorem cell23_7861768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 5].length) (baseStart_7861768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861768 prefixEnd_7861768 := by exact prefixLift 7861768
  have htrace : WordTrace (prefixWord ++ tailWord_7861768) baseStart_7861768 baseEnd_7861768 := by
    simpa [prefixWord, tailWord_7861768, baseEnd_7861768] using wordTrace_append hprefix tailTrace_7861768
  have hstable : (prefixWord ++ tailWord_7861768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861768).length < 2 ^ (prefixWord ++ tailWord_7861768).sum := by decide
  have hdescent : baseEnd_7861768 < baseStart_7861768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861773 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7861773 : Nat := 118140960795 + 7861773 * 2 ^ 59
def prefixEnd_7861773 : Nat := 4983230072969 + 3 ^ 40 * 7861773 * 2
def baseEnd_7861773 : Nat := 4036868345539774510681871

theorem tailTrace_7861773 : CollatzResearch.WordTrace tailWord_7861773 prefixEnd_7861773 4036868345539774510681871 := by
  unfold tailWord_7861773
  simp only [CollatzResearch.WordTrace]
  refine ⟨286742418147146579776981973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191161612098097719851321315 286742418147146579776981973)
  ·
    refine ⟨6720525425323747963523015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 286742418147146579776981973 6720525425323747963523015)
    ·
      refine ⟨10080788137985621945284523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6720525425323747963523015 10080788137985621945284523)
      ·
        refine ⟨15121182206978432917926785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10080788137985621945284523 15121182206978432917926785)
        ·
          refine ⟨11340886655233824688445089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15121182206978432917926785 11340886655233824688445089)
          ·
            refine ⟨8505664991425368516333817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11340886655233824688445089 8505664991425368516333817)
            ·
              refine ⟨6379248743569026387250363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8505664991425368516333817 6379248743569026387250363)
              ·
                refine ⟨9568873115353539580875545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379248743569026387250363 9568873115353539580875545)
                ·
                  refine ⟨7176654836515154685656659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9568873115353539580875545 7176654836515154685656659)
                  ·
                    refine ⟨10764982254772732028484989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7176654836515154685656659 10764982254772732028484989)
                    ·
                      refine ⟨4036868345539774510681871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10764982254772732028484989 4036868345539774510681871)
                      ·
                        rfl

theorem cell23_7861773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7861773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861773 prefixEnd_7861773 := by exact prefixLift 7861773
  have htrace : WordTrace (prefixWord ++ tailWord_7861773) baseStart_7861773 baseEnd_7861773 := by
    simpa [prefixWord, tailWord_7861773, baseEnd_7861773] using wordTrace_append hprefix tailTrace_7861773
  have hstable : (prefixWord ++ tailWord_7861773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861773).length < 2 ^ (prefixWord ++ tailWord_7861773).sum := by decide
  have hdescent : baseEnd_7861773 < baseStart_7861773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861779 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 2, 2, 2]
def baseStart_7861779 : Nat := 118140960795 + 7861779 * 2 ^ 59
def prefixEnd_7861779 : Nat := 4983230072969 + 3 ^ 40 * 7861779 * 2
def baseEnd_7861779 : Nat := 4036871426423701487206843

theorem tailTrace_7861779 : CollatzResearch.WordTrace tailWord_7861779 prefixEnd_7861779 4036871426423701487206843 := by
  unfold tailWord_7861779
  simp only [CollatzResearch.WordTrace]
  refine ⟨286742636985124842801700391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191161757990083228534466927 286742636985124842801700391)
  ·
    refine ⟨430113955477687264202550587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286742636985124842801700391 430113955477687264202550587)
    ·
      refine ⟨645170933216530896303825881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430113955477687264202550587 645170933216530896303825881)
      ·
        refine ⟨483878199912398172227869411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645170933216530896303825881 483878199912398172227869411)
        ·
          refine ⟨725817299868597258341804117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483878199912398172227869411 725817299868597258341804117)
          ·
            refine ⟨8505671482835124121193017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 725817299868597258341804117 8505671482835124121193017)
            ·
              refine ⟨6379253612126343090894763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8505671482835124121193017 6379253612126343090894763)
              ·
                refine ⟨9568880418189514636342145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379253612126343090894763 9568880418189514636342145)
                ·
                  refine ⟨7176660313642135977256609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9568880418189514636342145 7176660313642135977256609)
                  ·
                    refine ⟨5382495235231601982942457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7176660313642135977256609 5382495235231601982942457)
                    ·
                      refine ⟨4036871426423701487206843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382495235231601982942457 4036871426423701487206843)
                      ·
                        rfl

theorem cell23_7861779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 2, 2].length) (baseStart_7861779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861779 prefixEnd_7861779 := by exact prefixLift 7861779
  have htrace : WordTrace (prefixWord ++ tailWord_7861779) baseStart_7861779 baseEnd_7861779 := by
    simpa [prefixWord, tailWord_7861779, baseEnd_7861779] using wordTrace_append hprefix tailTrace_7861779
  have hstable : (prefixWord ++ tailWord_7861779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861779).length < 2 ^ (prefixWord ++ tailWord_7861779).sum := by decide
  have hdescent : baseEnd_7861779 < baseStart_7861779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861818 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_7861818 : Nat := 118140960795 + 7861818 * 2 ^ 59
def prefixEnd_7861818 : Nat := 4983230072969 + 3 ^ 40 * 7861818 * 2
def baseEnd_7861818 : Nat := 4036891452169226834619163

theorem tailTrace_7861818 : CollatzResearch.WordTrace tailWord_7861818 prefixEnd_7861818 4036891452169226834619163 := by
  unfold tailWord_7861818
  simp only [CollatzResearch.WordTrace]
  refine ⟨71686014857995888115592527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191162706287989034974913405 71686014857995888115592527)
  ·
    refine ⟨107529022286993832173388791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71686014857995888115592527 107529022286993832173388791)
    ·
      refine ⟨161293533430490748260083187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107529022286993832173388791 161293533430490748260083187)
      ·
        refine ⟨241940300145736122390124781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161293533430490748260083187 241940300145736122390124781)
        ·
          refine ⟨90727612554651045896296793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241940300145736122390124781 90727612554651045896296793)
          ·
            refine ⟨68045709415988284422222595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90727612554651045896296793 68045709415988284422222595)
            ·
              refine ⟨102068564123982426633333893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68045709415988284422222595 102068564123982426633333893)
              ·
                refine ⟨19137855773246704993750105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102068564123982426633333893 19137855773246704993750105)
                ·
                  refine ⟨14353391829935028745312579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19137855773246704993750105 14353391829935028745312579)
                  ·
                    refine ⟨21530087744902543117968869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14353391829935028745312579 21530087744902543117968869)
                    ·
                      refine ⟨4036891452169226834619163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21530087744902543117968869 4036891452169226834619163)
                      ·
                        rfl

theorem cell23_7861818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_7861818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861818 prefixEnd_7861818 := by exact prefixLift 7861818
  have htrace : WordTrace (prefixWord ++ tailWord_7861818) baseStart_7861818 baseEnd_7861818 := by
    simpa [prefixWord, tailWord_7861818, baseEnd_7861818] using wordTrace_append hprefix tailTrace_7861818
  have hstable : (prefixWord ++ tailWord_7861818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861818).length < 2 ^ (prefixWord ++ tailWord_7861818).sum := by decide
  have hdescent : baseEnd_7861818 < baseStart_7861818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861838 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_7861838 : Nat := 118140960795 + 7861838 * 2 ^ 59
def prefixEnd_7861838 : Nat := 4983230072969 + 3 ^ 40 * 7861838 * 2
def baseEnd_7861838 : Nat := 4036901721782316756369071

theorem tailTrace_7861838 : CollatzResearch.WordTrace tailWord_7861838 prefixEnd_7861838 4036901721782316756369071 := by
  unfold tailWord_7861838
  simp only [CollatzResearch.WordTrace]
  refine ⟨35843098611488886984762271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191163192594607397252065445 35843098611488886984762271)
  ·
    refine ⟨53764647917233330477143407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35843098611488886984762271 53764647917233330477143407)
    ·
      refine ⟨80646971875849995715715111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53764647917233330477143407 80646971875849995715715111)
      ·
        refine ⟨120970457813774993573572667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80646971875849995715715111 120970457813774993573572667)
        ·
          refine ⟨181455686720662490360359001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120970457813774993573572667 181455686720662490360359001)
          ·
            refine ⟨136091765040496867770269251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181455686720662490360359001 136091765040496867770269251)
            ·
              refine ⟨204137647560745301655403877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136091765040496867770269251 204137647560745301655403877)
              ·
                refine ⟨38275808917639744060388227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204137647560745301655403877 38275808917639744060388227)
                ·
                  refine ⟨57413713376459616090582341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38275808917639744060388227 57413713376459616090582341)
                  ·
                    refine ⟨10765071258086178016984189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57413713376459616090582341 10765071258086178016984189)
                    ·
                      refine ⟨4036901721782316756369071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10765071258086178016984189 4036901721782316756369071)
                      ·
                        rfl

theorem cell23_7861838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_7861838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861838 prefixEnd_7861838 := by exact prefixLift 7861838
  have htrace : WordTrace (prefixWord ++ tailWord_7861838) baseStart_7861838 baseEnd_7861838 := by
    simpa [prefixWord, tailWord_7861838, baseEnd_7861838] using wordTrace_append hprefix tailTrace_7861838
  have hstable : (prefixWord ++ tailWord_7861838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861838).length < 2 ^ (prefixWord ++ tailWord_7861838).sum := by decide
  have hdescent : baseEnd_7861838 < baseStart_7861838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861852 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7861852 : Nat := 118140960795 + 7861852 * 2 ^ 59
def prefixEnd_7861852 : Nat := 4983230072969 + 3 ^ 40 * 7861852 * 2
def baseEnd_7861852 : Nat := 4036908910511479701594007

theorem tailTrace_7861852 : CollatzResearch.WordTrace tailWord_7861852 prefixEnd_7861852 4036908910511479701594007 := by
  unfold tailWord_7861852
  simp only [CollatzResearch.WordTrace]
  refine ⟨143372649756930188134553905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191163533009240250846071873 143372649756930188134553905)
  ·
    refine ⟨107529487317697641100915429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143372649756930188134553905 107529487317697641100915429)
    ·
      refine ⟨20161778872068307706421643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107529487317697641100915429 20161778872068307706421643)
      ·
        refine ⟨30242668308102461559632465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20161778872068307706421643 30242668308102461559632465)
        ·
          refine ⟨22682001231076846169724349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30242668308102461559632465 22682001231076846169724349)
          ·
            refine ⟨8505750461653817313646631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22682001231076846169724349 8505750461653817313646631)
            ·
              refine ⟨12758625692480725970469947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505750461653817313646631 12758625692480725970469947)
              ·
                refine ⟨19137938538721088955704921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12758625692480725970469947 19137938538721088955704921)
                ·
                  refine ⟨14353453904040816716778691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19137938538721088955704921 14353453904040816716778691)
                  ·
                    refine ⟨21530180856061225075168037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14353453904040816716778691 21530180856061225075168037)
                    ·
                      refine ⟨4036908910511479701594007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21530180856061225075168037 4036908910511479701594007)
                      ·
                        rfl

theorem cell23_7861852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7861852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861852 prefixEnd_7861852 := by exact prefixLift 7861852
  have htrace : WordTrace (prefixWord ++ tailWord_7861852) baseStart_7861852 baseEnd_7861852 := by
    simpa [prefixWord, tailWord_7861852, baseEnd_7861852] using wordTrace_append hprefix tailTrace_7861852
  have hstable : (prefixWord ++ tailWord_7861852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861852).length < 2 ^ (prefixWord ++ tailWord_7861852).sum := by decide
  have hdescent : baseEnd_7861852 < baseStart_7861852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861892 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 6]
def baseStart_7861892 : Nat := 118140960795 + 7861892 * 2 ^ 59
def prefixEnd_7861892 : Nat := 4983230072969 + 3 ^ 40 * 7861892 * 2
def baseEnd_7861892 : Nat := 448547716637517727232647

theorem tailTrace_7861892 : CollatzResearch.WordTrace tailWord_7861892 prefixEnd_7861892 448547716637517727232647 := by
  unfold tailWord_7861892
  simp only [CollatzResearch.WordTrace]
  refine ⟨143373379216857731550281965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191164505622476975400375953 143373379216857731550281965)
  ·
    refine ⟨53765017206321649331355737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143373379216857731550281965 53765017206321649331355737)
    ·
      refine ⟨40323762904741236998516803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53765017206321649331355737 40323762904741236998516803)
      ·
        refine ⟨60485644357111855497775205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40323762904741236998516803 60485644357111855497775205)
        ·
          refine ⟨11341058316958472905832851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60485644357111855497775205 11341058316958472905832851)
          ·
            refine ⟨17011587475437709358749277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11341058316958472905832851 17011587475437709358749277)
            ·
              refine ⟨6379345303289141009530979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17011587475437709358749277 6379345303289141009530979)
              ·
                refine ⟨9569017954933711514296469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379345303289141009530979 9569017954933711514296469)
                ·
                  refine ⟨448547716637517727232647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9569017954933711514296469 448547716637517727232647)
                  ·
                    rfl

theorem cell23_7861892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_7861892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861892 prefixEnd_7861892 := by exact prefixLift 7861892
  have htrace : WordTrace (prefixWord ++ tailWord_7861892) baseStart_7861892 baseEnd_7861892 := by
    simpa [prefixWord, tailWord_7861892, baseEnd_7861892] using wordTrace_append hprefix tailTrace_7861892
  have hstable : (prefixWord ++ tailWord_7861892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861892).length < 2 ^ (prefixWord ++ tailWord_7861892).sum := by decide
  have hdescent : baseEnd_7861892 < baseStart_7861892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861895 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_7861895 : Nat := 118140960795 + 7861895 * 2 ^ 59
def prefixEnd_7861895 : Nat := 4983230072969 + 3 ^ 40 * 7861895 * 2
def baseEnd_7861895 : Nat := 4036930990179623033356309

theorem tailTrace_7861895 : CollatzResearch.WordTrace tailWord_7861895 prefixEnd_7861895 4036930990179623033356309 := by
  unfold tailWord_7861895
  simp only [CollatzResearch.WordTrace]
  refine ⟨286746867852704594612923139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191164578568469729741948759 286746867852704594612923139)
  ·
    refine ⟨430120301779056891919384709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286746867852704594612923139 430120301779056891919384709)
    ·
      refine ⟨80647556583573167234884633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430120301779056891919384709 80647556583573167234884633)
      ·
        refine ⟨60485667437679875426163475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80647556583573167234884633 60485667437679875426163475)
        ·
          refine ⟨90728501156519813139245213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60485667437679875426163475 90728501156519813139245213)
          ·
            refine ⟨34023187933694929927216955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90728501156519813139245213 34023187933694929927216955)
            ·
              refine ⟨51034781900542394890825433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34023187933694929927216955 51034781900542394890825433)
              ·
                refine ⟨38276086425406796168119075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51034781900542394890825433 38276086425406796168119075)
                ·
                  refine ⟨57414129638110194252178613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38276086425406796168119075 57414129638110194252178613)
                  ·
                    refine ⟨5382574653572830711141745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57414129638110194252178613 5382574653572830711141745)
                    ·
                      refine ⟨4036930990179623033356309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382574653572830711141745 4036930990179623033356309)
                      ·
                        rfl

theorem cell23_7861895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_7861895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861895 prefixEnd_7861895 := by exact prefixLift 7861895
  have htrace : WordTrace (prefixWord ++ tailWord_7861895) baseStart_7861895 baseEnd_7861895 := by
    simpa [prefixWord, tailWord_7861895, baseEnd_7861895] using wordTrace_append hprefix tailTrace_7861895
  have hstable : (prefixWord ++ tailWord_7861895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861895).length < 2 ^ (prefixWord ++ tailWord_7861895).sum := by decide
  have hdescent : baseEnd_7861895 < baseStart_7861895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861902 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7861902 : Nat := 118140960795 + 7861902 * 2 ^ 59
def prefixEnd_7861902 : Nat := 4983230072969 + 3 ^ 40 * 7861902 * 2
def baseEnd_7861902 : Nat := 4036934584544204505968777

theorem tailTrace_7861902 : CollatzResearch.WordTrace tailWord_7861902 prefixEnd_7861902 4036934584544204505968777 := by
  unfold tailWord_7861902
  simp only [CollatzResearch.WordTrace]
  refine ⟨35843390395459904351053495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191164748775786156538951973 35843390395459904351053495)
  ·
    refine ⟨53765085593189856526580243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35843390395459904351053495 53765085593189856526580243)
    ·
      refine ⟨80647628389784784789870365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53765085593189856526580243 80647628389784784789870365)
      ·
        refine ⟨30242860646169294296201387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80647628389784784789870365 30242860646169294296201387)
        ·
          refine ⟨45364290969253941444302081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30242860646169294296201387 45364290969253941444302081)
          ·
            refine ⟨34023218226940456083226561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45364290969253941444302081 34023218226940456083226561)
            ·
              refine ⟨25517413670205342062419921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34023218226940456083226561 25517413670205342062419921)
              ·
                refine ⟨19138060252654006546814941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25517413670205342062419921 19138060252654006546814941)
                ·
                  refine ⟨7176772594745252455055603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19138060252654006546814941 7176772594745252455055603)
                  ·
                    refine ⟨10765158892117878682583405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7176772594745252455055603 10765158892117878682583405)
                    ·
                      refine ⟨4036934584544204505968777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10765158892117878682583405 4036934584544204505968777)
                      ·
                        rfl

theorem cell23_7861902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7861902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861902 prefixEnd_7861902 := by exact prefixLift 7861902
  have htrace : WordTrace (prefixWord ++ tailWord_7861902) baseStart_7861902 baseEnd_7861902 := by
    simpa [prefixWord, tailWord_7861902, baseEnd_7861902] using wordTrace_append hprefix tailTrace_7861902
  have hstable : (prefixWord ++ tailWord_7861902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861902).length < 2 ^ (prefixWord ++ tailWord_7861902).sum := by decide
  have hdescent : baseEnd_7861902 < baseStart_7861902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861925 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_7861925 : Nat := 118140960795 + 7861925 * 2 ^ 59
def prefixEnd_7861925 : Nat := 4983230072969 + 3 ^ 40 * 7861925 * 2
def baseEnd_7861925 : Nat := 4036946394599257915981171

theorem tailTrace_7861925 : CollatzResearch.WordTrace tailWord_7861925 prefixEnd_7861925 4036946394599257915981171 := by
  unfold tailWord_7861925
  simp only [CollatzResearch.WordTrace]
  refine ⟨286747962042595909736515229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191165308028397273157676819 286747962042595909736515229)
  ·
    refine ⟨107530485765973466151193211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286747962042595909736515229 107530485765973466151193211)
    ·
      refine ⟨161295728648960199226789817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107530485765973466151193211 161295728648960199226789817)
      ·
        refine ⟨120971796486720149420092363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161295728648960199226789817 120971796486720149420092363)
        ·
          refine ⟨181457694730080224130138545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120971796486720149420092363 181457694730080224130138545)
          ·
            refine ⟨136093271047560168097603909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181457694730080224130138545 136093271047560168097603909)
            ·
              refine ⟨25517488321417531518300733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136093271047560168097603909 25517488321417531518300733)
              ·
                refine ⟨9569058120531574319362775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25517488321417531518300733 9569058120531574319362775)
                ·
                  refine ⟨14353587180797361479044163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569058120531574319362775 14353587180797361479044163)
                  ·
                    refine ⟨21530380771196042218566245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14353587180797361479044163 21530380771196042218566245)
                    ·
                      refine ⟨4036946394599257915981171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21530380771196042218566245 4036946394599257915981171)
                      ·
                        rfl

theorem cell23_7861925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_7861925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861925 prefixEnd_7861925 := by exact prefixLift 7861925
  have htrace : WordTrace (prefixWord ++ tailWord_7861925) baseStart_7861925 baseEnd_7861925 := by
    simpa [prefixWord, tailWord_7861925, baseEnd_7861925] using wordTrace_append hprefix tailTrace_7861925
  have hstable : (prefixWord ++ tailWord_7861925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861925).length < 2 ^ (prefixWord ++ tailWord_7861925).sum := by decide
  have hdescent : baseEnd_7861925 < baseStart_7861925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861935 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 2, 4]
def baseStart_7861935 : Nat := 118140960795 + 7861935 * 2 ^ 59
def prefixEnd_7861935 : Nat := 4983230072969 + 3 ^ 40 * 7861935 * 2
def baseEnd_7861935 : Nat := 1345650509801934292285375

theorem tailTrace_7861935 : CollatzResearch.WordTrace tailWord_7861935 prefixEnd_7861935 1345650509801934292285375 := by
  unfold tailWord_7861935
  simp only [CollatzResearch.WordTrace]
  refine ⟨286748326772559681444379259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191165551181706454296252839 286748326772559681444379259)
  ·
    refine ⟨430122490158839522166568889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286748326772559681444379259 430122490158839522166568889)
    ·
      refine ⟨322591867619129641624926667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430122490158839522166568889 322591867619129641624926667)
      ·
        refine ⟨483887801428694462437390001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322591867619129641624926667 483887801428694462437390001)
        ·
          refine ⟨362915851071520846828042501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483887801428694462437390001 362915851071520846828042501)
          ·
            refine ⟨68046722075910158780257969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362915851071520846828042501 68046722075910158780257969)
            ·
              refine ⟨51035041556932619085193477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68046722075910158780257969 51035041556932619085193477)
              ·
                refine ⟨9569070291924866078473777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51035041556932619085193477 9569070291924866078473777)
                ·
                  refine ⟨7176802718943649558855333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9569070291924866078473777 7176802718943649558855333)
                  ·
                    refine ⟨1345650509801934292285375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7176802718943649558855333 1345650509801934292285375)
                    ·
                      rfl

theorem cell23_7861935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_7861935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861935 prefixEnd_7861935 := by exact prefixLift 7861935
  have htrace : WordTrace (prefixWord ++ tailWord_7861935) baseStart_7861935 baseEnd_7861935 := by
    simpa [prefixWord, tailWord_7861935, baseEnd_7861935] using wordTrace_append hprefix tailTrace_7861935
  have hstable : (prefixWord ++ tailWord_7861935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861935).length < 2 ^ (prefixWord ++ tailWord_7861935).sum := by decide
  have hdescent : baseEnd_7861935 < baseStart_7861935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861938 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_7861938 : Nat := 118140960795 + 7861938 * 2 ^ 59
def prefixEnd_7861938 : Nat := 4983230072969 + 3 ^ 40 * 7861938 * 2
def baseEnd_7861938 : Nat := 4036953069847766365118611

theorem tailTrace_7861938 : CollatzResearch.WordTrace tailWord_7861938 prefixEnd_7861938 4036953069847766365118611 := by
  unfold tailWord_7861938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71687109047887203239184617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191165624127699208637825645 71687109047887203239184617)
  ·
    refine ⟨53765331785915402429388463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71687109047887203239184617 53765331785915402429388463)
    ·
      refine ⟨80647997678873103644082695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53765331785915402429388463 80647997678873103644082695)
      ·
        refine ⟨120971996518309655466124043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80647997678873103644082695 120971996518309655466124043)
        ·
          refine ⟨181457994777464483199186065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120971996518309655466124043 181457994777464483199186065)
          ·
            refine ⟨136093496083098362399389549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181457994777464483199186065 136093496083098362399389549)
            ·
              refine ⟨51035061031161885899771081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136093496083098362399389549 51035061031161885899771081)
              ·
                refine ⟨38276295773371414424828311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51035061031161885899771081 38276295773371414424828311)
                ·
                  refine ⟨57414443660057121637242467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38276295773371414424828311 57414443660057121637242467)
                  ·
                    refine ⟨86121665490085682455863701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57414443660057121637242467 86121665490085682455863701)
                    ·
                      refine ⟨4036953069847766365118611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86121665490085682455863701 4036953069847766365118611)
                      ·
                        rfl

theorem cell23_7861938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_7861938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861938 prefixEnd_7861938 := by exact prefixLift 7861938
  have htrace : WordTrace (prefixWord ++ tailWord_7861938) baseStart_7861938 baseEnd_7861938 := by
    simpa [prefixWord, tailWord_7861938, baseEnd_7861938] using wordTrace_append hprefix tailTrace_7861938
  have hstable : (prefixWord ++ tailWord_7861938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861938).length < 2 ^ (prefixWord ++ tailWord_7861938).sum := by decide
  have hdescent : baseEnd_7861938 < baseStart_7861938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861948 : List Nat := [2, 2, 2, 3, 1, 2, 1, 10]
def baseStart_7861948 : Nat := 118140960795 + 7861948 * 2 ^ 59
def prefixEnd_7861948 : Nat := 4983230072969 + 3 ^ 40 * 7861948 * 2
def baseEnd_7861948 : Nat := 149516970542752271333095

theorem tailTrace_7861948 : CollatzResearch.WordTrace tailWord_7861948 prefixEnd_7861948 149516970542752271333095 := by
  unfold tailWord_7861948
  simp only [CollatzResearch.WordTrace]
  refine ⟨143374400460756292332301249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191165867281008389776401665 143374400460756292332301249)
  ·
    refine ⟨107530800345567219249225937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143374400460756292332301249 107530800345567219249225937)
    ·
      refine ⟨80648100259175414436919453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107530800345567219249225937 80648100259175414436919453)
      ·
        refine ⟨30243037597190780413844795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80648100259175414436919453 30243037597190780413844795)
        ·
          refine ⟨45364556395786170620767193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30243037597190780413844795 45364556395786170620767193)
          ·
            refine ⟨34023417296839627965575395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45364556395786170620767193 34023417296839627965575395)
            ·
              refine ⟨51035125945259441948363093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34023417296839627965575395 51035125945259441948363093)
              ·
                refine ⟨149516970542752271333095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51035125945259441948363093 149516970542752271333095)
                ·
                  rfl

theorem cell23_7861948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 10].length) (baseStart_7861948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861948 prefixEnd_7861948 := by exact prefixLift 7861948
  have htrace : WordTrace (prefixWord ++ tailWord_7861948) baseStart_7861948 baseEnd_7861948 := by
    simpa [prefixWord, tailWord_7861948, baseEnd_7861948] using wordTrace_append hprefix tailTrace_7861948
  have hstable : (prefixWord ++ tailWord_7861948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861948).length < 2 ^ (prefixWord ++ tailWord_7861948).sum := by decide
  have hdescent : baseEnd_7861948 < baseStart_7861948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861962 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_7861962 : Nat := 118140960795 + 7861962 * 2 ^ 59
def prefixEnd_7861962 : Nat := 4983230072969 + 3 ^ 40 * 7861962 * 2
def baseEnd_7861962 : Nat := 4036965393383474271218501

theorem tailTrace_7861962 : CollatzResearch.WordTrace tailWord_7861962 prefixEnd_7861962 4036965393383474271218501 := by
  unfold tailWord_7861962
  simp only [CollatzResearch.WordTrace]
  refine ⟨71687327885865466263903035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191166207695641243370408093 71687327885865466263903035)
  ·
    refine ⟨107530991828798199395854553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71687327885865466263903035 107530991828798199395854553)
    ·
      refine ⟨80648243871598649546890915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107530991828798199395854553 80648243871598649546890915)
      ·
        refine ⟨120972365807397974320336373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80648243871598649546890915 120972365807397974320336373)
        ·
          refine ⟨11341159294443560092531535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120972365807397974320336373 11341159294443560092531535)
          ·
            refine ⟨17011738941665340138797303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11341159294443560092531535 17011738941665340138797303)
            ·
              refine ⟨25517608412498010208195955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17011738941665340138797303 25517608412498010208195955)
              ·
                refine ⟨38276412618747015312293933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25517608412498010208195955 38276412618747015312293933)
                ·
                  refine ⟨14353654732030130742110225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38276412618747015312293933 14353654732030130742110225)
                  ·
                    refine ⟨10765241049022598056582669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14353654732030130742110225 10765241049022598056582669)
                    ·
                      refine ⟨4036965393383474271218501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10765241049022598056582669 4036965393383474271218501)
                      ·
                        rfl

theorem cell23_7861962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_7861962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861962 prefixEnd_7861962 := by exact prefixLift 7861962
  have htrace : WordTrace (prefixWord ++ tailWord_7861962) baseStart_7861962 baseEnd_7861962 := by
    simpa [prefixWord, tailWord_7861962, baseEnd_7861962] using wordTrace_append hprefix tailTrace_7861962
  have hstable : (prefixWord ++ tailWord_7861962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861962).length < 2 ^ (prefixWord ++ tailWord_7861962).sum := by decide
  have hdescent : baseEnd_7861962 < baseStart_7861962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861972 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7861972 : Nat := 118140960795 + 7861972 * 2 ^ 59
def prefixEnd_7861972 : Nat := 4983230072969 + 3 ^ 40 * 7861972 * 2
def baseEnd_7861972 : Nat := 4036970528190019232093455

theorem tailTrace_7861972 : CollatzResearch.WordTrace tailWord_7861972 prefixEnd_7861972 4036970528190019232093455 := by
  unfold tailWord_7861972
  simp only [CollatzResearch.WordTrace]
  refine ⟨143374838136712818381738085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191166450848950424508984113 143374838136712818381738085)
  ·
    refine ⟨26882782150633653446575891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143374838136712818381738085 26882782150633653446575891)
    ·
      refine ⟨40324173225950480169863837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26882782150633653446575891 40324173225950480169863837)
      ·
        refine ⟨15121564959731430063698939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40324173225950480169863837 15121564959731430063698939)
        ·
          refine ⟨22682347439597145095548409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15121564959731430063698939 22682347439597145095548409)
          ·
            refine ⟨17011760579697858821661307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22682347439597145095548409 17011760579697858821661307)
            ·
              refine ⟨25517640869546788232491961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17011760579697858821661307 25517640869546788232491961)
              ·
                refine ⟨19138230652160091174368971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25517640869546788232491961 19138230652160091174368971)
                ·
                  refine ⟨28707345978240136761553457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19138230652160091174368971 28707345978240136761553457)
                  ·
                    refine ⟨21530509483680102571165093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28707345978240136761553457 21530509483680102571165093)
                    ·
                      refine ⟨4036970528190019232093455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21530509483680102571165093 4036970528190019232093455)
                      ·
                        rfl

theorem cell23_7861972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7861972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861972 prefixEnd_7861972 := by exact prefixLift 7861972
  have htrace : WordTrace (prefixWord ++ tailWord_7861972) baseStart_7861972 baseEnd_7861972 := by
    simpa [prefixWord, tailWord_7861972, baseEnd_7861972] using wordTrace_append hprefix tailTrace_7861972
  have hstable : (prefixWord ++ tailWord_7861972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861972).length < 2 ^ (prefixWord ++ tailWord_7861972).sum := by decide
  have hdescent : baseEnd_7861972 < baseStart_7861972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7861975 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_7861975 : Nat := 118140960795 + 7861975 * 2 ^ 59
def prefixEnd_7861975 : Nat := 4983230072969 + 3 ^ 40 * 7861975 * 2
def baseEnd_7861975 : Nat := 4036972068631982720355941

theorem tailTrace_7861975 : CollatzResearch.WordTrace tailWord_7861975 prefixEnd_7861975 4036972068631982720355941 := by
  unfold tailWord_7861975
  simp only [CollatzResearch.WordTrace]
  refine ⟨286749785692414768275835379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191166523794943178850556919 286749785692414768275835379)
  ·
    refine ⟨430124678538622152413753069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286749785692414768275835379 430124678538622152413753069)
    ·
      refine ⟨161296754451983307155157401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430124678538622152413753069 161296754451983307155157401)
      ·
        refine ⟨120972565838987480366368051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161296754451983307155157401 120972565838987480366368051)
        ·
          refine ⟨181458848758481220549552077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120972565838987480366368051 181458848758481220549552077)
          ·
            refine ⟨68047068284430457706082029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181458848758481220549552077 68047068284430457706082029)
            ·
              refine ⟨25517650606661421639780761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68047068284430457706082029 25517650606661421639780761)
              ·
                refine ⟨19138237954996066229835571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25517650606661421639780761 19138237954996066229835571)
                ·
                  refine ⟨28707356932494099344753357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19138237954996066229835571 28707356932494099344753357)
                  ·
                    refine ⟨10765258849685287254282509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28707356932494099344753357 10765258849685287254282509)
                    ·
                      refine ⟨4036972068631982720355941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10765258849685287254282509 4036972068631982720355941)
                      ·
                        rfl

theorem cell23_7861975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_7861975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7861975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7861975 prefixEnd_7861975 := by exact prefixLift 7861975
  have htrace : WordTrace (prefixWord ++ tailWord_7861975) baseStart_7861975 baseEnd_7861975 := by
    simpa [prefixWord, tailWord_7861975, baseEnd_7861975] using wordTrace_append hprefix tailTrace_7861975
  have hstable : (prefixWord ++ tailWord_7861975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7861975).length < 2 ^ (prefixWord ++ tailWord_7861975).sum := by decide
  have hdescent : baseEnd_7861975 < baseStart_7861975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7861975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862002 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_7862002 : Nat := 118140960795 + 7862002 * 2 ^ 59
def prefixEnd_7862002 : Nat := 4983230072969 + 3 ^ 40 * 7862002 * 2
def baseEnd_7862002 : Nat := 4036985932609654114718317

theorem tailTrace_7862002 : CollatzResearch.WordTrace tailWord_7862002 prefixEnd_7862002 4036985932609654114718317 := by
  unfold tailWord_7862002
  simp only [CollatzResearch.WordTrace]
  refine ⟨71687692615829237971767065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191167180308877967924712173 71687692615829237971767065)
  ·
    refine ⟨53765769461871928478825299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71687692615829237971767065 53765769461871928478825299)
    ·
      refine ⟨80648654192807892718237949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53765769461871928478825299 80648654192807892718237949)
      ·
        refine ⟨30243245322302959769339231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80648654192807892718237949 30243245322302959769339231)
        ·
          refine ⟨45364867983454439654008847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30243245322302959769339231 45364867983454439654008847)
          ·
            refine ⟨68047301975181659481013271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45364867983454439654008847 68047301975181659481013271)
            ·
              refine ⟨102070952962772489221519907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68047301975181659481013271 102070952962772489221519907)
              ·
                refine ⟨153106429444158733832279861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102070952962772489221519907 153106429444158733832279861)
                ·
                  refine ⟨14353727760389881296776237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153106429444158733832279861 14353727760389881296776237)
                  ·
                    refine ⟨5382647910146205486291089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14353727760389881296776237 5382647910146205486291089)
                    ·
                      refine ⟨4036985932609654114718317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382647910146205486291089 4036985932609654114718317)
                      ·
                        rfl

theorem cell23_7862002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_7862002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862002 prefixEnd_7862002 := by exact prefixLift 7862002
  have htrace : WordTrace (prefixWord ++ tailWord_7862002) baseStart_7862002 baseEnd_7862002 := by
    simpa [prefixWord, tailWord_7862002, baseEnd_7862002] using wordTrace_append hprefix tailTrace_7862002
  have hstable : (prefixWord ++ tailWord_7862002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862002).length < 2 ^ (prefixWord ++ tailWord_7862002).sum := by decide
  have hdescent : baseEnd_7862002 < baseStart_7862002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862049 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7862049 : Nat := 118140960795 + 7862049 * 2 ^ 59
def prefixEnd_7862049 : Nat := 4983230072969 + 3 ^ 40 * 7862049 * 2
def baseEnd_7862049 : Nat := 4037010066200415430830601

theorem tailTrace_7862049 : CollatzResearch.WordTrace tailWord_7862049 prefixEnd_7862049 4037010066200415430830601 := by
  unfold tailWord_7862049
  simp only [CollatzResearch.WordTrace]
  refine ⟨286752484694146678914029201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191168323129431119276019467 286752484694146678914029201)
  ·
    refine ⟨215064363520610009185521901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286752484694146678914029201 215064363520610009185521901)
    ·
      refine ⟨80649136320228753444570713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215064363520610009185521901 80649136320228753444570713)
      ·
        refine ⟨60486852240171565083428035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80649136320228753444570713 60486852240171565083428035)
        ·
          refine ⟨90730278360257347625142053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60486852240171565083428035 90730278360257347625142053)
          ·
            refine ⟨17011927192548252679714135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90730278360257347625142053 17011927192548252679714135)
            ·
              refine ⟨25517890788822379019571203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17011927192548252679714135 25517890788822379019571203)
              ·
                refine ⟨38276836183233568529356805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25517890788822379019571203 38276836183233568529356805)
                ·
                  refine ⟨7176906784356294099254401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38276836183233568529356805 7176906784356294099254401)
                  ·
                    refine ⟨5382680088267220574440801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7176906784356294099254401 5382680088267220574440801)
                    ·
                      refine ⟨4037010066200415430830601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382680088267220574440801 4037010066200415430830601)
                      ·
                        rfl

theorem cell23_7862049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7862049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862049 prefixEnd_7862049 := by exact prefixLift 7862049
  have htrace : WordTrace (prefixWord ++ tailWord_7862049) baseStart_7862049 baseEnd_7862049 := by
    simpa [prefixWord, tailWord_7862049, baseEnd_7862049] using wordTrace_append hprefix tailTrace_7862049
  have hstable : (prefixWord ++ tailWord_7862049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862049).length < 2 ^ (prefixWord ++ tailWord_7862049).sum := by decide
  have hdescent : baseEnd_7862049 < baseStart_7862049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862085 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_7862085 : Nat := 118140960795 + 7862085 * 2 ^ 59
def prefixEnd_7862085 : Nat := 4983230072969 + 3 ^ 40 * 7862085 * 2
def baseEnd_7862085 : Nat := 1345676183834659096660145

theorem tailTrace_7862085 : CollatzResearch.WordTrace tailWord_7862085 prefixEnd_7862085 1345676183834659096660145 := by
  unfold tailWord_7862085
  simp only [CollatzResearch.WordTrace]
  refine ⟨286753797722016257062339709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191169198481344171374893139 286753797722016257062339709)
  ·
    refine ⟨107532674145756096398377391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286753797722016257062339709 107532674145756096398377391)
    ·
      refine ⟨161299011218634144597566087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107532674145756096398377391 161299011218634144597566087)
      ·
        refine ⟨241948516827951216896349131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161299011218634144597566087 241948516827951216896349131)
        ·
          refine ⟨362922775241926825344523697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241948516827951216896349131 362922775241926825344523697)
          ·
            refine ⟨272192081431445119008392773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362922775241926825344523697 272192081431445119008392773)
            ·
              refine ⟨51036015268395959814073645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272192081431445119008392773 51036015268395959814073645)
              ·
                refine ⟨19138505725648484930277617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51036015268395959814073645 19138505725648484930277617)
                ·
                  refine ⟨14353879294236363697708213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19138505725648484930277617 14353879294236363697708213)
                  ·
                    refine ⟨1345676183834659096660145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14353879294236363697708213 1345676183834659096660145)
                    ·
                      rfl

theorem cell23_7862085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_7862085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862085 prefixEnd_7862085 := by exact prefixLift 7862085
  have htrace : WordTrace (prefixWord ++ tailWord_7862085) baseStart_7862085 baseEnd_7862085 := by
    simpa [prefixWord, tailWord_7862085, baseEnd_7862085] using wordTrace_append hprefix tailTrace_7862085
  have hstable : (prefixWord ++ tailWord_7862085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862085).length < 2 ^ (prefixWord ++ tailWord_7862085).sum := by decide
  have hdescent : baseEnd_7862085 < baseStart_7862085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862149 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_7862149 : Nat := 118140960795 + 7862149 * 2 ^ 59
def prefixEnd_7862149 : Nat := 4983230072969 + 3 ^ 40 * 7862149 * 2
def baseEnd_7862149 : Nat := 1345687138088621679860047

theorem tailTrace_7862149 : CollatzResearch.WordTrace tailWord_7862149 prefixEnd_7862149 1345687138088621679860047 := by
  unfold tailWord_7862149
  simp only [CollatzResearch.WordTrace]
  refine ⟨286756131993784395992669501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191170754662522930661779667 286756131993784395992669501)
  ·
    refine ⟨107533549497669148497251063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286756131993784395992669501 107533549497669148497251063)
    ·
      refine ⟨161300324246503722745876595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107533549497669148497251063 161300324246503722745876595)
      ·
        refine ⟨241950486369755584118814893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161300324246503722745876595 241950486369755584118814893)
        ·
          refine ⟨90731432388658344044555585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241950486369755584118814893 90731432388658344044555585)
          ·
            refine ⟨68048574291493758033416689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90731432388658344044555585 68048574291493758033416689)
            ·
              refine ⟨51036430718620318525062517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68048574291493758033416689 51036430718620318525062517)
              ·
                refine ⟨4784665379870654861724611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51036430718620318525062517 4784665379870654861724611)
                ·
                  refine ⟨7176998069805982292586917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784665379870654861724611 7176998069805982292586917)
                  ·
                    refine ⟨1345687138088621679860047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7176998069805982292586917 1345687138088621679860047)
                    ·
                      rfl

theorem cell23_7862149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_7862149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862149 prefixEnd_7862149 := by exact prefixLift 7862149
  have htrace : WordTrace (prefixWord ++ tailWord_7862149) baseStart_7862149 baseEnd_7862149 := by
    simpa [prefixWord, tailWord_7862149, baseEnd_7862149] using wordTrace_append hprefix tailTrace_7862149
  have hstable : (prefixWord ++ tailWord_7862149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862149).length < 2 ^ (prefixWord ++ tailWord_7862149).sum := by decide
  have hdescent : baseEnd_7862149 < baseStart_7862149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862165 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7862165 : Nat := 118140960795 + 7862165 * 2 ^ 59
def prefixEnd_7862165 : Nat := 4983230072969 + 3 ^ 40 * 7862165 * 2
def baseEnd_7862165 : Nat := 4037069629956336976980067

theorem tailTrace_7862165 : CollatzResearch.WordTrace tailWord_7862165 prefixEnd_7862165 4037069629956336976980067 := by
  unfold tailWord_7862165
  simp only [CollatzResearch.WordTrace]
  refine ⟨286756715561726430725251949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191171143707817620483501299 286756715561726430725251949)
  ·
    refine ⟨107533768335647411521969481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286756715561726430725251949 107533768335647411521969481)
    ·
      refine ⟨80650326251735558641477111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107533768335647411521969481 80650326251735558641477111)
      ·
        refine ⟨120975489377603337962215667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80650326251735558641477111 120975489377603337962215667)
        ·
          refine ⟨181463234066405006943323501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120975489377603337962215667 181463234066405006943323501)
          ·
            refine ⟨68048712774901877603746313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181463234066405006943323501 68048712774901877603746313)
            ·
              refine ⟨51036534581176408202809735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68048712774901877603746313 51036534581176408202809735)
              ·
                refine ⟨76554801871764612304214603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51036534581176408202809735 76554801871764612304214603)
                ·
                  refine ⟨114832202807646918456321905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76554801871764612304214603 114832202807646918456321905)
                  ·
                    refine ⟨86124152105735188842241429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114832202807646918456321905 86124152105735188842241429)
                    ·
                      refine ⟨4037069629956336976980067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86124152105735188842241429 4037069629956336976980067)
                      ·
                        rfl

theorem cell23_7862165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7862165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862165 prefixEnd_7862165 := by exact prefixLift 7862165
  have htrace : WordTrace (prefixWord ++ tailWord_7862165) baseStart_7862165 baseEnd_7862165 := by
    simpa [prefixWord, tailWord_7862165, baseEnd_7862165] using wordTrace_append hprefix tailTrace_7862165
  have hstable : (prefixWord ++ tailWord_7862165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862165).length < 2 ^ (prefixWord ++ tailWord_7862165).sum := by decide
  have hdescent : baseEnd_7862165 < baseStart_7862165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862190 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7862190 : Nat := 118140960795 + 7862190 * 2 ^ 59
def prefixEnd_7862190 : Nat := 4983230072969 + 3 ^ 40 * 7862190 * 2
def baseEnd_7862190 : Nat := 4037082466972699379167453

theorem tailTrace_7862190 : CollatzResearch.WordTrace tailWord_7862190 prefixEnd_7862190 4037082466972699379167453 := by
  unfold tailWord_7862190
  simp only [CollatzResearch.WordTrace]
  refine ⟨35844703423329482499364003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191171751591090573329941349 35844703423329482499364003)
  ·
    refine ⟨53767055134994223749046005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35844703423329482499364003 53767055134994223749046005)
    ·
      refine ⟨5040661418905708476473063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53767055134994223749046005 5040661418905708476473063)
      ·
        refine ⟨7560992128358562714709595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040661418905708476473063 7560992128358562714709595)
        ·
          refine ⟨11341488192537844072064393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7560992128358562714709595 11341488192537844072064393)
          ·
            refine ⟨8506116144403383054048295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11341488192537844072064393 8506116144403383054048295)
            ·
              refine ⟨12759174216605074581072443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506116144403383054048295 12759174216605074581072443)
              ·
                refine ⟨19138761324907611871608665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12759174216605074581072443 19138761324907611871608665)
                ·
                  refine ⟨14354070993680708903706499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19138761324907611871608665 14354070993680708903706499)
                  ·
                    refine ⟨21531106490521063355559749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14354070993680708903706499 21531106490521063355559749)
                    ·
                      refine ⟨4037082466972699379167453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21531106490521063355559749 4037082466972699379167453)
                      ·
                        rfl

theorem cell23_7862190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7862190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862190 prefixEnd_7862190 := by exact prefixLift 7862190
  have htrace : WordTrace (prefixWord ++ tailWord_7862190) baseStart_7862190 baseEnd_7862190 := by
    simpa [prefixWord, tailWord_7862190, baseEnd_7862190] using wordTrace_append hprefix tailTrace_7862190
  have hstable : (prefixWord ++ tailWord_7862190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862190).length < 2 ^ (prefixWord ++ tailWord_7862190).sum := by decide
  have hdescent : baseEnd_7862190 < baseStart_7862190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862232 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_7862232 : Nat := 118140960795 + 7862232 * 2 ^ 59
def prefixEnd_7862232 : Nat := 4983230072969 + 3 ^ 40 * 7862232 * 2
def baseEnd_7862232 : Nat := 4037104033160188214842259

theorem tailTrace_7862232 : CollatzResearch.WordTrace tailWord_7862232 prefixEnd_7862232 4037104033160188214842259 := by
  unfold tailWord_7862232
  simp only [CollatzResearch.WordTrace]
  refine ⟨143379579626241850583970475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191172772834989134111960633 143379579626241850583970475)
  ·
    refine ⟨215069369439362775875955713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143379579626241850583970475 215069369439362775875955713)
    ·
      refine ⟨161302027079522081906966785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215069369439362775875955713 161302027079522081906966785)
      ·
        refine ⟨120976520309641561430225089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161302027079522081906966785 120976520309641561430225089)
        ·
          refine ⟨90732390232231171072668817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120976520309641561430225089 90732390232231171072668817)
          ·
            refine ⟨68049292674173378304501613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90732390232231171072668817 68049292674173378304501613)
            ·
              refine ⟨25518484752815016864188105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68049292674173378304501613 25518484752815016864188105)
              ·
                refine ⟨19138863564611262648141079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25518484752815016864188105 19138863564611262648141079)
                ·
                  refine ⟨28708295346916893972211619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19138863564611262648141079 28708295346916893972211619)
                  ·
                    refine ⟨43062443020375340958317429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28708295346916893972211619 43062443020375340958317429)
                    ·
                      refine ⟨4037104033160188214842259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43062443020375340958317429 4037104033160188214842259)
                      ·
                        rfl

theorem cell23_7862232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_7862232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862232 prefixEnd_7862232 := by exact prefixLift 7862232
  have htrace : WordTrace (prefixWord ++ tailWord_7862232) baseStart_7862232 baseEnd_7862232 := by
    simpa [prefixWord, tailWord_7862232, baseEnd_7862232] using wordTrace_append hprefix tailTrace_7862232
  have hstable : (prefixWord ++ tailWord_7862232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862232).length < 2 ^ (prefixWord ++ tailWord_7862232).sum := by decide
  have hdescent : baseEnd_7862232 < baseStart_7862232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862239 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 1, 6]
def baseStart_7862239 : Nat := 118140960795 + 7862239 * 2 ^ 59
def prefixEnd_7862239 : Nat := 4983230072969 + 3 ^ 40 * 7862239 * 2
def baseEnd_7862239 : Nat := 1345702542508256562484909

theorem tailTrace_7862239 : CollatzResearch.WordTrace tailWord_7862239 prefixEnd_7862239 1345702542508256562484909 := by
  unfold tailWord_7862239
  simp only [CollatzResearch.WordTrace]
  refine ⟨286759414563458341363445771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191172943042305560908963847 286759414563458341363445771)
  ·
    refine ⟨430139121845187512045168657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286759414563458341363445771 430139121845187512045168657)
    ·
      refine ⟨322604341383890634033876493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430139121845187512045168657 322604341383890634033876493)
      ·
        refine ⟨120976628018958987762703685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322604341383890634033876493 120976628018958987762703685)
        ·
          refine ⟨22683117753554810205506941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120976628018958987762703685 22683117753554810205506941)
          ·
            refine ⟨8506169157583053827065103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22683117753554810205506941 8506169157583053827065103)
            ·
              refine ⟨12759253736374580740597655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506169157583053827065103 12759253736374580740597655)
              ·
                refine ⟨19138880604561871110896483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12759253736374580740597655 19138880604561871110896483)
                ·
                  refine ⟨28708320906842806666344725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19138880604561871110896483 28708320906842806666344725)
                  ·
                    refine ⟨1345702542508256562484909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28708320906842806666344725 1345702542508256562484909)
                    ·
                      rfl

theorem cell23_7862239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_7862239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862239 prefixEnd_7862239 := by exact prefixLift 7862239
  have htrace : WordTrace (prefixWord ++ tailWord_7862239) baseStart_7862239 baseEnd_7862239 := by
    simpa [prefixWord, tailWord_7862239, baseEnd_7862239] using wordTrace_append hprefix tailTrace_7862239
  have hstable : (prefixWord ++ tailWord_7862239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862239).length < 2 ^ (prefixWord ++ tailWord_7862239).sum := by decide
  have hdescent : baseEnd_7862239 < baseStart_7862239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862280 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_7862280 : Nat := 118140960795 + 7862280 * 2 ^ 59
def prefixEnd_7862280 : Nat := 4983230072969 + 3 ^ 40 * 7862280 * 2
def baseEnd_7862280 : Nat := 4037128680231604027042039

theorem tailTrace_7862280 : CollatzResearch.WordTrace tailWord_7862280 prefixEnd_7862280 4037128680231604027042039 := by
  unfold tailWord_7862280
  simp only [CollatzResearch.WordTrace]
  refine ⟨143380454978154902682844147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191173939970873203577125529 143380454978154902682844147)
  ·
    refine ⟨215070682467232354024266221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143380454978154902682844147 215070682467232354024266221)
    ·
      refine ⟨80651505925212132759099833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215070682467232354024266221 80651505925212132759099833)
      ·
        refine ⟨60488629443909099569324875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80651505925212132759099833 60488629443909099569324875)
        ·
          refine ⟨90732944165863649353987313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60488629443909099569324875 90732944165863649353987313)
          ·
            refine ⟨68049708124397737015490485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90732944165863649353987313 68049708124397737015490485)
            ·
              refine ⟨6379660136662287845202233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68049708124397737015490485 6379660136662287845202233)
              ·
                refine ⟨4784745102496715883901675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379660136662287845202233 4784745102496715883901675)
                ·
                  refine ⟨7177117653745073825852513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784745102496715883901675 7177117653745073825852513)
                  ·
                    refine ⟨5382838240308805369389385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7177117653745073825852513 5382838240308805369389385)
                    ·
                      refine ⟨4037128680231604027042039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382838240308805369389385 4037128680231604027042039)
                      ·
                        rfl

theorem cell23_7862280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_7862280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862280 prefixEnd_7862280 := by exact prefixLift 7862280
  have htrace : WordTrace (prefixWord ++ tailWord_7862280) baseStart_7862280 baseEnd_7862280 := by
    simpa [prefixWord, tailWord_7862280, baseEnd_7862280] using wordTrace_append hprefix tailTrace_7862280
  have hstable : (prefixWord ++ tailWord_7862280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862280).length < 2 ^ (prefixWord ++ tailWord_7862280).sum := by decide
  have hdescent : baseEnd_7862280 < baseStart_7862280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862296 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_7862296 : Nat := 118140960795 + 7862296 * 2 ^ 59
def prefixEnd_7862296 : Nat := 4983230072969 + 3 ^ 40 * 7862296 * 2
def baseEnd_7862296 : Nat := 4037136895922075964441965

theorem tailTrace_7862296 : CollatzResearch.WordTrace tailWord_7862296 prefixEnd_7862296 4037136895922075964441965 := by
  unfold tailWord_7862296
  simp only [CollatzResearch.WordTrace]
  refine ⟨143380746762125920049135371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191174329016167893398847161 143380746762125920049135371)
  ·
    refine ⟨215071120143188880073703057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143380746762125920049135371 215071120143188880073703057)
    ·
      refine ⟨161303340107391660055277293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215071120143188880073703057 161303340107391660055277293)
      ·
        refine ⟨60488752540271872520728985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161303340107391660055277293 60488752540271872520728985)
        ·
          refine ⟨45366564405203904390546739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60488752540271872520728985 45366564405203904390546739)
          ·
            refine ⟨68049846607805856585820109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45366564405203904390546739 68049846607805856585820109)
            ·
              refine ⟨25518692477927196219682541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68049846607805856585820109 25518692477927196219682541)
              ·
                refine ⟨9569509679222698582380953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25518692477927196219682541 9569509679222698582380953)
                ·
                  refine ⟨7177132259417023936785715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9569509679222698582380953 7177132259417023936785715)
                  ·
                    refine ⟨10765698389125535905178573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7177132259417023936785715 10765698389125535905178573)
                    ·
                      refine ⟨4037136895922075964441965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10765698389125535905178573 4037136895922075964441965)
                      ·
                        rfl

theorem cell23_7862296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_7862296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862296 prefixEnd_7862296 := by exact prefixLift 7862296
  have htrace : WordTrace (prefixWord ++ tailWord_7862296) baseStart_7862296 baseEnd_7862296 := by
    simpa [prefixWord, tailWord_7862296, baseEnd_7862296] using wordTrace_append hprefix tailTrace_7862296
  have hstable : (prefixWord ++ tailWord_7862296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862296).length < 2 ^ (prefixWord ++ tailWord_7862296).sum := by decide
  have hdescent : baseEnd_7862296 < baseStart_7862296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862306 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_7862306 : Nat := 118140960795 + 7862306 * 2 ^ 59
def prefixEnd_7862306 : Nat := 4983230072969 + 3 ^ 40 * 7862306 * 2
def baseEnd_7862306 : Nat := 4037142030728620925316919

theorem tailTrace_7862306 : CollatzResearch.WordTrace tailWord_7862306 prefixEnd_7862306 4037142030728620925316919 := by
  unfold tailWord_7862306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71690464563553902951533693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191174572169477074537423181 71690464563553902951533693)
  ·
    refine ⟨26883924211332713606825135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71690464563553902951533693 26883924211332713606825135)
    ·
      refine ⟨40325886316999070410237703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26883924211332713606825135 40325886316999070410237703)
      ·
        refine ⟨60488829475498605615356555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40325886316999070410237703 60488829475498605615356555)
        ·
          refine ⟨90733244213247908423034833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60488829475498605615356555 90733244213247908423034833)
          ·
            refine ⟨68049933159935931317276125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90733244213247908423034833 68049933159935931317276125)
            ·
              refine ⟨25518724934975974243978547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68049933159935931317276125 25518724934975974243978547)
              ·
                refine ⟨38278087402463961365967821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25518724934975974243978547 38278087402463961365967821)
                ·
                  refine ⟨14354282775923985512237933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38278087402463961365967821 14354282775923985512237933)
                  ·
                    refine ⟨5382856040971494567089225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14354282775923985512237933 5382856040971494567089225)
                    ·
                      refine ⟨4037142030728620925316919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5382856040971494567089225 4037142030728620925316919)
                      ·
                        rfl

theorem cell23_7862306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_7862306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862306 prefixEnd_7862306 := by exact prefixLift 7862306
  have htrace : WordTrace (prefixWord ++ tailWord_7862306) baseStart_7862306 baseEnd_7862306 := by
    simpa [prefixWord, tailWord_7862306, baseEnd_7862306] using wordTrace_append hprefix tailTrace_7862306
  have hstable : (prefixWord ++ tailWord_7862306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862306).length < 2 ^ (prefixWord ++ tailWord_7862306).sum := by decide
  have hdescent : baseEnd_7862306 < baseStart_7862306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862479 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 3, 5]
def baseStart_7862479 : Nat := 118140960795 + 7862479 * 2 ^ 59
def prefixEnd_7862479 : Nat := 4983230072969 + 3 ^ 40 * 7862479 * 2
def baseEnd_7862479 : Nat := 1345743620960616249484541

theorem tailTrace_7862479 : CollatzResearch.WordTrace tailWord_7862479 prefixEnd_7862479 1345743620960616249484541 := by
  unfold tailWord_7862479
  simp only [CollatzResearch.WordTrace]
  refine ⟨286768168082588862352182491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191178778721725908234788327 286768168082588862352182491)
  ·
    refine ⟨430152252123883293528273737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286768168082588862352182491 430152252123883293528273737)
    ·
      refine ⟨322614189092912470146205303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430152252123883293528273737 322614189092912470146205303)
      ·
        refine ⟨483921283639368705219307955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322614189092912470146205303 483921283639368705219307955)
        ·
          refine ⟨725881925459053057828961933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483921283639368705219307955 725881925459053057828961933)
          ·
            refine ⟨272205722047144896685860725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 725881925459053057828961933 272205722047144896685860725)
            ·
              refine ⟨25519286441919834064299443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272205722047144896685860725 25519286441919834064299443)
              ·
                refine ⟨38278929662879751096449165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25519286441919834064299443 38278929662879751096449165)
                ·
                  refine ⟨14354598623579906661168437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38278929662879751096449165 14354598623579906661168437)
                  ·
                    refine ⟨1345743620960616249484541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14354598623579906661168437 1345743620960616249484541)
                    ·
                      rfl

theorem cell23_7862479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_7862479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862479 prefixEnd_7862479 := by exact prefixLift 7862479
  have htrace : WordTrace (prefixWord ++ tailWord_7862479) baseStart_7862479 baseEnd_7862479 := by
    simpa [prefixWord, tailWord_7862479, baseEnd_7862479] using wordTrace_append hprefix tailTrace_7862479
  have hstable : (prefixWord ++ tailWord_7862479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862479).length < 2 ^ (prefixWord ++ tailWord_7862479).sum := by decide
  have hdescent : baseEnd_7862479 < baseStart_7862479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862519 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_7862519 : Nat := 118140960795 + 7862519 * 2 ^ 59
def prefixEnd_7862519 : Nat := 4983230072969 + 3 ^ 40 * 7862519 * 2
def baseEnd_7862519 : Nat := 4037251402108028591953439

theorem tailTrace_7862519 : CollatzResearch.WordTrace tailWord_7862519 prefixEnd_7862519 4037251402108028591953439 := by
  unfold tailWord_7862519
  simp only [CollatzResearch.WordTrace]
  refine ⟨286769627002443949183638611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191179751334962632789092407 286769627002443949183638611)
  ·
    refine ⟨430154440503665923775457917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286769627002443949183638611 430154440503665923775457917)
    ·
      refine ⟨161307915188874721415796719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430154440503665923775457917 161307915188874721415796719)
      ·
        refine ⟨241961872783312082123695079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161307915188874721415796719 241961872783312082123695079)
        ·
          refine ⟨362942809174968123185542619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241961872783312082123695079 362942809174968123185542619)
          ·
            refine ⟨544414213762452184778313929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362942809174968123185542619 544414213762452184778313929)
            ·
              refine ⟨408310660321839138583735447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544414213762452184778313929 408310660321839138583735447)
              ·
                refine ⟨612465990482758707875603171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408310660321839138583735447 612465990482758707875603171)
                ·
                  refine ⟨918698985724138061813404757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612465990482758707875603171 918698985724138061813404757)
                  ·
                    refine ⟨10766003738954742911875837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 918698985724138061813404757 10766003738954742911875837)
                    ·
                      refine ⟨4037251402108028591953439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766003738954742911875837 4037251402108028591953439)
                      ·
                        rfl

theorem cell23_7862519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_7862519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862519 prefixEnd_7862519 := by exact prefixLift 7862519
  have htrace : WordTrace (prefixWord ++ tailWord_7862519) baseStart_7862519 baseEnd_7862519 := by
    simpa [prefixWord, tailWord_7862519, baseEnd_7862519] using wordTrace_append hprefix tailTrace_7862519
  have hstable : (prefixWord ++ tailWord_7862519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862519).length < 2 ^ (prefixWord ++ tailWord_7862519).sum := by decide
  have hdescent : baseEnd_7862519 < baseStart_7862519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862560 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 2, 4]
def baseStart_7862560 : Nat := 118140960795 + 7862560 * 2 ^ 59
def prefixEnd_7862560 : Nat := 4983230072969 + 3 ^ 40 * 7862560 * 2
def baseEnd_7862560 : Nat := 1345757484938287643846917

theorem tailTrace_7862560 : CollatzResearch.WordTrace tailWord_7862560 prefixEnd_7862560 1345757484938287643846917 := by
  unfold tailWord_7862560
  simp only [CollatzResearch.WordTrace]
  refine ⟨143385561197647706592940567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191180748263530275457254089 143385561197647706592940567)
  ·
    refine ⟨215078341796471559889410851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143385561197647706592940567 215078341796471559889410851)
    ·
      refine ⟨322617512694707339834116277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215078341796471559889410851 322617512694707339834116277)
      ·
        refine ⟨30245391815128813109448401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322617512694707339834116277 30245391815128813109448401)
        ·
          refine ⟨22684043861346609832086301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30245391815128813109448401 22684043861346609832086301)
          ·
            refine ⟨8506516448004978687032363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22684043861346609832086301 8506516448004978687032363)
            ·
              refine ⟨12759774672007468030548545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506516448004978687032363 12759774672007468030548545)
              ·
                refine ⟨9569831004005601022911409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12759774672007468030548545 9569831004005601022911409)
                ·
                  refine ⟨7177373253004200767183557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9569831004005601022911409 7177373253004200767183557)
                  ·
                    refine ⟨1345757484938287643846917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7177373253004200767183557 1345757484938287643846917)
                    ·
                      rfl

theorem cell23_7862560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_7862560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862560 prefixEnd_7862560 := by exact prefixLift 7862560
  have htrace : WordTrace (prefixWord ++ tailWord_7862560) baseStart_7862560 baseEnd_7862560 := by
    simpa [prefixWord, tailWord_7862560, baseEnd_7862560] using wordTrace_append hprefix tailTrace_7862560
  have hstable : (prefixWord ++ tailWord_7862560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862560).length < 2 ^ (prefixWord ++ tailWord_7862560).sum := by decide
  have hdescent : baseEnd_7862560 < baseStart_7862560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862576 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 7, 2]
def baseStart_7862576 : Nat := 118140960795 + 7862576 * 2 ^ 59
def prefixEnd_7862576 : Nat := 4983230072969 + 3 ^ 40 * 7862576 * 2
def baseEnd_7862576 : Nat := 4037280670505334868940677

theorem tailTrace_7862576 : CollatzResearch.WordTrace tailWord_7862576 prefixEnd_7862576 4037280670505334868940677 := by
  unfold tailWord_7862576
  simp only [CollatzResearch.WordTrace]
  refine ⟨143385852981618723959231791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191181137308824965278975721 143385852981618723959231791)
  ·
    refine ⟨215078779472428085938847687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143385852981618723959231791 215078779472428085938847687)
    ·
      refine ⟨322618169208642128908271531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215078779472428085938847687 322618169208642128908271531)
      ·
        refine ⟨483927253812963193362407297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322618169208642128908271531 483927253812963193362407297)
        ·
          refine ⟨362945440359722395021805473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483927253812963193362407297 362945440359722395021805473)
          ·
            refine ⟨272209080269791796266354105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362945440359722395021805473 272209080269791796266354105)
            ·
              refine ⟨204156810202343847199765579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272209080269791796266354105 204156810202343847199765579)
              ·
                refine ⟨306235215303515770799648369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204156810202343847199765579 306235215303515770799648369)
                ·
                  refine ⟨229676411477636828099736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306235215303515770799648369 229676411477636828099736277)
                  ·
                    refine ⟨5383040894007113158587569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 229676411477636828099736277 5383040894007113158587569)
                    ·
                      refine ⟨4037280670505334868940677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383040894007113158587569 4037280670505334868940677)
                      ·
                        rfl

theorem cell23_7862576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 7, 2].length) (baseStart_7862576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862576 prefixEnd_7862576 := by exact prefixLift 7862576
  have htrace : WordTrace (prefixWord ++ tailWord_7862576) baseStart_7862576 baseEnd_7862576 := by
    simpa [prefixWord, tailWord_7862576, baseEnd_7862576] using wordTrace_append hprefix tailTrace_7862576
  have hstable : (prefixWord ++ tailWord_7862576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862576).length < 2 ^ (prefixWord ++ tailWord_7862576).sum := by decide
  have hdescent : baseEnd_7862576 < baseStart_7862576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862580 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_7862580 : Nat := 118140960795 + 7862580 * 2 ^ 59
def prefixEnd_7862580 : Nat := 4983230072969 + 3 ^ 40 * 7862580 * 2
def baseEnd_7862580 : Nat := 4037282724427952853290659

theorem tailTrace_7862580 : CollatzResearch.WordTrace tailWord_7862580 prefixEnd_7862580 4037282724427952853290659 := by
  unfold tailWord_7862580
  simp only [CollatzResearch.WordTrace]
  refine ⟨143385925927611478300804597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191181234570148637734406129 143385925927611478300804597)
  ·
    refine ⟨13442430555713576090700431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143385925927611478300804597 13442430555713576090700431)
    ·
      refine ⟨20163645833570364136050647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13442430555713576090700431 20163645833570364136050647)
      ·
        refine ⟨30245468750355546204075971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20163645833570364136050647 30245468750355546204075971)
        ·
          refine ⟨45368203125533319306113957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30245468750355546204075971 45368203125533319306113957)
          ·
            refine ⟨8506538086037497369896367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45368203125533319306113957 8506538086037497369896367)
            ·
              refine ⟨12759807129056246054844551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506538086037497369896367 12759807129056246054844551)
              ·
                refine ⟨19139710693584369082266827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12759807129056246054844551 19139710693584369082266827)
                ·
                  refine ⟨28709566040376553623400241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19139710693584369082266827 28709566040376553623400241)
                  ·
                    refine ⟨21532174530282415217550181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28709566040376553623400241 21532174530282415217550181)
                    ·
                      refine ⟨4037282724427952853290659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21532174530282415217550181 4037282724427952853290659)
                      ·
                        rfl

theorem cell23_7862580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_7862580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862580 prefixEnd_7862580 := by exact prefixLift 7862580
  have htrace : WordTrace (prefixWord ++ tailWord_7862580) baseStart_7862580 baseEnd_7862580 := by
    simpa [prefixWord, tailWord_7862580, baseEnd_7862580] using wordTrace_append hprefix tailTrace_7862580
  have hstable : (prefixWord ++ tailWord_7862580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862580).length < 2 ^ (prefixWord ++ tailWord_7862580).sum := by decide
  have hdescent : baseEnd_7862580 < baseStart_7862580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862583 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_7862583 : Nat := 118140960795 + 7862583 * 2 ^ 59
def prefixEnd_7862583 : Nat := 4983230072969 + 3 ^ 40 * 7862583 * 2
def baseEnd_7862583 : Nat := 4037284264869916341553145

theorem tailTrace_7862583 : CollatzResearch.WordTrace tailWord_7862583 prefixEnd_7862583 4037284264869916341553145 := by
  unfold tailWord_7862583
  simp only [CollatzResearch.WordTrace]
  refine ⟨286771961274212088113968403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191181307516141392075978935 286771961274212088113968403)
  ·
    refine ⟨430157941911318132170952605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286771961274212088113968403 430157941911318132170952605)
    ·
      refine ⟨161309228216744299564107227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430157941911318132170952605 161309228216744299564107227)
      ·
        refine ⟨241963842325116449346160841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161309228216744299564107227 241963842325116449346160841)
        ·
          refine ⟨181472881743837337009620631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241963842325116449346160841 181472881743837337009620631)
          ·
            refine ⟨272209322615756005514430947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181472881743837337009620631 272209322615756005514430947)
            ·
              refine ⟨408313983923634008271646421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272209322615756005514430947 408313983923634008271646421)
              ·
                refine ⟨9569858998210172068866713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 408313983923634008271646421 9569858998210172068866713)
                ·
                  refine ⟨7177394248657629051650035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9569858998210172068866713 7177394248657629051650035)
                  ·
                    refine ⟨10766091372986443577475053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7177394248657629051650035 10766091372986443577475053)
                    ·
                      refine ⟨4037284264869916341553145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766091372986443577475053 4037284264869916341553145)
                      ·
                        rfl

theorem cell23_7862583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_7862583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862583 prefixEnd_7862583 := by exact prefixLift 7862583
  have htrace : WordTrace (prefixWord ++ tailWord_7862583) baseStart_7862583 baseEnd_7862583 := by
    simpa [prefixWord, tailWord_7862583, baseEnd_7862583] using wordTrace_append hprefix tailTrace_7862583
  have hstable : (prefixWord ++ tailWord_7862583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862583).length < 2 ^ (prefixWord ++ tailWord_7862583).sum := by decide
  have hdescent : baseEnd_7862583 < baseStart_7862583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862610 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_7862610 : Nat := 118140960795 + 7862610 * 2 ^ 59
def prefixEnd_7862610 : Nat := 4983230072969 + 3 ^ 40 * 7862610 * 2
def baseEnd_7862610 : Nat := 4037298128847587735915521

theorem tailTrace_7862610 : CollatzResearch.WordTrace tailWord_7862610 prefixEnd_7862610 4037298128847587735915521 := by
  unfold tailWord_7862610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71693236511278567931300321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191181964030076181150134189 71693236511278567931300321)
  ·
    refine ⟨53769927383458925948475241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71693236511278567931300321 53769927383458925948475241)
    ·
      refine ⟨40327445537594194461356431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53769927383458925948475241 40327445537594194461356431)
      ·
        refine ⟨60491168306391291692034647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40327445537594194461356431 60491168306391291692034647)
        ·
          refine ⟨90736752459586937538051971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60491168306391291692034647 90736752459586937538051971)
          ·
            refine ⟨136105128689380406307077957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90736752459586937538051971 136105128689380406307077957)
            ·
              refine ⟨25519711629258826182577117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136105128689380406307077957 25519711629258826182577117)
              ·
                refine ⟨9569891860972059818466419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25519711629258826182577117 9569891860972059818466419)
                ·
                  refine ⟨14354837791458089727699629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569891860972059818466419 14354837791458089727699629)
                  ·
                    refine ⟨5383064171796783647887361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14354837791458089727699629 5383064171796783647887361)
                    ·
                      refine ⟨4037298128847587735915521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383064171796783647887361 4037298128847587735915521)
                      ·
                        rfl

theorem cell23_7862610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_7862610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862610 prefixEnd_7862610 := by exact prefixLift 7862610
  have htrace : WordTrace (prefixWord ++ tailWord_7862610) baseStart_7862610 baseEnd_7862610 := by
    simpa [prefixWord, tailWord_7862610, baseEnd_7862610] using wordTrace_append hprefix tailTrace_7862610
  have hstable : (prefixWord ++ tailWord_7862610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862610).length < 2 ^ (prefixWord ++ tailWord_7862610).sum := by decide
  have hdescent : baseEnd_7862610 < baseStart_7862610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862634 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7862634 : Nat := 118140960795 + 7862634 * 2 ^ 59
def prefixEnd_7862634 : Nat := 4983230072969 + 3 ^ 40 * 7862634 * 2
def baseEnd_7862634 : Nat := 4037310452383295642015411

theorem tailTrace_7862634 : CollatzResearch.WordTrace tailWord_7862634 prefixEnd_7862634 4037310452383295642015411 := by
  unfold tailWord_7862634
  simp only [CollatzResearch.WordTrace]
  refine ⟨71693455349256830956018739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191182547598018215882716637 71693455349256830956018739)
  ·
    refine ⟨107540183023885246434028109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71693455349256830956018739 107540183023885246434028109)
    ·
      refine ⟨40327568633956967412760541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107540183023885246434028109 40327568633956967412760541)
      ·
        refine ⟨15122838237733862779785203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40327568633956967412760541 15122838237733862779785203)
        ·
          refine ⟨22684257356600794169677805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15122838237733862779785203 22684257356600794169677805)
          ·
            refine ⟨8506596508725297813629177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22684257356600794169677805 8506596508725297813629177)
            ·
              refine ⟨6379947381543973360221883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8506596508725297813629177 6379947381543973360221883)
              ·
                refine ⟨9569921072315960040332825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379947381543973360221883 9569921072315960040332825)
                ·
                  refine ⟨7177440804236970030249619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9569921072315960040332825 7177440804236970030249619)
                  ·
                    refine ⟨10766161206355455045374429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7177440804236970030249619 10766161206355455045374429)
                    ·
                      refine ⟨4037310452383295642015411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766161206355455045374429 4037310452383295642015411)
                      ·
                        rfl

theorem cell23_7862634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7862634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862634 prefixEnd_7862634 := by exact prefixLift 7862634
  have htrace : WordTrace (prefixWord ++ tailWord_7862634) baseStart_7862634 baseEnd_7862634 := by
    simpa [prefixWord, tailWord_7862634, baseEnd_7862634] using wordTrace_append hprefix tailTrace_7862634
  have hstable : (prefixWord ++ tailWord_7862634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862634).length < 2 ^ (prefixWord ++ tailWord_7862634).sum := by decide
  have hdescent : baseEnd_7862634 < baseStart_7862634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862656 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_7862656 : Nat := 118140960795 + 7862656 * 2 ^ 59
def prefixEnd_7862656 : Nat := 4983230072969 + 3 ^ 40 * 7862656 * 2
def baseEnd_7862656 : Nat := 4037321748957694555940309

theorem tailTrace_7862656 : CollatzResearch.WordTrace tailWord_7862656 prefixEnd_7862656 4037321748957694555940309 := by
  unfold tailWord_7862656
  simp only [CollatzResearch.WordTrace]
  refine ⟨143387311901473810790687911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191183082535298414387583881 143387311901473810790687911)
  ·
    refine ⟨215080967852210716186031867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143387311901473810790687911 215080967852210716186031867)
    ·
      refine ⟨322621451778316074279047801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215080967852210716186031867 322621451778316074279047801)
      ·
        refine ⟨241966088833737055709285851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322621451778316074279047801 241966088833737055709285851)
        ·
          refine ⟨362949133250605583563928777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241966088833737055709285851 362949133250605583563928777)
          ·
            refine ⟨272211849937954187672946583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362949133250605583563928777 272211849937954187672946583)
            ·
              refine ⟨408317774906931281509419875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272211849937954187672946583 408317774906931281509419875)
              ·
                refine ⟨612476662360396922264129813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408317774906931281509419875 612476662360396922264129813)
                ·
                  refine ⟨28709843548143605731131085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 612476662360396922264129813 28709843548143605731131085)
                  ·
                    refine ⟨10766191330553852149174157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28709843548143605731131085 10766191330553852149174157)
                    ·
                      refine ⟨4037321748957694555940309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766191330553852149174157 4037321748957694555940309)
                      ·
                        rfl

theorem cell23_7862656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_7862656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862656 prefixEnd_7862656 := by exact prefixLift 7862656
  have htrace : WordTrace (prefixWord ++ tailWord_7862656) baseStart_7862656 baseEnd_7862656 := by
    simpa [prefixWord, tailWord_7862656, baseEnd_7862656] using wordTrace_append hprefix tailTrace_7862656
  have hstable : (prefixWord ++ tailWord_7862656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862656).length < 2 ^ (prefixWord ++ tailWord_7862656).sum := by decide
  have hdescent : baseEnd_7862656 < baseStart_7862656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862663 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 5]
def baseStart_7862663 : Nat := 118140960795 + 7862663 * 2 ^ 59
def prefixEnd_7862663 : Nat := 4983230072969 + 3 ^ 40 * 7862663 * 2
def baseEnd_7862663 : Nat := 448591704813586225394753

theorem tailTrace_7862663 : CollatzResearch.WordTrace tailWord_7862663 prefixEnd_7862663 448591704813586225394753 := by
  unfold tailWord_7862663
  simp only [CollatzResearch.WordTrace]
  refine ⟨286774879113922261776880643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191183252742614841184587095 286774879113922261776880643)
  ·
    refine ⟨430162318670883392665320965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286774879113922261776880643 430162318670883392665320965)
    ·
      refine ⟨80655434750790636124747681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430162318670883392665320965 80655434750790636124747681)
      ·
        refine ⟨60491576063092977093560761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80655434750790636124747681 60491576063092977093560761)
        ·
          refine ⟨45368682047319732820170571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60491576063092977093560761 45368682047319732820170571)
          ·
            refine ⟨68053023070979599230255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45368682047319732820170571 68053023070979599230255857)
            ·
              refine ⟨51039767303234699422691893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68053023070979599230255857 51039767303234699422691893)
              ·
                refine ⟨4784978184678253070877365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51039767303234699422691893 4784978184678253070877365)
                ·
                  refine ⟨448591704813586225394753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4784978184678253070877365 448591704813586225394753)
                  ·
                    rfl

theorem cell23_7862663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 5].length) (baseStart_7862663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862663 prefixEnd_7862663 := by exact prefixLift 7862663
  have htrace : WordTrace (prefixWord ++ tailWord_7862663) baseStart_7862663 baseEnd_7862663 := by
    simpa [prefixWord, tailWord_7862663, baseEnd_7862663] using wordTrace_append hprefix tailTrace_7862663
  have hstable : (prefixWord ++ tailWord_7862663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862663).length < 2 ^ (prefixWord ++ tailWord_7862663).sum := by decide
  have hdescent : baseEnd_7862663 < baseStart_7862663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862680 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 5]
def baseStart_7862680 : Nat := 118140960795 + 7862680 * 2 ^ 59
def prefixEnd_7862680 : Nat := 4983230072969 + 3 ^ 40 * 7862680 * 2
def baseEnd_7862680 : Nat := 448592674721489162448911

theorem tailTrace_7862680 : CollatzResearch.WordTrace tailWord_7862680 prefixEnd_7862680 448592674721489162448911 := by
  unfold tailWord_7862680
  simp only [CollatzResearch.WordTrace]
  refine ⟨143387749577430336840124747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191183666103240449120166329 143387749577430336840124747)
  ·
    refine ⟨215081624366145505260187121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143387749577430336840124747 215081624366145505260187121)
    ·
      refine ⟨161311218274609128945140341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215081624366145505260187121 161311218274609128945140341)
      ·
        refine ⟨15122926713244605838606907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161311218274609128945140341 15122926713244605838606907)
        ·
          refine ⟨22684390069866908757910361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15122926713244605838606907 22684390069866908757910361)
          ·
            refine ⟨17013292552400181568432771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22684390069866908757910361 17013292552400181568432771)
            ·
              refine ⟨25519938828600272352649157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17013292552400181568432771 25519938828600272352649157)
              ·
                refine ⟨4784988530362551066121717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25519938828600272352649157 4784988530362551066121717)
                ·
                  refine ⟨448592674721489162448911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4784988530362551066121717 448592674721489162448911)
                  ·
                    rfl

theorem cell23_7862680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 5].length) (baseStart_7862680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862680 prefixEnd_7862680 := by exact prefixLift 7862680
  have htrace : WordTrace (prefixWord ++ tailWord_7862680) baseStart_7862680 baseEnd_7862680 := by
    simpa [prefixWord, tailWord_7862680, baseEnd_7862680] using wordTrace_append hprefix tailTrace_7862680
  have hstable : (prefixWord ++ tailWord_7862680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862680).length < 2 ^ (prefixWord ++ tailWord_7862680).sum := by decide
  have hdescent : baseEnd_7862680 < baseStart_7862680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862713 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7862713 : Nat := 118140960795 + 7862713 * 2 ^ 59
def prefixEnd_7862713 : Nat := 4983230072969 + 3 ^ 40 * 7862713 * 2
def baseEnd_7862713 : Nat := 4037351017355000832927547

theorem tailTrace_7862713 : CollatzResearch.WordTrace tailWord_7862713 prefixEnd_7862713 4037351017355000832927547 := by
  unfold tailWord_7862713
  simp only [CollatzResearch.WordTrace]
  refine ⟨286776702763741120316200793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191184468509160746877467195 286776702763741120316200793)
  ·
    refine ⟨215082527072805840237150595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286776702763741120316200793 215082527072805840237150595)
    ·
      refine ⟨322623790609208760355725893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215082527072805840237150595 322623790609208760355725893)
      ·
        refine ⟨60491960739226642566698605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322623790609208760355725893 60491960739226642566698605)
        ·
          refine ⟨22684485277209990962511977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60491960739226642566698605 22684485277209990962511977)
          ·
            refine ⟨17013363957907493221883983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22684485277209990962511977 17013363957907493221883983)
            ·
              refine ⟨25520045936861239832825975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17013363957907493221883983 25520045936861239832825975)
              ·
                refine ⟨38280068905291859749238963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25520045936861239832825975 38280068905291859749238963)
                ·
                  refine ⟨57420103357937789623858445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38280068905291859749238963 57420103357937789623858445)
                  ·
                    refine ⟨21532538759226671108946917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57420103357937789623858445 21532538759226671108946917)
                    ·
                      refine ⟨4037351017355000832927547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21532538759226671108946917 4037351017355000832927547)
                      ·
                        rfl

theorem cell23_7862713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7862713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862713 prefixEnd_7862713 := by exact prefixLift 7862713
  have htrace : WordTrace (prefixWord ++ tailWord_7862713) baseStart_7862713 baseEnd_7862713 := by
    simpa [prefixWord, tailWord_7862713, baseEnd_7862713] using wordTrace_append hprefix tailTrace_7862713
  have hstable : (prefixWord ++ tailWord_7862713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862713).length < 2 ^ (prefixWord ++ tailWord_7862713).sum := by decide
  have hdescent : baseEnd_7862713 < baseStart_7862713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862740 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_7862740 : Nat := 118140960795 + 7862740 * 2 ^ 59
def prefixEnd_7862740 : Nat := 4983230072969 + 3 ^ 40 * 7862740 * 2
def baseEnd_7862740 : Nat := 1345788293777557409096641

theorem tailTrace_7862740 : CollatzResearch.WordTrace tailWord_7862740 prefixEnd_7862740 1345788293777557409096641 := by
  unfold tailWord_7862740
  simp only [CollatzResearch.WordTrace]
  refine ⟨143388843767321651963716837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191185125023095535951622449 143388843767321651963716837)
  ·
    refine ⟨26885408206372809743196907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143388843767321651963716837 26885408206372809743196907)
    ·
      refine ⟨40328112309559214614795361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26885408206372809743196907 40328112309559214614795361)
      ·
        refine ⟨30246084232169410961096521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40328112309559214614795361 30246084232169410961096521)
        ·
          refine ⟨22684563174127058220822391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30246084232169410961096521 22684563174127058220822391)
          ·
            refine ⟨34026844761190587331233587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22684563174127058220822391 34026844761190587331233587)
            ·
              refine ⟨51040267141785880996850381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34026844761190587331233587 51040267141785880996850381)
              ·
                refine ⟨19140100178169705373818893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51040267141785880996850381 19140100178169705373818893)
                ·
                  refine ⟨7177537566813639515182085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19140100178169705373818893 7177537566813639515182085)
                  ·
                    refine ⟨1345788293777557409096641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7177537566813639515182085 1345788293777557409096641)
                    ·
                      rfl

theorem cell23_7862740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_7862740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862740 prefixEnd_7862740 := by exact prefixLift 7862740
  have htrace : WordTrace (prefixWord ++ tailWord_7862740) baseStart_7862740 baseEnd_7862740 := by
    simpa [prefixWord, tailWord_7862740, baseEnd_7862740] using wordTrace_append hprefix tailTrace_7862740
  have hstable : (prefixWord ++ tailWord_7862740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862740).length < 2 ^ (prefixWord ++ tailWord_7862740).sum := by decide
  have hdescent : baseEnd_7862740 < baseStart_7862740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862783 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 1, 5]
def baseStart_7862783 : Nat := 118140960795 + 7862783 * 2 ^ 59
def prefixEnd_7862783 : Nat := 4983230072969 + 3 ^ 40 * 7862783 * 2
def baseEnd_7862783 : Nat := 1345795653666938519684075

theorem tailTrace_7862783 : CollatzResearch.WordTrace tailWord_7862783 prefixEnd_7862783 1345795653666938519684075 := by
  unfold tailWord_7862783
  simp only [CollatzResearch.WordTrace]
  refine ⟨286779255873487522271249003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191186170582325014847499335 286779255873487522271249003)
  ·
    refine ⟨430168883810231283406873505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286779255873487522271249003 430168883810231283406873505)
    ·
      refine ⟨322626662857673462555155129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430168883810231283406873505 322626662857673462555155129)
      ·
        refine ⟨241969997143255096916366347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322626662857673462555155129 241969997143255096916366347)
        ·
          refine ⟨362954995714882645374549521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241969997143255096916366347 362954995714882645374549521)
          ·
            refine ⟨272216246786161984030912141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362954995714882645374549521 272216246786161984030912141)
            ·
              refine ⟨102081092544810744011592053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272216246786161984030912141 102081092544810744011592053)
              ·
                refine ⟨9570102426076007251086755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102081092544810744011592053 9570102426076007251086755)
                ·
                  refine ⟨14355153639114010876630133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570102426076007251086755 14355153639114010876630133)
                  ·
                    refine ⟨1345795653666938519684075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14355153639114010876630133 1345795653666938519684075)
                    ·
                      rfl

theorem cell23_7862783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_7862783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862783 prefixEnd_7862783 := by exact prefixLift 7862783
  have htrace : WordTrace (prefixWord ++ tailWord_7862783) baseStart_7862783 baseEnd_7862783 := by
    simpa [prefixWord, tailWord_7862783, baseEnd_7862783] using wordTrace_append hprefix tailTrace_7862783
  have hstable : (prefixWord ++ tailWord_7862783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862783).length < 2 ^ (prefixWord ++ tailWord_7862783).sum := by decide
  have hdescent : baseEnd_7862783 < baseStart_7862783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862803 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 4]
def baseStart_7862803 : Nat := 118140960795 + 7862803 * 2 ^ 59
def prefixEnd_7862803 : Nat := 4983230072969 + 3 ^ 40 * 7862803 * 2
def baseEnd_7862803 : Nat := 4037397230613905480802133

theorem tailTrace_7862803 : CollatzResearch.WordTrace tailWord_7862803 prefixEnd_7862803 4037397230613905480802133 := by
  unfold tailWord_7862803
  simp only [CollatzResearch.WordTrace]
  refine ⟨286779985333415065686977063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191186656888943377124651375 286779985333415065686977063)
  ·
    refine ⟨430169978000122598530465595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286779985333415065686977063 430169978000122598530465595)
    ·
      refine ⟨645254967000183897795698393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430169978000122598530465595 645254967000183897795698393)
      ·
        refine ⟨483941225250137923346773795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645254967000183897795698393 483941225250137923346773795)
        ·
          refine ⟨725911837875206885020160693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483941225250137923346773795 725911837875206885020160693)
          ·
            refine ⟨68054234800800645470640065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 725911837875206885020160693 68054234800800645470640065)
            ·
              refine ⟨51040676100600484102980049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68054234800800645470640065 51040676100600484102980049)
              ·
                refine ⟨38280507075450363077235037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51040676100600484102980049 38280507075450363077235037)
                ·
                  refine ⟨14355190153293886153963139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38280507075450363077235037 14355190153293886153963139)
                  ·
                    refine ⟨21532785229940829230944709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14355190153293886153963139 21532785229940829230944709)
                    ·
                      refine ⟨4037397230613905480802133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21532785229940829230944709 4037397230613905480802133)
                      ·
                        rfl

theorem cell23_7862803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_7862803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862803 prefixEnd_7862803 := by exact prefixLift 7862803
  have htrace : WordTrace (prefixWord ++ tailWord_7862803) baseStart_7862803 baseEnd_7862803 := by
    simpa [prefixWord, tailWord_7862803, baseEnd_7862803] using wordTrace_append hprefix tailTrace_7862803
  have hstable : (prefixWord ++ tailWord_7862803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862803).length < 2 ^ (prefixWord ++ tailWord_7862803).sum := by decide
  have hdescent : baseEnd_7862803 < baseStart_7862803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862804 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 6]
def baseStart_7862804 : Nat := 118140960795 + 7862804 * 2 ^ 59
def prefixEnd_7862804 : Nat := 4983230072969 + 3 ^ 40 * 7862804 * 2
def baseEnd_7862804 : Nat := 448599749343839997432181

theorem tailTrace_7862804 : CollatzResearch.WordTrace tailWord_7862804 prefixEnd_7862804 448599749343839997432181 := by
  unfold tailWord_7862804
  simp only [CollatzResearch.WordTrace]
  refine ⟨143390010903205721428881733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191186681204274295238508977 143390010903205721428881733)
  ·
    refine ⟨26885627044351072767915325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143390010903205721428881733 26885627044351072767915325)
    ·
      refine ⟨10082110141631652287968247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26885627044351072767915325 10082110141631652287968247)
      ·
        refine ⟨15123165212447478431952371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10082110141631652287968247 15123165212447478431952371)
        ·
          refine ⟨22684747818671217647928557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123165212447478431952371 22684747818671217647928557)
          ·
            refine ⟨8506780432001706617973209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22684747818671217647928557 8506780432001706617973209)
            ·
              refine ⟨6380085324001279963479907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8506780432001706617973209 6380085324001279963479907)
              ·
                refine ⟨9570127986001919945219861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380085324001279963479907 9570127986001919945219861)
                ·
                  refine ⟨448599749343839997432181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9570127986001919945219861 448599749343839997432181)
                  ·
                    rfl

theorem cell23_7862804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_7862804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862804 prefixEnd_7862804 := by exact prefixLift 7862804
  have htrace : WordTrace (prefixWord ++ tailWord_7862804) baseStart_7862804 baseEnd_7862804 := by
    simpa [prefixWord, tailWord_7862804, baseEnd_7862804] using wordTrace_append hprefix tailTrace_7862804
  have hstable : (prefixWord ++ tailWord_7862804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862804).length < 2 ^ (prefixWord ++ tailWord_7862804).sum := by decide
  have hdescent : baseEnd_7862804 < baseStart_7862804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862824 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7862824 : Nat := 118140960795 + 7862824 * 2 ^ 59
def prefixEnd_7862824 : Nat := 4983230072969 + 3 ^ 40 * 7862824 * 2
def baseEnd_7862824 : Nat := 4037408013707649898639537

theorem tailTrace_7862824 : CollatzResearch.WordTrace tailWord_7862824 prefixEnd_7862824 4037408013707649898639537 := by
  unfold tailWord_7862824
  simp only [CollatzResearch.WordTrace]
  refine ⟨143390375633169493136745763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191187167510892657515661017 143390375633169493136745763)
  ·
    refine ⟨215085563449754239705118645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143390375633169493136745763 215085563449754239705118645)
    ·
      refine ⟨20164271573414459972354873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215085563449754239705118645 20164271573414459972354873)
      ·
        refine ⟨15123203680060844979266155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20164271573414459972354873 15123203680060844979266155)
        ·
          refine ⟨22684805520091267468899233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123203680060844979266155 22684805520091267468899233)
          ·
            refine ⟨17013604140068450601674425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22684805520091267468899233 17013604140068450601674425)
            ·
              refine ⟨12760203105051337951255819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17013604140068450601674425 12760203105051337951255819)
              ·
                refine ⟨19140304657577006926883729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760203105051337951255819 19140304657577006926883729)
                ·
                  refine ⟨14355228493182755195162797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19140304657577006926883729 14355228493182755195162797)
                  ·
                    refine ⟨5383210684943533198186049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14355228493182755195162797 5383210684943533198186049)
                    ·
                      refine ⟨4037408013707649898639537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383210684943533198186049 4037408013707649898639537)
                      ·
                        rfl

theorem cell23_7862824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7862824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862824 prefixEnd_7862824 := by exact prefixLift 7862824
  have htrace : WordTrace (prefixWord ++ tailWord_7862824) baseStart_7862824 baseEnd_7862824 := by
    simpa [prefixWord, tailWord_7862824, baseEnd_7862824] using wordTrace_append hprefix tailTrace_7862824
  have hstable : (prefixWord ++ tailWord_7862824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862824).length < 2 ^ (prefixWord ++ tailWord_7862824).sum := by decide
  have hdescent : baseEnd_7862824 < baseStart_7862824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862833 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_7862833 : Nat := 118140960795 + 7862833 * 2 ^ 59
def prefixEnd_7862833 : Nat := 4983230072969 + 3 ^ 40 * 7862833 * 2
def baseEnd_7862833 : Nat := 4037412635033540363426995

theorem tailTrace_7862833 : CollatzResearch.WordTrace tailWord_7862833 prefixEnd_7862833 4037412635033540363426995 := by
  unfold tailWord_7862833
  simp only [CollatzResearch.WordTrace]
  refine ⟨286781079523306380810569153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191187386348870920540379435 286781079523306380810569153)
  ·
    refine ⟨215085809642479785607926865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286781079523306380810569153 215085809642479785607926865)
    ·
      refine ⟨161314357231859839205945149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215085809642479785607926865 161314357231859839205945149)
      ·
        refine ⟨60492883961947439702229431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161314357231859839205945149 60492883961947439702229431)
        ·
          refine ⟨90739325942921159553344147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60492883961947439702229431 90739325942921159553344147)
          ·
            refine ⟨136108988914381739330016221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90739325942921159553344147 136108988914381739330016221)
            ·
              refine ⟨51040870842893152248756083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136108988914381739330016221 51040870842893152248756083)
              ·
                refine ⟨76561306264339728373134125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51040870842893152248756083 76561306264339728373134125)
                ·
                  refine ⟨28710489849127398139925297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76561306264339728373134125 28710489849127398139925297)
                  ·
                    refine ⟨21532867386845548604943973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28710489849127398139925297 21532867386845548604943973)
                    ·
                      refine ⟨4037412635033540363426995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21532867386845548604943973 4037412635033540363426995)
                      ·
                        rfl

theorem cell23_7862833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_7862833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862833 prefixEnd_7862833 := by exact prefixLift 7862833
  have htrace : WordTrace (prefixWord ++ tailWord_7862833) baseStart_7862833 baseEnd_7862833 := by
    simpa [prefixWord, tailWord_7862833, baseEnd_7862833] using wordTrace_append hprefix tailTrace_7862833
  have hstable : (prefixWord ++ tailWord_7862833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862833).length < 2 ^ (prefixWord ++ tailWord_7862833).sum := by decide
  have hdescent : baseEnd_7862833 < baseStart_7862833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862837 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_7862837 : Nat := 118140960795 + 7862837 * 2 ^ 59
def prefixEnd_7862837 : Nat := 4983230072969 + 3 ^ 40 * 7862837 * 2
def baseEnd_7862837 : Nat := 4037414688956158347776977

theorem tailTrace_7862837 : CollatzResearch.WordTrace tailWord_7862837 prefixEnd_7862837 4037414688956158347776977 := by
  unfold tailWord_7862837
  simp only [CollatzResearch.WordTrace]
  refine ⟨286781225415291889493714765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191187483610194592995809843 286781225415291889493714765)
  ·
    refine ⟨107542959530734458560143037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286781225415291889493714765 107542959530734458560143037)
    ·
      refine ⟨40328609824025421960053639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107542959530734458560143037 40328609824025421960053639)
      ·
        refine ⟨60492914736038132940080459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40328609824025421960053639 60492914736038132940080459)
        ·
          refine ⟨90739372104057199410120689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60492914736038132940080459 90739372104057199410120689)
          ·
            refine ⟨68054529078042899557590517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90739372104057199410120689 68054529078042899557590517)
            ·
              refine ⟨6380112101066521833524111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68054529078042899557590517 6380112101066521833524111)
              ·
                refine ⟨9570168151599782750286167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380112101066521833524111 9570168151599782750286167)
                ·
                  refine ⟨14355252227399674125429251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570168151599782750286167 14355252227399674125429251)
                  ·
                    refine ⟨21532878341099511188143877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14355252227399674125429251 21532878341099511188143877)
                    ·
                      refine ⟨4037414688956158347776977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21532878341099511188143877 4037414688956158347776977)
                      ·
                        rfl

theorem cell23_7862837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_7862837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862837 prefixEnd_7862837 := by exact prefixLift 7862837
  have htrace : WordTrace (prefixWord ++ tailWord_7862837) baseStart_7862837 baseEnd_7862837 := by
    simpa [prefixWord, tailWord_7862837, baseEnd_7862837] using wordTrace_append hprefix tailTrace_7862837
  have hstable : (prefixWord ++ tailWord_7862837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862837).length < 2 ^ (prefixWord ++ tailWord_7862837).sum := by decide
  have hdescent : baseEnd_7862837 < baseStart_7862837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862883 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7862883 : Nat := 118140960795 + 7862883 * 2 ^ 59
def prefixEnd_7862883 : Nat := 4983230072969 + 3 ^ 40 * 7862883 * 2
def baseEnd_7862883 : Nat := 4037438309066265167801765

theorem tailTrace_7862883 : CollatzResearch.WordTrace tailWord_7862883 prefixEnd_7862883 4037438309066265167801765 := by
  unfold tailWord_7862883
  simp only [CollatzResearch.WordTrace]
  refine ⟨286782903173125239349889303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191188602115416826233259535 286782903173125239349889303)
  ·
    refine ⟨430174354759687859024833955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286782903173125239349889303 430174354759687859024833955)
    ·
      refine ⟨645261532139531788537250933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430174354759687859024833955 645261532139531788537250933)
      ·
        refine ⟨60493268638081105175367275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 645261532139531788537250933 60493268638081105175367275)
        ·
          refine ⟨90739902957121657763050913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60493268638081105175367275 90739902957121657763050913)
          ·
            refine ⟨68054927217841243322288185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90739902957121657763050913 68054927217841243322288185)
            ·
              refine ⟨51041195413380932491716139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68054927217841243322288185 51041195413380932491716139)
              ·
                refine ⟨76561793120071398737574209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51041195413380932491716139 76561793120071398737574209)
                ·
                  refine ⟨57421344840053549053180657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76561793120071398737574209 57421344840053549053180657)
                  ·
                    refine ⟨43066008630040161789885493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57421344840053549053180657 43066008630040161789885493)
                    ·
                      refine ⟨4037438309066265167801765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43066008630040161789885493 4037438309066265167801765)
                      ·
                        rfl

theorem cell23_7862883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7862883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862883 prefixEnd_7862883 := by exact prefixLift 7862883
  have htrace : WordTrace (prefixWord ++ tailWord_7862883) baseStart_7862883 baseEnd_7862883 := by
    simpa [prefixWord, tailWord_7862883, baseEnd_7862883] using wordTrace_append hprefix tailTrace_7862883
  have hstable : (prefixWord ++ tailWord_7862883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862883).length < 2 ^ (prefixWord ++ tailWord_7862883).sum := by decide
  have hdescent : baseEnd_7862883 < baseStart_7862883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862888 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7862888 : Nat := 118140960795 + 7862888 * 2 ^ 59
def prefixEnd_7862888 : Nat := 4983230072969 + 3 ^ 40 * 7862888 * 2
def baseEnd_7862888 : Nat := 4037440876469537648239243

theorem tailTrace_7862888 : CollatzResearch.WordTrace tailWord_7862888 prefixEnd_7862888 4037440876469537648239243 := by
  unfold tailWord_7862888
  simp only [CollatzResearch.WordTrace]
  refine ⟨143391542769053562601910659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191188723692071416802547545 143391542769053562601910659)
  ·
    refine ⟨215087314153580343902865989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143391542769053562601910659 215087314153580343902865989)
    ·
      refine ⟨40328871403796314481787373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215087314153580343902865989 40328871403796314481787373)
      ·
        refine ⟨15123326776423617930670265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40328871403796314481787373 15123326776423617930670265)
        ·
          refine ⟨11342495082317713448002699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15123326776423617930670265 11342495082317713448002699)
          ·
            refine ⟨17013742623476570172004049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11342495082317713448002699 17013742623476570172004049)
            ·
              refine ⟨12760306967607427629003037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17013742623476570172004049 12760306967607427629003037)
              ·
                refine ⟨4785115112852785360876139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12760306967607427629003037 4785115112852785360876139)
                ·
                  refine ⟨7177672669279178041314209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785115112852785360876139 7177672669279178041314209)
                  ·
                    refine ⟨5383254501959383530985657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7177672669279178041314209 5383254501959383530985657)
                    ·
                      refine ⟨4037440876469537648239243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383254501959383530985657 4037440876469537648239243)
                      ·
                        rfl

theorem cell23_7862888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7862888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862888 prefixEnd_7862888 := by exact prefixLift 7862888
  have htrace : WordTrace (prefixWord ++ tailWord_7862888) baseStart_7862888 baseEnd_7862888 := by
    simpa [prefixWord, tailWord_7862888, baseEnd_7862888] using wordTrace_append hprefix tailTrace_7862888
  have hstable : (prefixWord ++ tailWord_7862888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862888).length < 2 ^ (prefixWord ++ tailWord_7862888).sum := by decide
  have hdescent : baseEnd_7862888 < baseStart_7862888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862903 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 2, 6]
def baseStart_7862903 : Nat := 118140960795 + 7862903 * 2 ^ 59
def prefixEnd_7862903 : Nat := 4983230072969 + 3 ^ 40 * 7862903 * 2
def baseEnd_7862903 : Nat := 1345816192893118363183891

theorem tailTrace_7862903 : CollatzResearch.WordTrace tailWord_7862903 prefixEnd_7862903 1345816192893118363183891 := by
  unfold tailWord_7862903
  simp only [CollatzResearch.WordTrace]
  refine ⟨286783632633052782765617363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191189088422035188510411575 286783632633052782765617363)
  ·
    refine ⟨430175448949579174148426045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286783632633052782765617363 430175448949579174148426045)
    ·
      refine ⟨161315793356092190305659767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430175448949579174148426045 161315793356092190305659767)
      ·
        refine ⟨241973690034138285458489651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161315793356092190305659767 241973690034138285458489651)
        ·
          refine ⟨362960535051207428187734477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241973690034138285458489651 362960535051207428187734477)
          ·
            refine ⟨136110200644202785570400429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362960535051207428187734477 136110200644202785570400429)
            ·
              refine ⟨51041325241576044588900161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136110200644202785570400429 51041325241576044588900161)
              ·
                refine ⟨38280993931182033441675121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51041325241576044588900161 38280993931182033441675121)
                ·
                  refine ⟨28710745448386525081256341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38280993931182033441675121 28710745448386525081256341)
                  ·
                    refine ⟨1345816192893118363183891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28710745448386525081256341 1345816192893118363183891)
                    ·
                      rfl

theorem cell23_7862903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_7862903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862903 prefixEnd_7862903 := by exact prefixLift 7862903
  have htrace : WordTrace (prefixWord ++ tailWord_7862903) baseStart_7862903 baseEnd_7862903 := by
    simpa [prefixWord, tailWord_7862903, baseEnd_7862903] using wordTrace_append hprefix tailTrace_7862903
  have hstable : (prefixWord ++ tailWord_7862903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862903).length < 2 ^ (prefixWord ++ tailWord_7862903).sum := by decide
  have hdescent : baseEnd_7862903 < baseStart_7862903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862923 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4]
def baseStart_7862923 : Nat := 118140960795 + 7862923 * 2 ^ 59
def prefixEnd_7862923 : Nat := 4983230072969 + 3 ^ 40 * 7862923 * 2
def baseEnd_7862923 : Nat := 4037458848292445011301581

theorem tailTrace_7862923 : CollatzResearch.WordTrace tailWord_7862923 prefixEnd_7862923 4037458848292445011301581 := by
  unfold tailWord_7862923
  simp only [CollatzResearch.WordTrace]
  refine ⟨286784362092980326181345423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191189574728653550787563615 286784362092980326181345423)
  ·
    refine ⟨430176543139470489272018135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286784362092980326181345423 430176543139470489272018135)
    ·
      refine ⟨645264814709205733908027203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430176543139470489272018135 645264814709205733908027203)
      ·
        refine ⟨967897222063808600862040805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645264814709205733908027203 967897222063808600862040805)
        ·
          refine ⟨181480729136964112661632651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 967897222063808600862040805 181480729136964112661632651)
          ·
            refine ⟨272221093705446168992448977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181480729136964112661632651 272221093705446168992448977)
            ·
              refine ⟨204165820279084626744336733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272221093705446168992448977 204165820279084626744336733)
              ·
                refine ⟨76562182604656735029126275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204165820279084626744336733 76562182604656735029126275)
                ·
                  refine ⟨114843273906985102543689413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76562182604656735029126275 114843273906985102543689413)
                  ·
                    refine ⟨21533113857559706726941765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114843273906985102543689413 21533113857559706726941765)
                    ·
                      refine ⟨4037458848292445011301581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21533113857559706726941765 4037458848292445011301581)
                      ·
                        rfl

theorem cell23_7862923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_7862923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862923 prefixEnd_7862923 := by exact prefixLift 7862923
  have htrace : WordTrace (prefixWord ++ tailWord_7862923) baseStart_7862923 baseEnd_7862923 := by
    simpa [prefixWord, tailWord_7862923, baseEnd_7862923] using wordTrace_append hprefix tailTrace_7862923
  have hstable : (prefixWord ++ tailWord_7862923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862923).length < 2 ^ (prefixWord ++ tailWord_7862923).sum := by decide
  have hdescent : baseEnd_7862923 < baseStart_7862923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862967 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 7]
def baseStart_7862967 : Nat := 118140960795 + 7862967 * 2 ^ 59
def prefixEnd_7862967 : Nat := 4983230072969 + 3 ^ 40 * 7862967 * 2
def baseEnd_7862967 : Nat := 448609049049026982127931

theorem tailTrace_7862967 : CollatzResearch.WordTrace tailWord_7862967 prefixEnd_7862967 448609049049026982127931 := by
  unfold tailWord_7862967
  simp only [CollatzResearch.WordTrace]
  refine ⟨286785966904820921695947155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191190644603213947797298103 286785966904820921695947155)
  ·
    refine ⟨430178950357231382543920733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286785966904820921695947155 430178950357231382543920733)
    ·
      refine ⟨161317106383961768453970275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430178950357231382543920733 161317106383961768453970275)
      ·
        refine ⟨241975659575942652680955413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161317106383961768453970275 241975659575942652680955413)
        ·
          refine ⟨11342609042622311844419785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241975659575942652680955413 11342609042622311844419785)
          ·
            refine ⟨8506956781966733883314839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11342609042622311844419785 8506956781966733883314839)
            ·
              refine ⟨12760435172950100824972259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506956781966733883314839 12760435172950100824972259)
              ·
                refine ⟨19140652759425151237458389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760435172950100824972259 19140652759425151237458389)
                ·
                  refine ⟨448609049049026982127931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19140652759425151237458389 448609049049026982127931)
                  ·
                    rfl

theorem cell23_7862967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 7].length) (baseStart_7862967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862967 prefixEnd_7862967 := by exact prefixLift 7862967
  have htrace : WordTrace (prefixWord ++ tailWord_7862967) baseStart_7862967 baseEnd_7862967 := by
    simpa [prefixWord, tailWord_7862967, baseEnd_7862967] using wordTrace_append hprefix tailTrace_7862967
  have hstable : (prefixWord ++ tailWord_7862967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862967).length < 2 ^ (prefixWord ++ tailWord_7862967).sum := by decide
  have hdescent : baseEnd_7862967 < baseStart_7862967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7862982 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7862982 : Nat := 118140960795 + 7862982 * 2 ^ 59
def prefixEnd_7862982 : Nat := 4983230072969 + 3 ^ 40 * 7862982 * 2
def baseEnd_7862982 : Nat := 4037489143651060280463811

theorem tailTrace_7862982 : CollatzResearch.WordTrace tailWord_7862982 prefixEnd_7862982 4037489143651060280463811 := by
  unfold tailWord_7862982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8962078562492705601804475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191191009333177719505162133 8962078562492705601804475)
  ·
    refine ⟨13443117843739058402706713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8962078562492705601804475 13443117843739058402706713)
    ·
      refine ⟨10082338382804293802030035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13443117843739058402706713 10082338382804293802030035)
      ·
        refine ⟨15123507574206440703045053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10082338382804293802030035 15123507574206440703045053)
        ·
          refine ⟨5671315340327415263641895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15123507574206440703045053 5671315340327415263641895)
          ·
            refine ⟨8506973010491122895462843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671315340327415263641895 8506973010491122895462843)
            ·
              refine ⟨12760459515736684343194265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506973010491122895462843 12760459515736684343194265)
              ·
                refine ⟨9570344636802513257395699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12760459515736684343194265 9570344636802513257395699)
                ·
                  refine ⟨14355516955203769886093549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570344636802513257395699 14355516955203769886093549)
                  ·
                    refine ⟨5383318858201413707285081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14355516955203769886093549 5383318858201413707285081)
                    ·
                      refine ⟨4037489143651060280463811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383318858201413707285081 4037489143651060280463811)
                      ·
                        rfl

theorem cell23_7862982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7862982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7862982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7862982 prefixEnd_7862982 := by exact prefixLift 7862982
  have htrace : WordTrace (prefixWord ++ tailWord_7862982) baseStart_7862982 baseEnd_7862982 := by
    simpa [prefixWord, tailWord_7862982, baseEnd_7862982] using wordTrace_append hprefix tailTrace_7862982
  have hstable : (prefixWord ++ tailWord_7862982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7862982).length < 2 ^ (prefixWord ++ tailWord_7862982).sum := by decide
  have hdescent : baseEnd_7862982 < baseStart_7862982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7862982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863020 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_7863020 : Nat := 118140960795 + 7863020 * 2 ^ 59
def prefixEnd_7863020 : Nat := 4983230072969 + 3 ^ 40 * 7863020 * 2
def baseEnd_7863020 : Nat := 4037508655915931131788635

theorem tailTrace_7863020 : CollatzResearch.WordTrace tailWord_7863020 prefixEnd_7863020 4037508655915931131788635 := by
  unfold tailWord_7863020
  simp only [CollatzResearch.WordTrace]
  refine ⟨143393949986814455873813257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191191933315752607831751009 143393949986814455873813257)
  ·
    refine ⟨107545462490110841905359943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143393949986814455873813257 107545462490110841905359943)
    ·
      refine ⟨161318193735166262858039915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107545462490110841905359943 161318193735166262858039915)
      ·
        refine ⟨241977290602749394287059873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161318193735166262858039915 241977290602749394287059873)
        ·
          refine ⟨181482967952062045715294905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241977290602749394287059873 181482967952062045715294905)
          ·
            refine ⟨136112225964046534286471179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181482967952062045715294905 136112225964046534286471179)
            ·
              refine ⟨204168338946069801429706769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136112225964046534286471179 204168338946069801429706769)
              ·
                refine ⟨153126254209552351072280077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204168338946069801429706769 153126254209552351072280077)
                ·
                  refine ⟨57422345328582131652105029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153126254209552351072280077 57422345328582131652105029)
                  ·
                    refine ⟨10766689749109149684769693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57422345328582131652105029 10766689749109149684769693)
                    ·
                      refine ⟨4037508655915931131788635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766689749109149684769693 4037508655915931131788635)
                      ·
                        rfl

theorem cell23_7863020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_7863020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863020 prefixEnd_7863020 := by exact prefixLift 7863020
  have htrace : WordTrace (prefixWord ++ tailWord_7863020) baseStart_7863020 baseEnd_7863020 := by
    simpa [prefixWord, tailWord_7863020, baseEnd_7863020] using wordTrace_append hprefix tailTrace_7863020
  have hstable : (prefixWord ++ tailWord_7863020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863020).length < 2 ^ (prefixWord ++ tailWord_7863020).sum := by decide
  have hdescent : baseEnd_7863020 < baseStart_7863020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863074 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_7863074 : Nat := 118140960795 + 7863074 * 2 ^ 59
def prefixEnd_7863074 : Nat := 4983230072969 + 3 ^ 40 * 7863074 * 2
def baseEnd_7863074 : Nat := 448615153763474880057043

theorem tailTrace_7863074 : CollatzResearch.WordTrace tailWord_7863074 prefixEnd_7863074 448615153763474880057043 := by
  unfold tailWord_7863074
  simp only [CollatzResearch.WordTrace]
  refine ⟨71697467378858319742523069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191193246343622185980061517 71697467378858319742523069)
  ·
    refine ⟨26886550267071869903446151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71697467378858319742523069 26886550267071869903446151)
    ·
      refine ⟨40329825400607804855169227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26886550267071869903446151 40329825400607804855169227)
      ·
        refine ⟨60494738100911707282753841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40329825400607804855169227 60494738100911707282753841)
        ·
          refine ⟨45371053575683780462065381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60494738100911707282753841 45371053575683780462065381)
          ·
            refine ⟨8507072545440708836637259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45371053575683780462065381 8507072545440708836637259)
            ·
              refine ⟨12760608818161063254955889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507072545440708836637259 12760608818161063254955889)
              ·
                refine ⟨9570456613620797441216917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12760608818161063254955889 9570456613620797441216917)
                ·
                  refine ⟨448615153763474880057043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9570456613620797441216917 448615153763474880057043)
                  ·
                    rfl

theorem cell23_7863074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_7863074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863074 prefixEnd_7863074 := by exact prefixLift 7863074
  have htrace : WordTrace (prefixWord ++ tailWord_7863074) baseStart_7863074 baseEnd_7863074 := by
    simpa [prefixWord, tailWord_7863074, baseEnd_7863074] using wordTrace_append hprefix tailTrace_7863074
  have hstable : (prefixWord ++ tailWord_7863074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863074).length < 2 ^ (prefixWord ++ tailWord_7863074).sum := by decide
  have hdescent : baseEnd_7863074 < baseStart_7863074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863084 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_7863084 : Nat := 118140960795 + 7863084 * 2 ^ 59
def prefixEnd_7863084 : Nat := 4983230072969 + 3 ^ 40 * 7863084 * 2
def baseEnd_7863084 : Nat := 4037541518677818881388341

theorem tailTrace_7863084 : CollatzResearch.WordTrace tailWord_7863084 prefixEnd_7863084 4037541518677818881388341 := by
  unfold tailWord_7863084
  simp only [CollatzResearch.WordTrace]
  refine ⟨143395117122698525338978153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191193489496931367118637537 143395117122698525338978153)
  ·
    refine ⟨107546337842023894004233615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143395117122698525338978153 107546337842023894004233615)
    ·
      refine ⟨161319506763035841006350423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107546337842023894004233615 161319506763035841006350423)
      ·
        refine ⟨241979260144553761509525635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161319506763035841006350423 241979260144553761509525635)
        ·
          refine ⟨362968890216830642264288453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241979260144553761509525635 362968890216830642264288453)
          ·
            refine ⟨68056666915655745424554085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362968890216830642264288453 68056666915655745424554085)
            ·
              refine ⟨12760625046685452267103891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68056666915655745424554085 12760625046685452267103891)
              ·
                refine ⟨19140937570028178400655837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760625046685452267103891 19140937570028178400655837)
                ·
                  refine ⟨7177851588760566900245939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19140937570028178400655837 7177851588760566900245939)
                  ·
                    refine ⟨10766777383140850350368909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7177851588760566900245939 10766777383140850350368909)
                    ·
                      refine ⟨4037541518677818881388341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766777383140850350368909 4037541518677818881388341)
                      ·
                        rfl

theorem cell23_7863084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_7863084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863084 prefixEnd_7863084 := by exact prefixLift 7863084
  have htrace : WordTrace (prefixWord ++ tailWord_7863084) baseStart_7863084 baseEnd_7863084 := by
    simpa [prefixWord, tailWord_7863084, baseEnd_7863084] using wordTrace_append hprefix tailTrace_7863084
  have hstable : (prefixWord ++ tailWord_7863084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863084).length < 2 ^ (prefixWord ++ tailWord_7863084).sum := by decide
  have hdescent : baseEnd_7863084 < baseStart_7863084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863107 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 6, 2]
def baseStart_7863107 : Nat := 118140960795 + 7863107 * 2 ^ 59
def prefixEnd_7863107 : Nat := 4983230072969 + 3 ^ 40 * 7863107 * 2
def baseEnd_7863107 : Nat := 4037553328732872291400735

theorem tailTrace_7863107 : CollatzResearch.WordTrace tailWord_7863107 prefixEnd_7863107 4037553328732872291400735 := by
  unfold tailWord_7863107
  simp only [CollatzResearch.WordTrace]
  refine ⟨286791073124313725606043575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191194048749542483737362383 286791073124313725606043575)
  ·
    refine ⟨430186609686470588409065363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286791073124313725606043575 430186609686470588409065363)
    ·
      refine ⟨645279914529705882613598045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430186609686470588409065363 645279914529705882613598045)
      ·
        refine ⟨241979967948639705980099267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645279914529705882613598045 241979967948639705980099267)
        ·
          refine ⟨362969951922959558970148901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241979967948639705980099267 362969951922959558970148901)
          ·
            refine ⟨68056865985554917306902919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362969951922959558970148901 68056865985554917306902919)
            ·
              refine ⟨102085298978332375960354379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68056865985554917306902919 102085298978332375960354379)
              ·
                refine ⟨153127948467498563940531569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102085298978332375960354379 153127948467498563940531569)
                ·
                  refine ⟨114845961350623922955398677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153127948467498563940531569 114845961350623922955398677)
                  ·
                    refine ⟨5383404438310496388534313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114845961350623922955398677 5383404438310496388534313)
                    ·
                      refine ⟨4037553328732872291400735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383404438310496388534313 4037553328732872291400735)
                      ·
                        rfl

theorem cell23_7863107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_7863107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863107 prefixEnd_7863107 := by exact prefixLift 7863107
  have htrace : WordTrace (prefixWord ++ tailWord_7863107) baseStart_7863107 baseEnd_7863107 := by
    simpa [prefixWord, tailWord_7863107, baseEnd_7863107] using wordTrace_append hprefix tailTrace_7863107
  have hstable : (prefixWord ++ tailWord_7863107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863107).length < 2 ^ (prefixWord ++ tailWord_7863107).sum := by decide
  have hdescent : baseEnd_7863107 < baseStart_7863107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863127 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_7863127 : Nat := 118140960795 + 7863127 * 2 ^ 59
def prefixEnd_7863127 : Nat := 4983230072969 + 3 ^ 40 * 7863127 * 2
def baseEnd_7863127 : Nat := 4037563598345962213150643

theorem tailTrace_7863127 : CollatzResearch.WordTrace tailWord_7863127 prefixEnd_7863127 4037563598345962213150643 := by
  unfold tailWord_7863127
  simp only [CollatzResearch.WordTrace]
  refine ⟨286791802584241269021771635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191194535056160846014514423 286791802584241269021771635)
  ·
    refine ⟨430187703876361903532657453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286791802584241269021771635 430187703876361903532657453)
    ·
      refine ⟨161320388953635713824746545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430187703876361903532657453 161320388953635713824746545)
      ·
        refine ⟨120990291715226785368559909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161320388953635713824746545 120990291715226785368559909)
        ·
          refine ⟨22685679696605022256604983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120990291715226785368559909 22685679696605022256604983)
          ·
            refine ⟨34028519544907533384907475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22685679696605022256604983 34028519544907533384907475)
            ·
              refine ⟨51042779317361300077361213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34028519544907533384907475 51042779317361300077361213)
              ·
                refine ⟨19141042244010487529010455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51042779317361300077361213 19141042244010487529010455)
                ·
                  refine ⟨28711563366015731293515683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19141042244010487529010455 28711563366015731293515683)
                  ·
                    refine ⟨43067345049023596940273525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28711563366015731293515683 43067345049023596940273525)
                    ·
                      refine ⟨4037563598345962213150643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43067345049023596940273525 4037563598345962213150643)
                      ·
                        rfl

theorem cell23_7863127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_7863127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863127 prefixEnd_7863127 := by exact prefixLift 7863127
  have htrace : WordTrace (prefixWord ++ tailWord_7863127) baseStart_7863127 baseEnd_7863127 := by
    simpa [prefixWord, tailWord_7863127, baseEnd_7863127] using wordTrace_append hprefix tailTrace_7863127
  have hstable : (prefixWord ++ tailWord_7863127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863127).length < 2 ^ (prefixWord ++ tailWord_7863127).sum := by decide
  have hdescent : baseEnd_7863127 < baseStart_7863127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863130 : List Nat := [3, 1, 1, 2, 1, 4, 11]
def baseStart_7863130 : Nat := 118140960795 + 7863130 * 2 ^ 59
def prefixEnd_7863130 : Nat := 4983230072969 + 3 ^ 40 * 7863130 * 2
def baseEnd_7863130 : Nat := 49846483194912662980409

theorem tailTrace_7863130 : CollatzResearch.WordTrace tailWord_7863130 prefixEnd_7863130 49846483194912662980409 := by
  unfold tailWord_7863130
  simp only [CollatzResearch.WordTrace]
  refine ⟨71697978000807600133532711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191194608002153600356087229 71697978000807600133532711)
  ·
    refine ⟨107546967001211400200299067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71697978000807600133532711 107546967001211400200299067)
    ·
      refine ⟨161320450501817100300448601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107546967001211400200299067 161320450501817100300448601)
      ·
        refine ⟨120990337876362825225336451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161320450501817100300448601 120990337876362825225336451)
        ·
          refine ⟨181485506814544237838004677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120990337876362825225336451 181485506814544237838004677)
          ·
            refine ⟨34028532527727044594625877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181485506814544237838004677 34028532527727044594625877)
            ·
              refine ⟨49846483194912662980409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34028532527727044594625877 49846483194912662980409)
              ·
                rfl

theorem cell23_7863130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 11].length) (baseStart_7863130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863130 prefixEnd_7863130 := by exact prefixLift 7863130
  have htrace : WordTrace (prefixWord ++ tailWord_7863130) baseStart_7863130 baseEnd_7863130 := by
    simpa [prefixWord, tailWord_7863130, baseEnd_7863130] using wordTrace_append hprefix tailTrace_7863130
  have hstable : (prefixWord ++ tailWord_7863130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863130).length < 2 ^ (prefixWord ++ tailWord_7863130).sum := by decide
  have hdescent : baseEnd_7863130 < baseStart_7863130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863141 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 3, 2, 2]
def baseStart_7863141 : Nat := 118140960795 + 7863141 * 2 ^ 59
def prefixEnd_7863141 : Nat := 4983230072969 + 3 ^ 40 * 7863141 * 2
def baseEnd_7863141 : Nat := 4037570787075125158375579

theorem tailTrace_7863141 : CollatzResearch.WordTrace tailWord_7863141 prefixEnd_7863141 4037570787075125158375579 := by
  unfold tailWord_7863141
  simp only [CollatzResearch.WordTrace]
  refine ⟨286792313206190549412781277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191194875470793699608520851 286792313206190549412781277)
  ·
    refine ⟨107547117452321456029792979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286792313206190549412781277 107547117452321456029792979)
    ·
      refine ⟨161320676178482184044689469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107547117452321456029792979 161320676178482184044689469)
      ·
        refine ⟨60495253566930819016758551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161320676178482184044689469 60495253566930819016758551)
        ·
          refine ⟨90742880350396228525137827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60495253566930819016758551 90742880350396228525137827)
          ·
            refine ⟨136114320525594342787706741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90742880350396228525137827 136114320525594342787706741)
            ·
              refine ⟨12760717549274469636347507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136114320525594342787706741 12760717549274469636347507)
              ·
                refine ⟨19141076323911704454521261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760717549274469636347507 19141076323911704454521261)
                ·
                  refine ⟨7177903621466889170445473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19141076323911704454521261 7177903621466889170445473)
                  ·
                    refine ⟨5383427716100166877834105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7177903621466889170445473 5383427716100166877834105)
                    ·
                      refine ⟨4037570787075125158375579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383427716100166877834105 4037570787075125158375579)
                      ·
                        rfl

theorem cell23_7863141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_7863141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863141 prefixEnd_7863141 := by exact prefixLift 7863141
  have htrace : WordTrace (prefixWord ++ tailWord_7863141) baseStart_7863141 baseEnd_7863141 := by
    simpa [prefixWord, tailWord_7863141, baseEnd_7863141] using wordTrace_append hprefix tailTrace_7863141
  have hstable : (prefixWord ++ tailWord_7863141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863141).length < 2 ^ (prefixWord ++ tailWord_7863141).sum := by decide
  have hdescent : baseEnd_7863141 < baseStart_7863141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863158 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7863158 : Nat := 118140960795 + 7863158 * 2 ^ 59
def prefixEnd_7863158 : Nat := 4983230072969 + 3 ^ 40 * 7863158 * 2
def baseEnd_7863158 : Nat := 4037579516246251591863001

theorem tailTrace_7863158 : CollatzResearch.WordTrace tailWord_7863158 prefixEnd_7863158 4037579516246251591863001 := by
  unfold tailWord_7863158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17924558327945560082259383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191195288831419307544100085 17924558327945560082259383)
  ·
    refine ⟨26886837491918340123389075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17924558327945560082259383 26886837491918340123389075)
    ·
      refine ⟨40330256237877510185083613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26886837491918340123389075 40330256237877510185083613)
      ·
        refine ⟨15123846089204066319406355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40330256237877510185083613 15123846089204066319406355)
        ·
          refine ⟨22685769133806099479109533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123846089204066319406355 22685769133806099479109533)
          ·
            refine ⟨8507163425177287304666075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22685769133806099479109533 8507163425177287304666075)
            ·
              refine ⟨12760745137765930956999113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507163425177287304666075 12760745137765930956999113)
              ·
                refine ⟨9570558853324448217749335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12760745137765930956999113 9570558853324448217749335)
                ·
                  refine ⟨14355838279986672326624003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570558853324448217749335 14355838279986672326624003)
                  ·
                    refine ⟨21533757419980008489936005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14355838279986672326624003 21533757419980008489936005)
                    ·
                      refine ⟨4037579516246251591863001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21533757419980008489936005 4037579516246251591863001)
                      ·
                        rfl

theorem cell23_7863158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7863158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863158 prefixEnd_7863158 := by exact prefixLift 7863158
  have htrace : WordTrace (prefixWord ++ tailWord_7863158) baseStart_7863158 baseEnd_7863158 := by
    simpa [prefixWord, tailWord_7863158, baseEnd_7863158] using wordTrace_append hprefix tailTrace_7863158
  have hstable : (prefixWord ++ tailWord_7863158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863158).length < 2 ^ (prefixWord ++ tailWord_7863158).sum := by decide
  have hdescent : baseEnd_7863158 < baseStart_7863158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863160 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_7863160 : Nat := 118140960795 + 7863160 * 2 ^ 59
def prefixEnd_7863160 : Nat := 4983230072969 + 3 ^ 40 * 7863160 * 2
def baseEnd_7863160 : Nat := 1345860181069186861345997

theorem tailTrace_7863160 : CollatzResearch.WordTrace tailWord_7863160 prefixEnd_7863160 1345860181069186861345997 := by
  unfold tailWord_7863160
  simp only [CollatzResearch.WordTrace]
  refine ⟨143396503096560857828861467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191195337462081143771815289 143396503096560857828861467)
  ·
    refine ⟨215094754644841286743292201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143396503096560857828861467 215094754644841286743292201)
    ·
      refine ⟨161321065983630965057469151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215094754644841286743292201 161321065983630965057469151)
      ·
        refine ⟨241981598975446447586203727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161321065983630965057469151 241981598975446447586203727)
        ·
          refine ⟨362972398463169671379305591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241981598975446447586203727 362972398463169671379305591)
          ·
            refine ⟨544458597694754507068958387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362972398463169671379305591 544458597694754507068958387)
            ·
              refine ⟨816687896542131760603437581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544458597694754507068958387 816687896542131760603437581)
              ·
                refine ⟨306257961203299410226289093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 816687896542131760603437581 306257961203299410226289093)
                ·
                  refine ⟨57423367725618639417429205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306257961203299410226289093 57423367725618639417429205)
                  ·
                    refine ⟨1345860181069186861345997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57423367725618639417429205 1345860181069186861345997)
                    ·
                      rfl

theorem cell23_7863160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_7863160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863160 prefixEnd_7863160 := by exact prefixLift 7863160
  have htrace : WordTrace (prefixWord ++ tailWord_7863160) baseStart_7863160 baseEnd_7863160 := by
    simpa [prefixWord, tailWord_7863160, baseEnd_7863160] using wordTrace_append hprefix tailTrace_7863160
  have hstable : (prefixWord ++ tailWord_7863160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863160).length < 2 ^ (prefixWord ++ tailWord_7863160).sum := by decide
  have hdescent : baseEnd_7863160 < baseStart_7863160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863161 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 3]
def baseStart_7863161 : Nat := 118140960795 + 7863161 * 2 ^ 59
def prefixEnd_7863161 : Nat := 4983230072969 + 3 ^ 40 * 7863161 * 2
def baseEnd_7863161 : Nat := 4037581056688215080125487

theorem tailTrace_7863161 : CollatzResearch.WordTrace tailWord_7863161 prefixEnd_7863161 4037581056688215080125487 := by
  unfold tailWord_7863161
  simp only [CollatzResearch.WordTrace]
  refine ⟨286793042666118092828509337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191195361777412061885672891 286793042666118092828509337)
  ·
    refine ⟨215094781999588569621382003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286793042666118092828509337 215094781999588569621382003)
    ·
      refine ⟨322642172999382854432073005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215094781999588569621382003 322642172999382854432073005)
      ·
        refine ⟨120990814874768570412027377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322642172999382854432073005 120990814874768570412027377)
        ·
          refine ⟨90743111156076427809020533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120990814874768570412027377 90743111156076427809020533)
          ·
            refine ⟨8507166670882165107095675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90743111156076427809020533 8507166670882165107095675)
            ·
              refine ⟨12760750006323247660643513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507166670882165107095675 12760750006323247660643513)
              ·
                refine ⟨9570562504742435745482635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12760750006323247660643513 9570562504742435745482635)
                ·
                  refine ⟨14355843757113653618223953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570562504742435745482635 14355843757113653618223953)
                  ·
                    refine ⟨10766882817835240213667965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14355843757113653618223953 10766882817835240213667965)
                    ·
                      refine ⟨4037581056688215080125487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766882817835240213667965 4037581056688215080125487)
                      ·
                        rfl

theorem cell23_7863161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_7863161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863161 prefixEnd_7863161 := by exact prefixLift 7863161
  have htrace : WordTrace (prefixWord ++ tailWord_7863161) baseStart_7863161 baseEnd_7863161 := by
    simpa [prefixWord, tailWord_7863161, baseEnd_7863161] using wordTrace_append hprefix tailTrace_7863161
  have hstable : (prefixWord ++ tailWord_7863161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863161).length < 2 ^ (prefixWord ++ tailWord_7863161).sum := by decide
  have hdescent : baseEnd_7863161 < baseStart_7863161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863178 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7863178 : Nat := 118140960795 + 7863178 * 2 ^ 59
def prefixEnd_7863178 : Nat := 4983230072969 + 3 ^ 40 * 7863178 * 2
def baseEnd_7863178 : Nat := 4037589785859341513612909

theorem tailTrace_7863178 : CollatzResearch.WordTrace tailWord_7863178 prefixEnd_7863178 4037589785859341513612909 := by
  unfold tailWord_7863178
  simp only [CollatzResearch.WordTrace]
  refine ⟨71698415676764126182969547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191195775138037669821252125 71698415676764126182969547)
  ·
    refine ⟨107547623515146189274454321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71698415676764126182969547 107547623515146189274454321)
    ·
      refine ⟨80660717636359641955840741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107547623515146189274454321 80660717636359641955840741)
      ·
        refine ⟨15123884556817432866720139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80660717636359641955840741 15123884556817432866720139)
        ·
          refine ⟨22685826835226149300080209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123884556817432866720139 22685826835226149300080209)
          ·
            refine ⟨17014370126419611975060157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22685826835226149300080209 17014370126419611975060157)
            ·
              refine ⟨6380388797407354490647559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17014370126419611975060157 6380388797407354490647559)
              ·
                refine ⟨9570583196111031735971339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380388797407354490647559 9570583196111031735971339)
                ·
                  refine ⟨14355874794166547603957009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570583196111031735971339 14355874794166547603957009)
                  ·
                    refine ⟨10766906095624910702967757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14355874794166547603957009 10766906095624910702967757)
                    ·
                      refine ⟨4037589785859341513612909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766906095624910702967757 4037589785859341513612909)
                      ·
                        rfl

theorem cell23_7863178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7863178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863178 prefixEnd_7863178 := by exact prefixLift 7863178
  have htrace : WordTrace (prefixWord ++ tailWord_7863178) baseStart_7863178 baseEnd_7863178 := by
    simpa [prefixWord, tailWord_7863178, baseEnd_7863178] using wordTrace_append hprefix tailTrace_7863178
  have hstable : (prefixWord ++ tailWord_7863178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863178).length < 2 ^ (prefixWord ++ tailWord_7863178).sum := by decide
  have hdescent : baseEnd_7863178 < baseStart_7863178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863191 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_7863191 : Nat := 118140960795 + 7863191 * 2 ^ 59
def prefixEnd_7863191 : Nat := 4983230072969 + 3 ^ 40 * 7863191 * 2
def baseEnd_7863191 : Nat := 4037596461107849962750349

theorem tailTrace_7863191 : CollatzResearch.WordTrace tailWord_7863191 prefixEnd_7863191 4037596461107849962750349 := by
  unfold tailWord_7863191
  simp only [CollatzResearch.WordTrace]
  refine ⟨286794136856009407952101427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191196091237339605301400951 286794136856009407952101427)
  ·
    refine ⟨430191205284014111928152141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286794136856009407952101427 430191205284014111928152141)
    ·
      refine ⟨161321701981505291973057053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430191205284014111928152141 161321701981505291973057053)
      ·
        refine ⟨60495638243064484489896395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161321701981505291973057053 60495638243064484489896395)
        ·
          refine ⟨90743457364596726734844593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60495638243064484489896395 90743457364596726734844593)
          ·
            refine ⟨68057593023447545051133445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90743457364596726734844593 68057593023447545051133445)
            ·
              refine ⟨12760798691896414697087521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68057593023447545051133445 12760798691896414697087521)
              ·
                refine ⟨9570599018922311022815641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12760798691896414697087521 9570599018922311022815641)
                ·
                  refine ⟨7177949264191733267111731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9570599018922311022815641 7177949264191733267111731)
                  ·
                    refine ⟨10766923896287599900667597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7177949264191733267111731 10766923896287599900667597)
                    ·
                      refine ⟨4037596461107849962750349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10766923896287599900667597 4037596461107849962750349)
                      ·
                        rfl

theorem cell23_7863191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_7863191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863191 prefixEnd_7863191 := by exact prefixLift 7863191
  have htrace : WordTrace (prefixWord ++ tailWord_7863191) baseStart_7863191 baseEnd_7863191 := by
    simpa [prefixWord, tailWord_7863191, baseEnd_7863191] using wordTrace_append hprefix tailTrace_7863191
  have hstable : (prefixWord ++ tailWord_7863191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863191).length < 2 ^ (prefixWord ++ tailWord_7863191).sum := by decide
  have hdescent : baseEnd_7863191 < baseStart_7863191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863197 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7863197 : Nat := 118140960795 + 7863197 * 2 ^ 59
def prefixEnd_7863197 : Nat := 4983230072969 + 3 ^ 40 * 7863197 * 2
def baseEnd_7863197 : Nat := 4037599541991776939275321

theorem tailTrace_7863197 : CollatzResearch.WordTrace tailWord_7863197 prefixEnd_7863197 4037599541991776939275321 := by
  unfold tailWord_7863197
  simp only [CollatzResearch.WordTrace]
  refine ⟨286794355693987670976819845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191196237129325113984546563 286794355693987670976819845)
  ·
    refine ⟨53773941692622688308153721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286794355693987670976819845 53773941692622688308153721)
    ·
      refine ⟨40330456269467016231115291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53773941692622688308153721 40330456269467016231115291)
      ·
        refine ⟨60495684404200524346672937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40330456269467016231115291 60495684404200524346672937)
        ·
          refine ⟨45371763303150393260004703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60495684404200524346672937 45371763303150393260004703)
          ·
            refine ⟨68057644954725589890007055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45371763303150393260004703 68057644954725589890007055)
            ·
              refine ⟨102086467432088384835010583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68057644954725589890007055 102086467432088384835010583)
              ·
                refine ⟨153129701148132577252515875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102086467432088384835010583 153129701148132577252515875)
                ·
                  refine ⟨229694551722198865878773813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153129701148132577252515875 229694551722198865878773813)
                  ·
                    refine ⟨21533864223956143676135045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229694551722198865878773813 21533864223956143676135045)
                    ·
                      refine ⟨4037599541991776939275321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21533864223956143676135045 4037599541991776939275321)
                      ·
                        rfl

theorem cell23_7863197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7863197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863197 prefixEnd_7863197 := by exact prefixLift 7863197
  have htrace : WordTrace (prefixWord ++ tailWord_7863197) baseStart_7863197 baseEnd_7863197 := by
    simpa [prefixWord, tailWord_7863197, baseEnd_7863197] using wordTrace_append hprefix tailTrace_7863197
  have hstable : (prefixWord ++ tailWord_7863197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863197).length < 2 ^ (prefixWord ++ tailWord_7863197).sum := by decide
  have hdescent : baseEnd_7863197 < baseStart_7863197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863201 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7863201 : Nat := 118140960795 + 7863201 * 2 ^ 59
def prefixEnd_7863201 : Nat := 4983230072969 + 3 ^ 40 * 7863201 * 2
def baseEnd_7863201 : Nat := 4037601595914394923625303

theorem tailTrace_7863201 : CollatzResearch.WordTrace tailWord_7863201 prefixEnd_7863201 4037601595914394923625303 := by
  unfold tailWord_7863201
  simp only [CollatzResearch.WordTrace]
  refine ⟨286794501585973179659965457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191196334390648786439976971 286794501585973179659965457)
  ·
    refine ⟨215095876189479884744974093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286794501585973179659965457 215095876189479884744974093)
    ·
      refine ⟨80660953571054956779365285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215095876189479884744974093 80660953571054956779365285)
      ·
        refine ⟨15123928794572804396130991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80660953571054956779365285 15123928794572804396130991)
        ·
          refine ⟨22685893191859206594196487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123928794572804396130991 22685893191859206594196487)
          ·
            refine ⟨34028839787788809891294731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22685893191859206594196487 34028839787788809891294731)
            ·
              refine ⟨51043259681683214836942097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34028839787788809891294731 51043259681683214836942097)
              ·
                refine ⟨38282444761262411127706573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51043259681683214836942097 38282444761262411127706573)
                ·
                  refine ⟨14355916785473404172889965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38282444761262411127706573 14355916785473404172889965)
                  ·
                    refine ⟨5383468794552526564833737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14355916785473404172889965 5383468794552526564833737)
                    ·
                      refine ⟨4037601595914394923625303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383468794552526564833737 4037601595914394923625303)
                      ·
                        rfl

theorem cell23_7863201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7863201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863201 prefixEnd_7863201 := by exact prefixLift 7863201
  have htrace : WordTrace (prefixWord ++ tailWord_7863201) baseStart_7863201 baseEnd_7863201 := by
    simpa [prefixWord, tailWord_7863201, baseEnd_7863201] using wordTrace_append hprefix tailTrace_7863201
  have hstable : (prefixWord ++ tailWord_7863201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863201).length < 2 ^ (prefixWord ++ tailWord_7863201).sum := by decide
  have hdescent : baseEnd_7863201 < baseStart_7863201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863267 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 3, 7]
def baseStart_7863267 : Nat := 118140960795 + 7863267 * 2 ^ 59
def prefixEnd_7863267 : Nat := 4983230072969 + 3 ^ 40 * 7863267 * 2
def baseEnd_7863267 : Nat := 1345878495212530555133333

theorem tailTrace_7863267 : CollatzResearch.WordTrace tailWord_7863267 prefixEnd_7863267 1345878495212530555133333 := by
  unfold tailWord_7863267
  simp only [CollatzResearch.WordTrace]
  refine ⟨286796908803734072931868055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191197939202489381954578703 286796908803734072931868055)
  ·
    refine ⟨430195363205601109397802083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286796908803734072931868055 430195363205601109397802083)
    ·
      refine ⟨645293044808401664096703125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430195363205601109397802083 645293044808401664096703125)
      ·
        refine ⟨30248111475393828004532959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 645293044808401664096703125 30248111475393828004532959)
        ·
          refine ⟨45372167213090742006799439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30248111475393828004532959 45372167213090742006799439)
          ·
            refine ⟨68058250819636113010199159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45372167213090742006799439 68058250819636113010199159)
            ·
              refine ⟨102087376229454169515298739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68058250819636113010199159 102087376229454169515298739)
              ·
                refine ⟨153131064344181254272948109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102087376229454169515298739 153131064344181254272948109)
                ·
                  refine ⟨57424149129067970352355541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153131064344181254272948109 57424149129067970352355541)
                  ·
                    refine ⟨1345878495212530555133333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57424149129067970352355541 1345878495212530555133333)
                    ·
                      rfl

theorem cell23_7863267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 7].length) (baseStart_7863267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863267 prefixEnd_7863267 := by exact prefixLift 7863267
  have htrace : WordTrace (prefixWord ++ tailWord_7863267) baseStart_7863267 baseEnd_7863267 := by
    simpa [prefixWord, tailWord_7863267, baseEnd_7863267] using wordTrace_append hprefix tailTrace_7863267
  have hstable : (prefixWord ++ tailWord_7863267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863267).length < 2 ^ (prefixWord ++ tailWord_7863267).sum := by decide
  have hdescent : baseEnd_7863267 < baseStart_7863267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863304 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_7863304 : Nat := 118140960795 + 7863304 * 2 ^ 59
def prefixEnd_7863304 : Nat := 4983230072969 + 3 ^ 40 * 7863304 * 2
def baseEnd_7863304 : Nat := 4037654484421808020637329

theorem tailTrace_7863304 : CollatzResearch.WordTrace tailWord_7863304 prefixEnd_7863304 4037654484421808020637329 := by
  unfold tailWord_7863304
  simp only [CollatzResearch.WordTrace]
  refine ⟨143399129152300014125482483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191198838869733352167309977 143399129152300014125482483)
  ·
    refine ⟨215098693728450021188223725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143399129152300014125482483 215098693728450021188223725)
    ·
      refine ⟨80662010148168757945583897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215098693728450021188223725 80662010148168757945583897)
      ·
        refine ⟨60496507611126568459187923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80662010148168757945583897 60496507611126568459187923)
        ·
          refine ⟨90744761416689852688781885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60496507611126568459187923 90744761416689852688781885)
          ·
            refine ⟨34029285531258694758293207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90744761416689852688781885 34029285531258694758293207)
            ·
              refine ⟨51043928296888042137439811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34029285531258694758293207 51043928296888042137439811)
              ·
                refine ⟨76565892445332063206159717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51043928296888042137439811 76565892445332063206159717)
                ·
                  refine ⟨14356104833499761851154947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76565892445332063206159717 14356104833499761851154947)
                  ·
                    refine ⟨21534157250249642776732421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14356104833499761851154947 21534157250249642776732421)
                    ·
                      refine ⟨4037654484421808020637329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21534157250249642776732421 4037654484421808020637329)
                      ·
                        rfl

theorem cell23_7863304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_7863304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863304 prefixEnd_7863304 := by exact prefixLift 7863304
  have htrace : WordTrace (prefixWord ++ tailWord_7863304) baseStart_7863304 baseEnd_7863304 := by
    simpa [prefixWord, tailWord_7863304, baseEnd_7863304] using wordTrace_append hprefix tailTrace_7863304
  have hstable : (prefixWord ++ tailWord_7863304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863304).length < 2 ^ (prefixWord ++ tailWord_7863304).sum := by decide
  have hdescent : baseEnd_7863304 < baseStart_7863304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863338 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7863338 : Nat := 118140960795 + 7863338 * 2 ^ 59
def prefixEnd_7863338 : Nat := 4983230072969 + 3 ^ 40 * 7863338 * 2
def baseEnd_7863338 : Nat := 4037671942764060887612173

theorem tailTrace_7863338 : CollatzResearch.WordTrace tailWord_7863338 prefixEnd_7863338 4037671942764060887612173 := by
  unfold tailWord_7863338
  simp only [CollatzResearch.WordTrace]
  refine ⟨71699874596619213014425667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191199665590984568038468445 71699874596619213014425667)
  ·
    refine ⟨107549811894928819521638501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71699874596619213014425667 107549811894928819521638501)
    ·
      refine ⟨20165589730299153660307219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107549811894928819521638501 20165589730299153660307219)
      ·
        refine ⟨30248384595448730490460829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20165589730299153660307219 30248384595448730490460829)
        ·
          refine ⟨11343144223293273933922811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30248384595448730490460829 11343144223293273933922811)
          ·
            refine ⟨17014716334939910900884217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343144223293273933922811 17014716334939910900884217)
            ·
              refine ⟨12761037251204933175663163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17014716334939910900884217 12761037251204933175663163)
              ·
                refine ⟨19141555876807399763494745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12761037251204933175663163 19141555876807399763494745)
                ·
                  refine ⟨14356166907605549822621059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19141555876807399763494745 14356166907605549822621059)
                  ·
                    refine ⟨21534250361408324733931589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14356166907605549822621059 21534250361408324733931589)
                    ·
                      refine ⟨4037671942764060887612173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21534250361408324733931589 4037671942764060887612173)
                      ·
                        rfl

theorem cell23_7863338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7863338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863338 prefixEnd_7863338 := by exact prefixLift 7863338
  have htrace : WordTrace (prefixWord ++ tailWord_7863338) baseStart_7863338 baseEnd_7863338 := by
    simpa [prefixWord, tailWord_7863338, baseEnd_7863338] using wordTrace_append hprefix tailTrace_7863338
  have hstable : (prefixWord ++ tailWord_7863338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863338).length < 2 ^ (prefixWord ++ tailWord_7863338).sum := by decide
  have hdescent : baseEnd_7863338 < baseStart_7863338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863347 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_7863347 : Nat := 118140960795 + 7863347 * 2 ^ 59
def prefixEnd_7863347 : Nat := 4983230072969 + 3 ^ 40 * 7863347 * 2
def baseEnd_7863347 : Nat := 4037676564089951352399631

theorem tailTrace_7863347 : CollatzResearch.WordTrace tailWord_7863347 prefixEnd_7863347 4037676564089951352399631 := by
  unfold tailWord_7863347
  simp only [CollatzResearch.WordTrace]
  refine ⟨286799826643444246594780295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191199884428962831063186863 286799826643444246594780295)
  ·
    refine ⟨430199739965166369892170443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286799826643444246594780295 430199739965166369892170443)
    ·
      refine ⟨645299609947749554838255665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430199739965166369892170443 645299609947749554838255665)
      ·
        refine ⟨483974707460812166128691749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645299609947749554838255665 483974707460812166128691749)
        ·
          refine ⟨90745257648902281149129703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483974707460812166128691749 90745257648902281149129703)
          ·
            refine ⟨136117886473353421723694555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90745257648902281149129703 136117886473353421723694555)
            ·
              refine ⟨204176829710030132585541833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136117886473353421723694555 204176829710030132585541833)
              ·
                refine ⟨153132622282522599439156375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204176829710030132585541833 153132622282522599439156375)
                ·
                  refine ⟨229698933423783899158734563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153132622282522599439156375 229698933423783899158734563)
                  ·
                    refine ⟨344548400135675848738101845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229698933423783899158734563 344548400135675848738101845)
                    ·
                      refine ⟨4037676564089951352399631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 344548400135675848738101845 4037676564089951352399631)
                      ·
                        rfl

theorem cell23_7863347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_7863347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863347 prefixEnd_7863347 := by exact prefixLift 7863347
  have htrace : WordTrace (prefixWord ++ tailWord_7863347) baseStart_7863347 baseEnd_7863347 := by
    simpa [prefixWord, tailWord_7863347, baseEnd_7863347] using wordTrace_append hprefix tailTrace_7863347
  have hstable : (prefixWord ++ tailWord_7863347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863347).length < 2 ^ (prefixWord ++ tailWord_7863347).sum := by decide
  have hdescent : baseEnd_7863347 < baseStart_7863347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863358 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_7863358 : Nat := 118140960795 + 7863358 * 2 ^ 59
def prefixEnd_7863358 : Nat := 4983230072969 + 3 ^ 40 * 7863358 * 2
def baseEnd_7863358 : Nat := 4037682212377150809362081

theorem tailTrace_7863358 : CollatzResearch.WordTrace tailWord_7863358 prefixEnd_7863358 4037682212377150809362081 := by
  unfold tailWord_7863358
  simp only [CollatzResearch.WordTrace]
  refine ⟨35850028480800549434178841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191200151897602930315620485 35850028480800549434178841)
  ·
    refine ⟨26887521360600412075634131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35850028480800549434178841 26887521360600412075634131)
    ·
      refine ⟨40331282040900618113451197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26887521360600412075634131 40331282040900618113451197)
      ·
        refine ⟨15124230765337731792544199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40331282040900618113451197 15124230765337731792544199)
        ·
          refine ⟨22686346148006597688816299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15124230765337731792544199 22686346148006597688816299)
          ·
            refine ⟨34029519222009896533224449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22686346148006597688816299 34029519222009896533224449)
            ·
              refine ⟨25522139416507422399918337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34029519222009896533224449 25522139416507422399918337)
              ·
                refine ⟨19141604562380566799938753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25522139416507422399918337 19141604562380566799938753)
                ·
                  refine ⟨14356203421785425099954065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19141604562380566799938753 14356203421785425099954065)
                  ·
                    refine ⟨10767152566339068824965549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14356203421785425099954065 10767152566339068824965549)
                    ·
                      refine ⟨4037682212377150809362081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767152566339068824965549 4037682212377150809362081)
                      ·
                        rfl

theorem cell23_7863358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_7863358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863358 prefixEnd_7863358 := by exact prefixLift 7863358
  have htrace : WordTrace (prefixWord ++ tailWord_7863358) baseStart_7863358 baseEnd_7863358 := by
    simpa [prefixWord, tailWord_7863358, baseEnd_7863358] using wordTrace_append hprefix tailTrace_7863358
  have hstable : (prefixWord ++ tailWord_7863358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863358).length < 2 ^ (prefixWord ++ tailWord_7863358).sum := by decide
  have hdescent : baseEnd_7863358 < baseStart_7863358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863374 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_7863374 : Nat := 118140960795 + 7863374 * 2 ^ 59
def prefixEnd_7863374 : Nat := 4983230072969 + 3 ^ 40 * 7863374 * 2
def baseEnd_7863374 : Nat := 1345896809355874248920669

theorem tailTrace_7863374 : CollatzResearch.WordTrace tailWord_7863374 prefixEnd_7863374 1345896809355874248920669 := by
  unfold tailWord_7863374
  simp only [CollatzResearch.WordTrace]
  refine ⟨35850101426793303775751647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191200540942897620137342117 35850101426793303775751647)
  ·
    refine ⟨53775152140189955663627471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35850101426793303775751647 53775152140189955663627471)
    ·
      refine ⟨80662728210284933495441207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53775152140189955663627471 80662728210284933495441207)
      ·
        refine ⟨120994092315427400243161811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80662728210284933495441207 120994092315427400243161811)
        ·
          refine ⟨181491138473141100364742717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120994092315427400243161811 181491138473141100364742717)
          ·
            refine ⟨68059176927427912636778519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181491138473141100364742717 68059176927427912636778519)
            ·
              refine ⟨102088765391141868955167779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68059176927427912636778519 102088765391141868955167779)
              ·
                refine ⟨153133148086712803432751669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102088765391141868955167779 153133148086712803432751669)
                ·
                  refine ⟨14356232633129325321820469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153133148086712803432751669 14356232633129325321820469)
                  ·
                    refine ⟨1345896809355874248920669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14356232633129325321820469 1345896809355874248920669)
                    ·
                      rfl

theorem cell23_7863374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_7863374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863374 prefixEnd_7863374 := by exact prefixLift 7863374
  have htrace : WordTrace (prefixWord ++ tailWord_7863374) baseStart_7863374 baseEnd_7863374 := by
    simpa [prefixWord, tailWord_7863374, baseEnd_7863374] using wordTrace_append hprefix tailTrace_7863374
  have hstable : (prefixWord ++ tailWord_7863374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863374).length < 2 ^ (prefixWord ++ tailWord_7863374).sum := by decide
  have hdescent : baseEnd_7863374 < baseStart_7863374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863381 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7863381 : Nat := 118140960795 + 7863381 * 2 ^ 59
def prefixEnd_7863381 : Nat := 4983230072969 + 3 ^ 40 * 7863381 * 2
def baseEnd_7863381 : Nat := 4037694022432204219374475

theorem tailTrace_7863381 : CollatzResearch.WordTrace tailWord_7863381 prefixEnd_7863381 4037694022432204219374475 := by
  unfold tailWord_7863381
  simp only [CollatzResearch.WordTrace]
  refine ⟨286801066725321070401517997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191200711150214046934345331 286801066725321070401517997)
  ·
    refine ⟨107550400021995401400569249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286801066725321070401517997 107550400021995401400569249)
    ·
      refine ⟨80662800016496551050426937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107550400021995401400569249 80662800016496551050426937)
      ·
        refine ⟨60497100012372413287820203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80662800016496551050426937 60497100012372413287820203)
        ·
          refine ⟨90745650018558619931730305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60497100012372413287820203 90745650018558619931730305)
          ·
            refine ⟨68059237513918964948797729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90745650018558619931730305 68059237513918964948797729)
            ·
              refine ⟨51044428135439223711598297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68059237513918964948797729 51044428135439223711598297)
              ·
                refine ⟨38283321101579417783698723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51044428135439223711598297 38283321101579417783698723)
                ·
                  refine ⟨57424981652369126675548085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38283321101579417783698723 57424981652369126675548085)
                  ·
                    refine ⟨5383592029909605625832633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57424981652369126675548085 5383592029909605625832633)
                    ·
                      refine ⟨4037694022432204219374475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383592029909605625832633 4037694022432204219374475)
                      ·
                        rfl

theorem cell23_7863381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7863381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863381 prefixEnd_7863381 := by exact prefixLift 7863381
  have htrace : WordTrace (prefixWord ++ tailWord_7863381) baseStart_7863381 baseEnd_7863381 := by
    simpa [prefixWord, tailWord_7863381, baseEnd_7863381] using wordTrace_append hprefix tailTrace_7863381
  have hstable : (prefixWord ++ tailWord_7863381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863381).length < 2 ^ (prefixWord ++ tailWord_7863381).sum := by decide
  have hdescent : baseEnd_7863381 < baseStart_7863381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863388 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7863388 : Nat := 118140960795 + 7863388 * 2 ^ 59
def prefixEnd_7863388 : Nat := 4983230072969 + 3 ^ 40 * 7863388 * 2
def baseEnd_7863388 : Nat := 4037697616796785691986943

theorem tailTrace_7863388 : CollatzResearch.WordTrace tailWord_7863388 prefixEnd_7863388 4037697616796785691986943 := by
  unfold tailWord_7863388
  simp only [CollatzResearch.WordTrace]
  refine ⟨143400661018147855298511409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191200881357530473731348545 143400661018147855298511409)
  ·
    refine ⟨107550495763610891473883557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143400661018147855298511409 107550495763610891473883557)
    ·
      refine ⟨20165717955677042151353167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107550495763610891473883557 20165717955677042151353167)
      ·
        refine ⟨30248576933515563227029751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20165717955677042151353167 30248576933515563227029751)
        ·
          refine ⟨45372865400273344840544627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30248576933515563227029751 45372865400273344840544627)
          ·
            refine ⟨68059298100410017260816941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45372865400273344840544627 68059298100410017260816941)
            ·
              refine ⟨25522236787653756472806353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68059298100410017260816941 25522236787653756472806353)
              ·
                refine ⟨19141677590740317354604765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25522236787653756472806353 19141677590740317354604765)
                ·
                  refine ⟨7178129096527619007976787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19141677590740317354604765 7178129096527619007976787)
                  ·
                    refine ⟨10767193644791428511965181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178129096527619007976787 10767193644791428511965181)
                    ·
                      refine ⟨4037697616796785691986943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767193644791428511965181 4037697616796785691986943)
                      ·
                        rfl

theorem cell23_7863388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7863388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863388 prefixEnd_7863388 := by exact prefixLift 7863388
  have htrace : WordTrace (prefixWord ++ tailWord_7863388) baseStart_7863388 baseEnd_7863388 := by
    simpa [prefixWord, tailWord_7863388, baseEnd_7863388] using wordTrace_append hprefix tailTrace_7863388
  have hstable : (prefixWord ++ tailWord_7863388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863388).length < 2 ^ (prefixWord ++ tailWord_7863388).sum := by decide
  have hdescent : baseEnd_7863388 < baseStart_7863388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863404 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_7863404 : Nat := 118140960795 + 7863404 * 2 ^ 59
def prefixEnd_7863404 : Nat := 4983230072969 + 3 ^ 40 * 7863404 * 2
def baseEnd_7863404 : Nat := 1345901944162419209795623

theorem tailTrace_7863404 : CollatzResearch.WordTrace tailWord_7863404 prefixEnd_7863404 1345901944162419209795623 := by
  unfold tailWord_7863404
  simp only [CollatzResearch.WordTrace]
  refine ⟨143400952802118872664802633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191201270402825163553070177 143400952802118872664802633)
  ·
    refine ⟨107550714601589154498601975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143400952802118872664802633 107550714601589154498601975)
    ·
      refine ⟨161326071902383731747902963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107550714601589154498601975 161326071902383731747902963)
      ·
        refine ⟨241989107853575597621854445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161326071902383731747902963 241989107853575597621854445)
        ·
          refine ⟨90745915445090849108195417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241989107853575597621854445 90745915445090849108195417)
          ·
            refine ⟨68059436583818136831146563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90745915445090849108195417 68059436583818136831146563)
            ·
              refine ⟨102089154875727205246719845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68059436583818136831146563 102089154875727205246719845)
              ·
                refine ⟨19141716539198850983759971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102089154875727205246719845 19141716539198850983759971)
                ·
                  refine ⟨28712574808798276475639957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19141716539198850983759971 28712574808798276475639957)
                  ·
                    refine ⟨1345901944162419209795623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28712574808798276475639957 1345901944162419209795623)
                    ·
                      rfl

theorem cell23_7863404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_7863404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863404 prefixEnd_7863404 := by exact prefixLift 7863404
  have htrace : WordTrace (prefixWord ++ tailWord_7863404) baseStart_7863404 baseEnd_7863404 := by
    simpa [prefixWord, tailWord_7863404, baseEnd_7863404] using wordTrace_append hprefix tailTrace_7863404
  have hstable : (prefixWord ++ tailWord_7863404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863404).length < 2 ^ (prefixWord ++ tailWord_7863404).sum := by decide
  have hdescent : baseEnd_7863404 < baseStart_7863404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863405 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_7863405 : Nat := 118140960795 + 7863405 * 2 ^ 59
def prefixEnd_7863405 : Nat := 4983230072969 + 3 ^ 40 * 7863405 * 2
def baseEnd_7863405 : Nat := 4037706345967912125474365

theorem tailTrace_7863405 : CollatzResearch.WordTrace tailWord_7863405 prefixEnd_7863405 4037706345967912125474365 := by
  unfold tailWord_7863405
  simp only [CollatzResearch.WordTrace]
  refine ⟨286801942077234122500391669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191201294718156081666927779 286801942077234122500391669)
  ·
    refine ⟨26887682069740698984411719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286801942077234122500391669 26887682069740698984411719)
    ·
      refine ⟨40331523104611048476617579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26887682069740698984411719 40331523104611048476617579)
      ·
        refine ⟨60497284656916572714926369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40331523104611048476617579 60497284656916572714926369)
        ·
          refine ⟨45372963492687429536194777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60497284656916572714926369 45372963492687429536194777)
          ·
            refine ⟨34029722619515572152146083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45372963492687429536194777 34029722619515572152146083)
            ·
              refine ⟨51044583929273358228219125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34029722619515572152146083 51044583929273358228219125)
              ·
                refine ⟨4785429743369377333895543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51044583929273358228219125 4785429743369377333895543)
                ·
                  refine ⟨7178144615054066000843315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785429743369377333895543 7178144615054066000843315)
                  ·
                    refine ⟨10767216922581099001264973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178144615054066000843315 10767216922581099001264973)
                    ·
                      refine ⟨4037706345967912125474365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767216922581099001264973 4037706345967912125474365)
                      ·
                        rfl

theorem cell23_7863405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_7863405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863405 prefixEnd_7863405 := by exact prefixLift 7863405
  have htrace : WordTrace (prefixWord ++ tailWord_7863405) baseStart_7863405 baseEnd_7863405 := by
    simpa [prefixWord, tailWord_7863405, baseEnd_7863405] using wordTrace_append hprefix tailTrace_7863405
  have hstable : (prefixWord ++ tailWord_7863405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863405).length < 2 ^ (prefixWord ++ tailWord_7863405).sum := by decide
  have hdescent : baseEnd_7863405 < baseStart_7863405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863421 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_7863421 : Nat := 118140960795 + 7863421 * 2 ^ 59
def prefixEnd_7863421 : Nat := 4983230072969 + 3 ^ 40 * 7863421 * 2
def baseEnd_7863421 : Nat := 1345904853886128020958097

theorem tailTrace_7863421 : CollatzResearch.WordTrace tailWord_7863421 prefixEnd_7863421 1345904853886128020958097 := by
  unfold tailWord_7863421
  simp only [CollatzResearch.WordTrace]
  refine ⟨286802525645176157232974117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191201683763450771488649411 286802525645176157232974117)
  ·
    refine ⟨53775473558470529481182647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286802525645176157232974117 53775473558470529481182647)
    ·
      refine ⟨80663210337705794221773971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53775473558470529481182647 80663210337705794221773971)
      ·
        refine ⟨120994815506558691332660957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80663210337705794221773971 120994815506558691332660957)
        ·
          refine ⟨45373055814959509249747859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120994815506558691332660957 45373055814959509249747859)
          ·
            refine ⟨68059583722439263874621789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45373055814959509249747859 68059583722439263874621789)
            ·
              refine ⟨25522343895914723952983171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68059583722439263874621789 25522343895914723952983171)
              ·
                refine ⟨38283515843872085929474757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25522343895914723952983171 38283515843872085929474757)
                ·
                  refine ⟨7178159220726016111776517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38283515843872085929474757 7178159220726016111776517)
                  ·
                    refine ⟨1345904853886128020958097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7178159220726016111776517 1345904853886128020958097)
                    ·
                      rfl

theorem cell23_7863421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_7863421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863421 prefixEnd_7863421 := by exact prefixLift 7863421
  have htrace : WordTrace (prefixWord ++ tailWord_7863421) baseStart_7863421 baseEnd_7863421 := by
    simpa [prefixWord, tailWord_7863421, baseEnd_7863421] using wordTrace_append hprefix tailTrace_7863421
  have hstable : (prefixWord ++ tailWord_7863421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863421).length < 2 ^ (prefixWord ++ tailWord_7863421).sum := by decide
  have hdescent : baseEnd_7863421 < baseStart_7863421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863424 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_7863424 : Nat := 118140960795 + 7863424 * 2 ^ 59
def prefixEnd_7863424 : Nat := 4983230072969 + 3 ^ 40 * 7863424 * 2
def baseEnd_7863424 : Nat := 4037716102100347551136777

theorem tailTrace_7863424 : CollatzResearch.WordTrace tailWord_7863424 prefixEnd_7863424 4037716102100347551136777 := by
  unfold tailWord_7863424
  simp only [CollatzResearch.WordTrace]
  refine ⟨143401317532082644372666663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191201756709443525830222217 143401317532082644372666663)
  ·
    refine ⟨215101976298123966558999995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143401317532082644372666663 215101976298123966558999995)
    ·
      refine ⟨322652964447185949838499993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215101976298123966558999995 322652964447185949838499993)
      ·
        refine ⟨241989723335389462378874995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322652964447185949838499993 241989723335389462378874995)
        ·
          refine ⟨362984585003084193568312493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241989723335389462378874995 362984585003084193568312493)
          ·
            refine ⟨136119219376156572588117185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362984585003084193568312493 136119219376156572588117185)
            ·
              refine ⟨102089414532117429441087889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136119219376156572588117185 102089414532117429441087889)
              ·
                refine ⟨76567060899088072080815917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102089414532117429441087889 76567060899088072080815917)
                ·
                  refine ⟨28712647837158027030305969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76567060899088072080815917 28712647837158027030305969)
                  ·
                    refine ⟨21534485877868520272729477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28712647837158027030305969 21534485877868520272729477)
                    ·
                      refine ⟨4037716102100347551136777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21534485877868520272729477 4037716102100347551136777)
                      ·
                        rfl

theorem cell23_7863424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_7863424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863424 prefixEnd_7863424 := by exact prefixLift 7863424
  have htrace : WordTrace (prefixWord ++ tailWord_7863424) baseStart_7863424 baseEnd_7863424 := by
    simpa [prefixWord, tailWord_7863424, baseEnd_7863424] using wordTrace_append hprefix tailTrace_7863424
  have hstable : (prefixWord ++ tailWord_7863424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863424).length < 2 ^ (prefixWord ++ tailWord_7863424).sum := by decide
  have hdescent : baseEnd_7863424 < baseStart_7863424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863434 : List Nat := [3, 1, 2, 3, 1, 1, 2, 10]
def baseStart_7863434 : Nat := 118140960795 + 7863434 * 2 ^ 59
def prefixEnd_7863434 : Nat := 4983230072969 + 3 ^ 40 * 7863434 * 2
def baseEnd_7863434 : Nat := 149545230996551574518953

theorem tailTrace_7863434 : CollatzResearch.WordTrace tailWord_7863434 prefixEnd_7863434 149545230996551574518953 := by
  unfold tailWord_7863434
  simp only [CollatzResearch.WordTrace]
  refine ⟨71700749948532265113299339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191201999862752706968798237 71700749948532265113299339)
  ·
    refine ⟨107551124922798397669949009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71700749948532265113299339 107551124922798397669949009)
    ·
      refine ⟨80663343692098798252461757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107551124922798397669949009 80663343692098798252461757)
      ·
        refine ⟨30248753884537049344673159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80663343692098798252461757 30248753884537049344673159)
        ·
          refine ⟨45373130826805574017009739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30248753884537049344673159 45373130826805574017009739)
          ·
            refine ⟨68059696240208361025514609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45373130826805574017009739 68059696240208361025514609)
            ·
              refine ⟨51044772180156270769135957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68059696240208361025514609 51044772180156270769135957)
              ·
                refine ⟨149545230996551574518953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51044772180156270769135957 149545230996551574518953)
                ·
                  rfl

theorem cell23_7863434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_7863434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863434 prefixEnd_7863434 := by exact prefixLift 7863434
  have htrace : WordTrace (prefixWord ++ tailWord_7863434) baseStart_7863434 baseEnd_7863434 := by
    simpa [prefixWord, tailWord_7863434, baseEnd_7863434] using wordTrace_append hprefix tailTrace_7863434
  have hstable : (prefixWord ++ tailWord_7863434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863434).length < 2 ^ (prefixWord ++ tailWord_7863434).sum := by decide
  have hdescent : baseEnd_7863434 < baseStart_7863434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863438 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_7863438 : Nat := 118140960795 + 7863438 * 2 ^ 59
def prefixEnd_7863438 : Nat := 4983230072969 + 3 ^ 40 * 7863438 * 2
def baseEnd_7863438 : Nat := 1345907763609836832120571

theorem tailTrace_7863438 : CollatzResearch.WordTrace tailWord_7863438 prefixEnd_7863438 1345907763609836832120571 := by
  unfold tailWord_7863438
  simp only [CollatzResearch.WordTrace]
  refine ⟨35850393210764321142042871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191202097124076379424228645 35850393210764321142042871)
  ·
    refine ⟨53775589816146481713064307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35850393210764321142042871 53775589816146481713064307)
    ·
      refine ⟨80663384724219722569596461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53775589816146481713064307 80663384724219722569596461)
      ·
        refine ⟨30248769271582395963598673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80663384724219722569596461 30248769271582395963598673)
        ·
          refine ⟨22686576953686796972699005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30248769271582395963598673 22686576953686796972699005)
          ·
            refine ⟨8507466357632548864762127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22686576953686796972699005 8507466357632548864762127)
            ·
              refine ⟨12761199536448823297143191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507466357632548864762127 12761199536448823297143191)
              ·
                refine ⟨19141799304673234945714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12761199536448823297143191 19141799304673234945714787)
                ·
                  refine ⟨28712698957009852418572181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19141799304673234945714787 28712698957009852418572181)
                  ·
                    refine ⟨1345907763609836832120571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28712698957009852418572181 1345907763609836832120571)
                    ·
                      rfl

theorem cell23_7863438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_7863438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863438 prefixEnd_7863438 := by exact prefixLift 7863438
  have htrace : WordTrace (prefixWord ++ tailWord_7863438) baseStart_7863438 baseEnd_7863438 := by
    simpa [prefixWord, tailWord_7863438, baseEnd_7863438] using wordTrace_append hprefix tailTrace_7863438
  have hstable : (prefixWord ++ tailWord_7863438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863438).length < 2 ^ (prefixWord ++ tailWord_7863438).sum := by decide
  have hdescent : baseEnd_7863438 < baseStart_7863438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863448 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_7863448 : Nat := 118140960795 + 7863448 * 2 ^ 59
def prefixEnd_7863448 : Nat := 4983230072969 + 3 ^ 40 * 7863448 * 2
def baseEnd_7863448 : Nat := 4037728425636055457236667

theorem tailTrace_7863448 : CollatzResearch.WordTrace tailWord_7863448 prefixEnd_7863448 4037728425636055457236667 := by
  unfold tailWord_7863448
  simp only [CollatzResearch.WordTrace]
  refine ⟨143401755208039170422103499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191202340277385560562804665 143401755208039170422103499)
  ·
    refine ⟨215102632812058755633155249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143401755208039170422103499 215102632812058755633155249)
    ·
      refine ⟨161326974609044066724866437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215102632812058755633155249 161326974609044066724866437)
      ·
        refine ⟨30248807739195762510912457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161326974609044066724866437 30248807739195762510912457)
        ·
          refine ⟨22686605804396821883184343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30248807739195762510912457 22686605804396821883184343)
          ·
            refine ⟨34029908706595232824776515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22686605804396821883184343 34029908706595232824776515)
            ·
              refine ⟨51044863059892849237164773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34029908706595232824776515 51044863059892849237164773)
              ·
                refine ⟨9570911823729909231968395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51044863059892849237164773 9570911823729909231968395)
                ·
                  refine ⟨14356367735594863847952593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570911823729909231968395 14356367735594863847952593)
                  ·
                    refine ⟨10767275801696147885964445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14356367735594863847952593 10767275801696147885964445)
                    ·
                      refine ⟨4037728425636055457236667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767275801696147885964445 4037728425636055457236667)
                      ·
                        rfl

theorem cell23_7863448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_7863448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863448 prefixEnd_7863448 := by exact prefixLift 7863448
  have htrace : WordTrace (prefixWord ++ tailWord_7863448) baseStart_7863448 baseEnd_7863448 := by
    simpa [prefixWord, tailWord_7863448, baseEnd_7863448] using wordTrace_append hprefix tailTrace_7863448
  have hstable : (prefixWord ++ tailWord_7863448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863448).length < 2 ^ (prefixWord ++ tailWord_7863448).sum := by decide
  have hdescent : baseEnd_7863448 < baseStart_7863448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863521 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7863521 : Nat := 118140960795 + 7863521 * 2 ^ 59
def prefixEnd_7863521 : Nat := 4983230072969 + 3 ^ 40 * 7863521 * 2
def baseEnd_7863521 : Nat := 4037765909723833671623831

theorem tailTrace_7863521 : CollatzResearch.WordTrace tailWord_7863521 prefixEnd_7863521 4037765909723833671623831 := by
  unfold tailWord_7863521
  simp only [CollatzResearch.WordTrace]
  refine ⟨286806172944813874311614417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191204115296542582874409611 286806172944813874311614417)
  ·
    refine ⟨215104629708610405733710813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286806172944813874311614417 215104629708610405733710813)
    ·
      refine ⟨80664236140728902150141555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215104629708610405733710813 80664236140728902150141555)
      ·
        refine ⟨120996354211093353225212333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80664236140728902150141555 120996354211093353225212333)
        ·
          refine ⟨45373632829160007459454625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120996354211093353225212333 45373632829160007459454625)
          ·
            refine ⟨34030224621870005594590969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45373632829160007459454625 34030224621870005594590969)
            ·
              refine ⟨25522668466402504195943227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34030224621870005594590969 25522668466402504195943227)
              ·
                refine ⟨38284002699603756293914841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25522668466402504195943227 38284002699603756293914841)
                ·
                  refine ⟨28713002024702817220436131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38284002699603756293914841 28713002024702817220436131)
                  ·
                    refine ⟨43069503037054225830654197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28713002024702817220436131 43069503037054225830654197)
                    ·
                      refine ⟨4037765909723833671623831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43069503037054225830654197 4037765909723833671623831)
                      ·
                        rfl

theorem cell23_7863521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7863521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863521 prefixEnd_7863521 := by exact prefixLift 7863521
  have htrace : WordTrace (prefixWord ++ tailWord_7863521) baseStart_7863521 baseEnd_7863521 := by
    simpa [prefixWord, tailWord_7863521, baseEnd_7863521] using wordTrace_append hprefix tailTrace_7863521
  have hstable : (prefixWord ++ tailWord_7863521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863521).length < 2 ^ (prefixWord ++ tailWord_7863521).sum := by decide
  have hdescent : baseEnd_7863521 < baseStart_7863521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863544 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_7863544 : Nat := 118140960795 + 7863544 * 2 ^ 59
def prefixEnd_7863544 : Nat := 4983230072969 + 3 ^ 40 * 7863544 * 2
def baseEnd_7863544 : Nat := 4037777719778887081636225

theorem tailTrace_7863544 : CollatzResearch.WordTrace tailWord_7863544 prefixEnd_7863544 4037777719778887081636225 := by
  unfold tailWord_7863544
  simp only [CollatzResearch.WordTrace]
  refine ⟨143403505911865274619850843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191204674549153699493134457 143403505911865274619850843)
  ·
    refine ⟨215105258867797911929776265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143403505911865274619850843 215105258867797911929776265)
    ·
      refine ⟨161328944150848433947332199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215105258867797911929776265 161328944150848433947332199)
      ·
        refine ⟨241993416226272650920998299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161328944150848433947332199 241993416226272650920998299)
        ·
          refine ⟨362990124339408976381497449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241993416226272650920998299 362990124339408976381497449)
          ·
            refine ⟨272242593254556732286123087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362990124339408976381497449 272242593254556732286123087)
            ·
              refine ⟨408363889881835098429184631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272242593254556732286123087 408363889881835098429184631)
              ·
                refine ⟨612545834822752647643776947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408363889881835098429184631 612545834822752647643776947)
                ·
                  refine ⟨918818752234128971465665421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612545834822752647643776947 918818752234128971465665421)
                  ·
                    refine ⟨344557032087798364299624533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918818752234128971465665421 344557032087798364299624533)
                    ·
                      refine ⟨4037777719778887081636225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 344557032087798364299624533 4037777719778887081636225)
                      ·
                        rfl

theorem cell23_7863544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_7863544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863544 prefixEnd_7863544 := by exact prefixLift 7863544
  have htrace : WordTrace (prefixWord ++ tailWord_7863544) baseStart_7863544 baseEnd_7863544 := by
    simpa [prefixWord, tailWord_7863544, baseEnd_7863544] using wordTrace_append hprefix tailTrace_7863544
  have hstable : (prefixWord ++ tailWord_7863544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863544).length < 2 ^ (prefixWord ++ tailWord_7863544).sum := by decide
  have hdescent : baseEnd_7863544 < baseStart_7863544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863548 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_7863548 : Nat := 118140960795 + 7863548 * 2 ^ 59
def prefixEnd_7863548 : Nat := 4983230072969 + 3 ^ 40 * 7863548 * 2
def baseEnd_7863548 : Nat := 4037779773701505065986207

theorem tailTrace_7863548 : CollatzResearch.WordTrace tailWord_7863548 prefixEnd_7863548 4037779773701505065986207 := by
  unfold tailWord_7863548
  simp only [CollatzResearch.WordTrace]
  refine ⟨143403578857858028961423649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191204771810477371948564865 143403578857858028961423649)
  ·
    refine ⟨107552684143393521721067737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143403578857858028961423649 107552684143393521721067737)
    ·
      refine ⟨80664513107545141290800803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107552684143393521721067737 80664513107545141290800803)
      ·
        refine ⟨120996769661317711936201205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80664513107545141290800803 120996769661317711936201205)
        ·
          refine ⟨11343447155748535494018863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120996769661317711936201205 11343447155748535494018863)
          ·
            refine ⟨17015170733622803241028295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343447155748535494018863 17015170733622803241028295)
            ·
              refine ⟨25522756100434204861542443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17015170733622803241028295 25522756100434204861542443)
              ·
                refine ⟨38284134150651307292313665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25522756100434204861542443 38284134150651307292313665)
                ·
                  refine ⟨28713100612988480469235249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38284134150651307292313665 28713100612988480469235249)
                  ·
                    refine ⟨21534825459741360351926437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28713100612988480469235249 21534825459741360351926437)
                    ·
                      refine ⟨4037779773701505065986207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21534825459741360351926437 4037779773701505065986207)
                      ·
                        rfl

theorem cell23_7863548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_7863548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863548 prefixEnd_7863548 := by exact prefixLift 7863548
  have htrace : WordTrace (prefixWord ++ tailWord_7863548) baseStart_7863548 baseEnd_7863548 := by
    simpa [prefixWord, tailWord_7863548, baseEnd_7863548] using wordTrace_append hprefix tailTrace_7863548
  have hstable : (prefixWord ++ tailWord_7863548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863548).length < 2 ^ (prefixWord ++ tailWord_7863548).sum := by decide
  have hdescent : baseEnd_7863548 < baseStart_7863548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863551 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_7863551 : Nat := 118140960795 + 7863551 * 2 ^ 59
def prefixEnd_7863551 : Nat := 4983230072969 + 3 ^ 40 * 7863551 * 2
def baseEnd_7863551 : Nat := 4037781314143468554248693

theorem tailTrace_7863551 : CollatzResearch.WordTrace tailWord_7863551 prefixEnd_7863551 4037781314143468554248693 := by
  unfold tailWord_7863551
  simp only [CollatzResearch.WordTrace]
  refine ⟨286807267134705189435206507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191204844756470126290137671 286807267134705189435206507)
  ·
    refine ⟨430210900702057784152809761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286807267134705189435206507 430210900702057784152809761)
    ·
      refine ⟨322658175526543338114607321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430210900702057784152809761 322658175526543338114607321)
      ·
        refine ⟨241993631644907503585955491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322658175526543338114607321 241993631644907503585955491)
        ·
          refine ⟨362990447467361255378933237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241993631644907503585955491 362990447467361255378933237)
          ·
            refine ⟨34030354450065117691774991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362990447467361255378933237 34030354450065117691774991)
            ·
              refine ⟨51045531675097676537662487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34030354450065117691774991 51045531675097676537662487)
              ·
                refine ⟨76568297512646514806493731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51045531675097676537662487 76568297512646514806493731)
                ·
                  refine ⟨114852446268969772209740597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76568297512646514806493731 114852446268969772209740597)
                  ·
                    refine ⟨10767416837715916144663181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114852446268969772209740597 10767416837715916144663181)
                    ·
                      refine ⟨4037781314143468554248693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767416837715916144663181 4037781314143468554248693)
                      ·
                        rfl

theorem cell23_7863551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_7863551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863551 prefixEnd_7863551 := by exact prefixLift 7863551
  have htrace : WordTrace (prefixWord ++ tailWord_7863551) baseStart_7863551 baseEnd_7863551 := by
    simpa [prefixWord, tailWord_7863551, baseEnd_7863551] using wordTrace_append hprefix tailTrace_7863551
  have hstable : (prefixWord ++ tailWord_7863551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863551).length < 2 ^ (prefixWord ++ tailWord_7863551).sum := by decide
  have hdescent : baseEnd_7863551 < baseStart_7863551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863586 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_7863586 : Nat := 118140960795 + 7863586 * 2 ^ 59
def prefixEnd_7863586 : Nat := 4983230072969 + 3 ^ 40 * 7863586 * 2
def baseEnd_7863586 : Nat := 4037799285966375917311033

theorem tailTrace_7863586 : CollatzResearch.WordTrace tailWord_7863586 prefixEnd_7863586 4037799285966375917311033 := by
  unfold tailWord_7863586
  simp only [CollatzResearch.WordTrace]
  refine ⟨71702135922394597603182653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191205695793052260275153741 71702135922394597603182653)
  ·
    refine ⟨26888300970897974101193495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71702135922394597603182653 26888300970897974101193495)
    ·
      refine ⟨40332451456346961151790243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26888300970897974101193495 40332451456346961151790243)
      ·
        refine ⟨60498677184520441727685365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40332451456346961151790243 60498677184520441727685365)
        ·
          refine ⟨5671750986048791411970503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60498677184520441727685365 5671750986048791411970503)
          ·
            refine ⟨8507626479073187117955755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671750986048791411970503 8507626479073187117955755)
            ·
              refine ⟨12761439718609780676933633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507626479073187117955755 12761439718609780676933633)
              ·
                refine ⟨9571079788957335507700225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12761439718609780676933633 9571079788957335507700225)
                ·
                  refine ⟨7178309841718001630775169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9571079788957335507700225 7178309841718001630775169)
                  ·
                    refine ⟨5383732381288501223081377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7178309841718001630775169 5383732381288501223081377)
                    ·
                      refine ⟨4037799285966375917311033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383732381288501223081377 4037799285966375917311033)
                      ·
                        rfl

theorem cell23_7863586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_7863586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863586 prefixEnd_7863586 := by exact prefixLift 7863586
  have htrace : WordTrace (prefixWord ++ tailWord_7863586) baseStart_7863586 baseEnd_7863586 := by
    simpa [prefixWord, tailWord_7863586, baseEnd_7863586] using wordTrace_append hprefix tailTrace_7863586
  have hstable : (prefixWord ++ tailWord_7863586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863586).length < 2 ^ (prefixWord ++ tailWord_7863586).sum := by decide
  have hdescent : baseEnd_7863586 < baseStart_7863586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863628 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_7863628 : Nat := 118140960795 + 7863628 * 2 ^ 59
def prefixEnd_7863628 : Nat := 4983230072969 + 3 ^ 40 * 7863628 * 2
def baseEnd_7863628 : Nat := 4037820852153864752985839

theorem tailTrace_7863628 : CollatzResearch.WordTrace tailWord_7863628 prefixEnd_7863628 4037820852153864752985839 := by
  unfold tailWord_7863628
  simp only [CollatzResearch.WordTrace]
  refine ⟨143405037777713115792879769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191206717036950821057173025 143405037777713115792879769)
  ·
    refine ⟨107553778333284836844659827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143405037777713115792879769 107553778333284836844659827)
    ·
      refine ⟨161330667499927255266989741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107553778333284836844659827 161330667499927255266989741)
      ·
        refine ⟨60499000312472720725121153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161330667499927255266989741 60499000312472720725121153)
        ·
          refine ⟨45374250234354540543840865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60499000312472720725121153 45374250234354540543840865)
          ·
            refine ⟨34030687675765905407880649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45374250234354540543840865 34030687675765905407880649)
            ·
              refine ⟨25523015756824429055910487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34030687675765905407880649 25523015756824429055910487)
              ·
                refine ⟨38284523635236643583865731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25523015756824429055910487 38284523635236643583865731)
                ·
                  refine ⟨57426785452854965375798597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38284523635236643583865731 57426785452854965375798597)
                  ·
                    refine ⟨10767522272410306007962237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57426785452854965375798597 10767522272410306007962237)
                    ·
                      refine ⟨4037820852153864752985839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767522272410306007962237 4037820852153864752985839)
                      ·
                        rfl

theorem cell23_7863628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_7863628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863628 prefixEnd_7863628 := by exact prefixLift 7863628
  have htrace : WordTrace (prefixWord ++ tailWord_7863628) baseStart_7863628 baseEnd_7863628 := by
    simpa [prefixWord, tailWord_7863628, baseEnd_7863628] using wordTrace_append hprefix tailTrace_7863628
  have hstable : (prefixWord ++ tailWord_7863628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863628).length < 2 ^ (prefixWord ++ tailWord_7863628).sum := by decide
  have hdescent : baseEnd_7863628 < baseStart_7863628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863685 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 2, 3, 2]
def baseStart_7863685 : Nat := 118140960795 + 7863685 * 2 ^ 59
def prefixEnd_7863685 : Nat := 4983230072969 + 3 ^ 40 * 7863685 * 2
def baseEnd_7863685 : Nat := 4037850120551171029973077

theorem tailTrace_7863685 : CollatzResearch.WordTrace tailWord_7863685 prefixEnd_7863685 4037850120551171029973077 := by
  unfold tailWord_7863685
  simp only [CollatzResearch.WordTrace]
  refine ⟨286812154516219730320584509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191208103010813153547056339 286812154516219730320584509)
  ·
    refine ⟨107554557943582398870219191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286812154516219730320584509 107554557943582398870219191)
    ·
      refine ⟨161331836915373598305328787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107554557943582398870219191 161331836915373598305328787)
      ·
        refine ⟨241997755373060397457993181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161331836915373598305328787 241997755373060397457993181)
        ·
          refine ⟨90749158264897649046747443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241997755373060397457993181 90749158264897649046747443)
          ·
            refine ⟨136123737397346473570121165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90749158264897649046747443 136123737397346473570121165)
            ·
              refine ⟨51046401524004927588795437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136123737397346473570121165 51046401524004927588795437)
              ·
                refine ⟨19142400571501847845798289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51046401524004927588795437 19142400571501847845798289)
                ·
                  refine ⟨14356800428626385884348717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19142400571501847845798289 14356800428626385884348717)
                  ·
                    refine ⟨5383800160734894706630769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14356800428626385884348717 5383800160734894706630769)
                    ·
                      refine ⟨4037850120551171029973077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383800160734894706630769 4037850120551171029973077)
                      ·
                        rfl

theorem cell23_7863685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_7863685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863685 prefixEnd_7863685 := by exact prefixLift 7863685
  have htrace : WordTrace (prefixWord ++ tailWord_7863685) baseStart_7863685 baseEnd_7863685 := by
    simpa [prefixWord, tailWord_7863685, baseEnd_7863685] using wordTrace_append hprefix tailTrace_7863685
  have hstable : (prefixWord ++ tailWord_7863685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863685).length < 2 ^ (prefixWord ++ tailWord_7863685).sum := by decide
  have hdescent : baseEnd_7863685 < baseStart_7863685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863692 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 1, 1, 3]
def baseStart_7863692 : Nat := 118140960795 + 7863692 * 2 ^ 59
def prefixEnd_7863692 : Nat := 4983230072969 + 3 ^ 40 * 7863692 * 2
def baseEnd_7863692 : Nat := 4037853714915752502585545

theorem tailTrace_7863692 : CollatzResearch.WordTrace tailWord_7863692 prefixEnd_7863692 4037853714915752502585545 := by
  unfold tailWord_7863692
  simp only [CollatzResearch.WordTrace]
  refine ⟨143406204913597185258044665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191208273218129580344059553 143406204913597185258044665)
  ·
    refine ⟨107554653685197888943533499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143406204913597185258044665 107554653685197888943533499)
    ·
      refine ⟨161331980527796833415300249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107554653685197888943533499 161331980527796833415300249)
      ·
        refine ⟨120998985395847625061475187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161331980527796833415300249 120998985395847625061475187)
        ·
          refine ⟨181498478093771437592212781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120998985395847625061475187 181498478093771437592212781)
          ·
            refine ⟨68061929285164289097079793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181498478093771437592212781 68061929285164289097079793)
            ·
              refine ⟨51046446963873216822809845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68061929285164289097079793 51046446963873216822809845)
              ·
                refine ⟨4785604402863114077138423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51046446963873216822809845 4785604402863114077138423)
                ·
                  refine ⟨7178406604294671115707635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785604402863114077138423 7178406604294671115707635)
                  ·
                    refine ⟨10767609906442006673561453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178406604294671115707635 10767609906442006673561453)
                    ·
                      refine ⟨4037853714915752502585545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767609906442006673561453 4037853714915752502585545)
                      ·
                        rfl

theorem cell23_7863692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_7863692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863692 prefixEnd_7863692 := by exact prefixLift 7863692
  have htrace : WordTrace (prefixWord ++ tailWord_7863692) baseStart_7863692 baseEnd_7863692 := by
    simpa [prefixWord, tailWord_7863692, baseEnd_7863692] using wordTrace_append hprefix tailTrace_7863692
  have hstable : (prefixWord ++ tailWord_7863692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863692).length < 2 ^ (prefixWord ++ tailWord_7863692).sum := by decide
  have hdescent : baseEnd_7863692 < baseStart_7863692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863709 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_7863709 : Nat := 118140960795 + 7863709 * 2 ^ 59
def prefixEnd_7863709 : Nat := 4983230072969 + 3 ^ 40 * 7863709 * 2
def baseEnd_7863709 : Nat := 4037862444086878936072967

theorem tailTrace_7863709 : CollatzResearch.WordTrace tailWord_7863709 prefixEnd_7863709 4037862444086878936072967 := by
  unfold tailWord_7863709
  simp only [CollatzResearch.WordTrace]
  refine ⟨286813029868132782419458181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191208686578755188279638787 286813029868132782419458181)
  ·
    refine ⟨53777443100274896703648409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286813029868132782419458181 53777443100274896703648409)
    ·
      refine ⟨40333082325206172527736307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53777443100274896703648409 40333082325206172527736307)
      ·
        refine ⟨60499623487809258791604461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40333082325206172527736307 60499623487809258791604461)
        ·
          refine ⟨22687358807928472046851673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60499623487809258791604461 22687358807928472046851673)
          ·
            refine ⟨17015519105946354035138755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22687358807928472046851673 17015519105946354035138755)
            ·
              refine ⟨25523278658919531052708133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17015519105946354035138755 25523278658919531052708133)
              ·
                refine ⟨4785614748547412072382775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25523278658919531052708133 4785614748547412072382775)
                ·
                  refine ⟨7178422122821118108574163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785614748547412072382775 7178422122821118108574163)
                  ·
                    refine ⟨10767633184231677162861245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178422122821118108574163 10767633184231677162861245)
                    ·
                      refine ⟨4037862444086878936072967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767633184231677162861245 4037862444086878936072967)
                      ·
                        rfl

theorem cell23_7863709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_7863709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863709 prefixEnd_7863709 := by exact prefixLift 7863709
  have htrace : WordTrace (prefixWord ++ tailWord_7863709) baseStart_7863709 baseEnd_7863709 := by
    simpa [prefixWord, tailWord_7863709, baseEnd_7863709] using wordTrace_append hprefix tailTrace_7863709
  have hstable : (prefixWord ++ tailWord_7863709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863709).length < 2 ^ (prefixWord ++ tailWord_7863709).sum := by decide
  have hdescent : baseEnd_7863709 < baseStart_7863709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863725 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7863725 : Nat := 118140960795 + 7863725 * 2 ^ 59
def prefixEnd_7863725 : Nat := 4983230072969 + 3 ^ 40 * 7863725 * 2
def baseEnd_7863725 : Nat := 1345956886592450291157631

theorem tailTrace_7863725 : CollatzResearch.WordTrace tailWord_7863725 prefixEnd_7863725 1345956886592450291157631 := by
  unfold tailWord_7863725
  simp only [CollatzResearch.WordTrace]
  refine ⟨286813613436074817152040629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191209075624049878101360419 286813613436074817152040629)
  ·
    refine ⟨26888776259632014108003809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286813613436074817152040629 26888776259632014108003809)
    ·
      refine ⟨20166582194724010581002857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26888776259632014108003809 20166582194724010581002857)
      ·
        refine ⟨15124936646043007935752143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20166582194724010581002857 15124936646043007935752143)
        ·
          refine ⟨22687404969064511903628215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15124936646043007935752143 22687404969064511903628215)
          ·
            refine ⟨34031107453596767855442323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22687404969064511903628215 34031107453596767855442323)
            ·
              refine ⟨51046661180395151783163485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34031107453596767855442323 51046661180395151783163485)
              ·
                refine ⟨19142497942648181918686307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51046661180395151783163485 19142497942648181918686307)
                ·
                  refine ⟨28713746913972272878029461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19142497942648181918686307 28713746913972272878029461)
                  ·
                    refine ⟨1345956886592450291157631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28713746913972272878029461 1345956886592450291157631)
                    ·
                      rfl

theorem cell23_7863725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7863725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863725 prefixEnd_7863725 := by exact prefixLift 7863725
  have htrace : WordTrace (prefixWord ++ tailWord_7863725) baseStart_7863725 baseEnd_7863725 := by
    simpa [prefixWord, tailWord_7863725, baseEnd_7863725] using wordTrace_append hprefix tailTrace_7863725
  have hstable : (prefixWord ++ tailWord_7863725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863725).length < 2 ^ (prefixWord ++ tailWord_7863725).sum := by decide
  have hdescent : baseEnd_7863725 < baseStart_7863725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863731 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_7863731 : Nat := 118140960795 + 7863731 * 2 ^ 59
def prefixEnd_7863731 : Nat := 4983230072969 + 3 ^ 40 * 7863731 * 2
def baseEnd_7863731 : Nat := 4037873740661277849997865

theorem tailTrace_7863731 : CollatzResearch.WordTrace tailWord_7863731 prefixEnd_7863731 4037873740661277849997865 := by
  unfold tailWord_7863731
  simp only [CollatzResearch.WordTrace]
  refine ⟨286813832274053080176759047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191209221516035386784506031 286813832274053080176759047)
  ·
    refine ⟨430220748411079620265138571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286813832274053080176759047 430220748411079620265138571)
    ·
      refine ⟨645331122616619430397707857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430220748411079620265138571 645331122616619430397707857)
      ·
        refine ⟨483998341962464572798280893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645331122616619430397707857 483998341962464572798280893)
        ·
          refine ⟨181499378235924214799355335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483998341962464572798280893 181499378235924214799355335)
          ·
            refine ⟨272249067353886322199033003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181499378235924214799355335 272249067353886322199033003)
            ·
              refine ⟨408373601030829483298549505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272249067353886322199033003 408373601030829483298549505)
              ·
                refine ⟨306280200773122112473912129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408373601030829483298549505 306280200773122112473912129)
                ·
                  refine ⟨229710150579841584355434097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306280200773122112473912129 229710150579841584355434097)
                  ·
                    refine ⟨172282612934881188266575573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229710150579841584355434097 172282612934881188266575573)
                    ·
                      refine ⟨4037873740661277849997865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172282612934881188266575573 4037873740661277849997865)
                      ·
                        rfl

theorem cell23_7863731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_7863731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863731 prefixEnd_7863731 := by exact prefixLift 7863731
  have htrace : WordTrace (prefixWord ++ tailWord_7863731) baseStart_7863731 baseEnd_7863731 := by
    simpa [prefixWord, tailWord_7863731, baseEnd_7863731] using wordTrace_append hprefix tailTrace_7863731
  have hstable : (prefixWord ++ tailWord_7863731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863731).length < 2 ^ (prefixWord ++ tailWord_7863731).sum := by decide
  have hdescent : baseEnd_7863731 < baseStart_7863731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863735 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_7863735 : Nat := 118140960795 + 7863735 * 2 ^ 59
def prefixEnd_7863735 : Nat := 4983230072969 + 3 ^ 40 * 7863735 * 2
def baseEnd_7863735 : Nat := 4037875794583895834347847

theorem tailTrace_7863735 : CollatzResearch.WordTrace tailWord_7863735 prefixEnd_7863735 4037875794583895834347847 := by
  unfold tailWord_7863735
  simp only [CollatzResearch.WordTrace]
  refine ⟨286813978166038588859904659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191209318777359059239936439 286813978166038588859904659)
  ·
    refine ⟨430220967249057883289856989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286813978166038588859904659 430220967249057883289856989)
    ·
      refine ⟨161332862718396706233696371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430220967249057883289856989 161332862718396706233696371)
      ·
        refine ⟨241999294077595059350544557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161332862718396706233696371 241999294077595059350544557)
        ·
          refine ⟨90749735279098147256454209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241999294077595059350544557 90749735279098147256454209)
          ·
            refine ⟨68062301459323610442340657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90749735279098147256454209 68062301459323610442340657)
            ·
              refine ⟨51046726094492707831755493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68062301459323610442340657 51046726094492707831755493)
              ·
                refine ⟨9571261142717382718454155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51046726094492707831755493 9571261142717382718454155)
                ·
                  refine ⟨14356891714076074077681233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9571261142717382718454155 14356891714076074077681233)
                  ·
                    refine ⟨10767668785557055558260925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14356891714076074077681233 10767668785557055558260925)
                    ·
                      refine ⟨4037875794583895834347847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10767668785557055558260925 4037875794583895834347847)
                      ·
                        rfl

theorem cell23_7863735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_7863735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863735 prefixEnd_7863735 := by exact prefixLift 7863735
  have htrace : WordTrace (prefixWord ++ tailWord_7863735) baseStart_7863735 baseEnd_7863735 := by
    simpa [prefixWord, tailWord_7863735, baseEnd_7863735] using wordTrace_append hprefix tailTrace_7863735
  have hstable : (prefixWord ++ tailWord_7863735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863735).length < 2 ^ (prefixWord ++ tailWord_7863735).sum := by decide
  have hdescent : baseEnd_7863735 < baseStart_7863735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863766 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_7863766 : Nat := 118140960795 + 7863766 * 2 ^ 59
def prefixEnd_7863766 : Nat := 4983230072969 + 3 ^ 40 * 7863766 * 2
def baseEnd_7863766 : Nat := 4037891712484185213060205

theorem tailTrace_7863766 : CollatzResearch.WordTrace tailWord_7863766 prefixEnd_7863766 4037891712484185213060205 := by
  unfold tailWord_7863766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17925944301807892572142697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191210072552617520769522101 17925944301807892572142697)
  ·
    refine ⟨13444458226355919429107023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17925944301807892572142697 13444458226355919429107023)
    ·
      refine ⟨20166687339533879143660535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13444458226355919429107023 20166687339533879143660535)
      ·
        refine ⟨30250031009300818715490803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20166687339533879143660535 30250031009300818715490803)
        ·
          refine ⟨45375046513951228073236205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30250031009300818715490803 45375046513951228073236205)
          ·
            refine ⟨17015642442731710527463577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45375046513951228073236205 17015642442731710527463577)
            ·
              refine ⟨12761731832048782895597683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17015642442731710527463577 12761731832048782895597683)
              ·
                refine ⟨19142597748073174343396525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12761731832048782895597683 19142597748073174343396525)
                ·
                  refine ⟨7178474155527440378773697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19142597748073174343396525 7178474155527440378773697)
                  ·
                    refine ⟨5383855616645580284080273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7178474155527440378773697 5383855616645580284080273)
                    ·
                      refine ⟨4037891712484185213060205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383855616645580284080273 4037891712484185213060205)
                      ·
                        rfl

theorem cell23_7863766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_7863766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863766 prefixEnd_7863766 := by exact prefixLift 7863766
  have htrace : WordTrace (prefixWord ++ tailWord_7863766) baseStart_7863766 baseEnd_7863766 := by
    simpa [prefixWord, tailWord_7863766, baseEnd_7863766] using wordTrace_append hprefix tailTrace_7863766
  have hstable : (prefixWord ++ tailWord_7863766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863766).length < 2 ^ (prefixWord ++ tailWord_7863766).sum := by decide
  have hdescent : baseEnd_7863766 < baseStart_7863766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863789 : List Nat := [1, 5, 1, 3, 3, 1, 2, 7]
def baseStart_7863789 : Nat := 118140960795 + 7863789 * 2 ^ 59
def prefixEnd_7863789 : Nat := 4983230072969 + 3 ^ 40 * 7863789 * 2
def baseEnd_7863789 : Nat := 149551982316268097150837

theorem tailTrace_7863789 : CollatzResearch.WordTrace tailWord_7863789 prefixEnd_7863789 149551982316268097150837 := by
  unfold tailWord_7863789
  simp only [CollatzResearch.WordTrace]
  refine ⟨286815947707842956082370421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191210631805228637388246947 286815947707842956082370421)
  ·
    refine ⟨26888995097610277132722227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286815947707842956082370421 26888995097610277132722227)
    ·
      refine ⟨40333492646415415699083341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26888995097610277132722227 40333492646415415699083341)
      ·
        refine ⟨15125059742405780887156253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40333492646415415699083341 15125059742405780887156253)
        ·
          refine ⟨5671897403402167832683595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15125059742405780887156253 5671897403402167832683595)
          ·
            refine ⟨8507846105103251749025393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671897403402167832683595 8507846105103251749025393)
            ·
              refine ⟨6380884578827438811769045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8507846105103251749025393 6380884578827438811769045)
              ·
                refine ⟨149551982316268097150837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6380884578827438811769045 149551982316268097150837)
                ·
                  rfl

theorem cell23_7863789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 7].length) (baseStart_7863789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863789 prefixEnd_7863789 := by exact prefixLift 7863789
  have htrace : WordTrace (prefixWord ++ tailWord_7863789) baseStart_7863789 baseEnd_7863789 := by
    simpa [prefixWord, tailWord_7863789, baseEnd_7863789] using wordTrace_append hprefix tailTrace_7863789
  have hstable : (prefixWord ++ tailWord_7863789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863789).length < 2 ^ (prefixWord ++ tailWord_7863789).sum := by decide
  have hdescent : baseEnd_7863789 < baseStart_7863789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863792 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 1, 3, 2]
def baseStart_7863792 : Nat := 118140960795 + 7863792 * 2 ^ 59
def prefixEnd_7863792 : Nat := 4983230072969 + 3 ^ 40 * 7863792 * 2
def baseEnd_7863792 : Nat := 4037905062981202111335085

theorem tailTrace_7863792 : CollatzResearch.WordTrace tailWord_7863792 prefixEnd_7863792 4037905062981202111335085 := by
  unfold tailWord_7863792
  simp only [CollatzResearch.WordTrace]
  refine ⟨143408028563416043797364815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191210704751221391729819753 143408028563416043797364815)
  ·
    refine ⟨215112042845124065696047223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143408028563416043797364815 215112042845124065696047223)
    ·
      refine ⟨322668064267686098544070835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215112042845124065696047223 322668064267686098544070835)
      ·
        refine ⟨484002096401529147816106253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322668064267686098544070835 484002096401529147816106253)
        ·
          refine ⟨181500786150573430431039845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484002096401529147816106253 181500786150573430431039845)
          ·
            refine ⟨34031397403232518205819971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181500786150573430431039845 34031397403232518205819971)
            ·
              refine ⟨51047096104848777308729957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34031397403232518205819971 51047096104848777308729957)
              ·
                refine ⟨9571330519659145745386867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51047096104848777308729957 9571330519659145745386867)
                ·
                  refine ⟨14356995779488718618080301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9571330519659145745386867 14356995779488718618080301)
                  ·
                    refine ⟨5383873417308269481780113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14356995779488718618080301 5383873417308269481780113)
                    ·
                      refine ⟨4037905062981202111335085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383873417308269481780113 4037905062981202111335085)
                      ·
                        rfl

theorem cell23_7863792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 3, 2].length) (baseStart_7863792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863792 prefixEnd_7863792 := by exact prefixLift 7863792
  have htrace : WordTrace (prefixWord ++ tailWord_7863792) baseStart_7863792 baseEnd_7863792 := by
    simpa [prefixWord, tailWord_7863792, baseEnd_7863792] using wordTrace_append hprefix tailTrace_7863792
  have hstable : (prefixWord ++ tailWord_7863792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863792).length < 2 ^ (prefixWord ++ tailWord_7863792).sum := by decide
  have hdescent : baseEnd_7863792 < baseStart_7863792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863912 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7863912 : Nat := 118140960795 + 7863912 * 2 ^ 59
def prefixEnd_7863912 : Nat := 4983230072969 + 3 ^ 40 * 7863912 * 2
def baseEnd_7863912 : Nat := 4037966680659741641834533

theorem tailTrace_7863912 : CollatzResearch.WordTrace tailWord_7863912 prefixEnd_7863912 4037966680659741641834533 := by
  unfold tailWord_7863912
  simp only [CollatzResearch.WordTrace]
  refine ⟨143410216943198674044548995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191213622590931565392731993 143410216943198674044548995)
  ·
    refine ⟨215115325414798011066823493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143410216943198674044548995 215115325414798011066823493)
    ·
      refine ⟨40334123515274627075029405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215115325414798011066823493 40334123515274627075029405)
      ·
        refine ⟨15125296318227985153136027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40334123515274627075029405 15125296318227985153136027)
        ·
          refine ⟨22687944477341977729704041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15125296318227985153136027 22687944477341977729704041)
          ·
            refine ⟨17015958358006483297278031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22687944477341977729704041 17015958358006483297278031)
            ·
              refine ⟨25523937537009724945917047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17015958358006483297278031 25523937537009724945917047)
              ·
                refine ⟨38285906305514587418875571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25523937537009724945917047 38285906305514587418875571)
                ·
                  refine ⟨57428859458271881128313357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38285906305514587418875571 57428859458271881128313357)
                  ·
                    refine ⟨21535822296851955423117509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57428859458271881128313357 21535822296851955423117509)
                    ·
                      refine ⟨4037966680659741641834533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21535822296851955423117509 4037966680659741641834533)
                      ·
                        rfl

theorem cell23_7863912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7863912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863912 prefixEnd_7863912 := by exact prefixLift 7863912
  have htrace : WordTrace (prefixWord ++ tailWord_7863912) baseStart_7863912 baseEnd_7863912 := by
    simpa [prefixWord, tailWord_7863912, baseEnd_7863912] using wordTrace_append hprefix tailTrace_7863912
  have hstable : (prefixWord ++ tailWord_7863912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863912).length < 2 ^ (prefixWord ++ tailWord_7863912).sum := by decide
  have hdescent : baseEnd_7863912 < baseStart_7863912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863990 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7863990 : Nat := 118140960795 + 7863990 * 2 ^ 59
def prefixEnd_7863990 : Nat := 4983230072969 + 3 ^ 40 * 7863990 * 2
def baseEnd_7863990 : Nat := 1346002244050264112219725

theorem tailTrace_7863990 : CollatzResearch.WordTrace tailWord_7863990 prefixEnd_7863990 1346002244050264112219725 := by
  unfold tailWord_7863990
  simp only [CollatzResearch.WordTrace]
  refine ⟨17926454923757172963152339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191215519186743178273624949 17926454923757172963152339)
  ·
    refine ⟨26889682385635759444728509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17926454923757172963152339 26889682385635759444728509)
    ·
      refine ⟨10083630894613409791773191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26889682385635759444728509 10083630894613409791773191)
      ·
        refine ⟨15125446341920114687659787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10083630894613409791773191 15125446341920114687659787)
        ·
          refine ⟨22688169512880172031489681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15125446341920114687659787 22688169512880172031489681)
          ·
            refine ⟨17016127134660129023617261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22688169512880172031489681 17016127134660129023617261)
            ·
              refine ⟨6381047675497548383856473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17016127134660129023617261 6381047675497548383856473)
              ·
                refine ⟨4785785756623161287892355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6381047675497548383856473 4785785756623161287892355)
                ·
                  refine ⟨7178678634934741931838533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785785756623161287892355 7178678634934741931838533)
                  ·
                    refine ⟨1346002244050264112219725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7178678634934741931838533 1346002244050264112219725)
                    ·
                      rfl

theorem cell23_7863990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7863990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863990 prefixEnd_7863990 := by exact prefixLift 7863990
  have htrace : WordTrace (prefixWord ++ tailWord_7863990) baseStart_7863990 baseEnd_7863990 := by
    simpa [prefixWord, tailWord_7863990, baseEnd_7863990] using wordTrace_append hprefix tailTrace_7863990
  have hstable : (prefixWord ++ tailWord_7863990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863990).length < 2 ^ (prefixWord ++ tailWord_7863990).sum := by decide
  have hdescent : baseEnd_7863990 < baseStart_7863990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863996 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7863996 : Nat := 118140960795 + 7863996 * 2 ^ 59
def prefixEnd_7863996 : Nat := 4983230072969 + 3 ^ 40 * 7863996 * 2
def baseEnd_7863996 : Nat := 4038009813034719313184147

theorem tailTrace_7863996 : CollatzResearch.WordTrace tailWord_7863996 prefixEnd_7863996 4038009813034719313184147 := by
  unfold tailWord_7863996
  simp only [CollatzResearch.WordTrace]
  refine ⟨143411748809046515217577921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191215665078728686956770561 143411748809046515217577921)
  ·
    refine ⟨107558811606784886413183441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143411748809046515217577921 107558811606784886413183441)
    ·
      refine ⟨80669108705088664809887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107558811606784886413183441 80669108705088664809887581)
      ·
        refine ⟨30250915764408249303707843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80669108705088664809887581 30250915764408249303707843)
        ·
          refine ⟨45376373646612373955561765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30250915764408249303707843 45376373646612373955561765)
          ·
            refine ⟨8508070058739820116667831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45376373646612373955561765 8508070058739820116667831)
            ·
              refine ⟨12762105088109730175001747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8508070058739820116667831 12762105088109730175001747)
              ·
                refine ⟨19143157632164595262502621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12762105088109730175001747 19143157632164595262502621)
                ·
                  refine ⟨7178684112061723223438483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19143157632164595262502621 7178684112061723223438483)
                  ·
                    refine ⟨10768026168092584835157725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178684112061723223438483 10768026168092584835157725)
                    ·
                      refine ⟨4038009813034719313184147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10768026168092584835157725 4038009813034719313184147)
                      ·
                        rfl

theorem cell23_7863996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7863996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863996 prefixEnd_7863996 := by exact prefixLift 7863996
  have htrace : WordTrace (prefixWord ++ tailWord_7863996) baseStart_7863996 baseEnd_7863996 := by
    simpa [prefixWord, tailWord_7863996, baseEnd_7863996] using wordTrace_append hprefix tailTrace_7863996
  have hstable : (prefixWord ++ tailWord_7863996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863996).length < 2 ^ (prefixWord ++ tailWord_7863996).sum := by decide
  have hdescent : baseEnd_7863996 < baseStart_7863996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864015 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_7864015 : Nat := 118140960795 + 7864015 * 2 ^ 59
def prefixEnd_7864015 : Nat := 4983230072969 + 3 ^ 40 * 7864015 * 2
def baseEnd_7864015 : Nat := 4038019569167154738846559

theorem tailTrace_7864015 : CollatzResearch.WordTrace tailWord_7864015 prefixEnd_7864015 4038019569167154738846559 := by
  unfold tailWord_7864015
  simp only [CollatzResearch.WordTrace]
  refine ⟨286824190605024196680097499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191216127070016131120064999 286824190605024196680097499)
  ·
    refine ⟨430236285907536295020146249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286824190605024196680097499 430236285907536295020146249)
    ·
      refine ⟨322677214430652221265109687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430236285907536295020146249 322677214430652221265109687)
      ·
        refine ⟨484015821645978331897664531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322677214430652221265109687 484015821645978331897664531)
        ·
          refine ⟨726023732468967497846496797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484015821645978331897664531 726023732468967497846496797)
          ·
            refine ⟨272258899675862811692436299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726023732468967497846496797 272258899675862811692436299)
            ·
              refine ⟨408388349513794217538654449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272258899675862811692436299 408388349513794217538654449)
              ·
                refine ⟨306291262135345663153990837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408388349513794217538654449 306291262135345663153990837)
                ·
                  refine ⟨28714805825188655920686641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306291262135345663153990837 28714805825188655920686641)
                  ·
                    refine ⟨21536104368891491940514981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28714805825188655920686641 21536104368891491940514981)
                    ·
                      refine ⟨4038019569167154738846559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21536104368891491940514981 4038019569167154738846559)
                      ·
                        rfl

theorem cell23_7864015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_7864015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864015 prefixEnd_7864015 := by exact prefixLift 7864015
  have htrace : WordTrace (prefixWord ++ tailWord_7864015) baseStart_7864015 baseEnd_7864015 := by
    simpa [prefixWord, tailWord_7864015, baseEnd_7864015] using wordTrace_append hprefix tailTrace_7864015
  have hstable : (prefixWord ++ tailWord_7864015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864015).length < 2 ^ (prefixWord ++ tailWord_7864015).sum := by decide
  have hdescent : baseEnd_7864015 < baseStart_7864015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864025 : List Nat := [1, 2, 1, 2, 3, 3, 2, 9]
def baseStart_7864025 : Nat := 118140960795 + 7864025 * 2 ^ 59
def prefixEnd_7864025 : Nat := 4983230072969 + 3 ^ 40 * 7864025 * 2
def baseEnd_7864025 : Nat := 149556470517544433323019

theorem tailTrace_7864025 : CollatzResearch.WordTrace tailWord_7864025 prefixEnd_7864025 149556470517544433323019 := by
  unfold tailWord_7864025
  simp only [CollatzResearch.WordTrace]
  refine ⟨286824555334987968387961529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191216370223325312258641019 286824555334987968387961529)
  ·
    refine ⟨215118416501240976290971147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286824555334987968387961529 215118416501240976290971147)
    ·
      refine ⟨322677624751861464436456721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215118416501240976290971147 322677624751861464436456721)
      ·
        refine ⟨242008218563896098327342541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322677624751861464436456721 242008218563896098327342541)
        ·
          refine ⟨90753081961461036872753453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242008218563896098327342541 90753081961461036872753453)
          ·
            refine ⟨34032405735547888827282545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90753081961461036872753453 34032405735547888827282545)
            ·
              refine ⟨25524304301660916620461909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34032405735547888827282545 25524304301660916620461909)
              ·
                refine ⟨149556470517544433323019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25524304301660916620461909 149556470517544433323019)
                ·
                  rfl

theorem cell23_7864025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 9].length) (baseStart_7864025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864025 prefixEnd_7864025 := by exact prefixLift 7864025
  have htrace : WordTrace (prefixWord ++ tailWord_7864025) baseStart_7864025 baseEnd_7864025 := by
    simpa [prefixWord, tailWord_7864025, baseEnd_7864025] using wordTrace_append hprefix tailTrace_7864025
  have hstable : (prefixWord ++ tailWord_7864025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864025).length < 2 ^ (prefixWord ++ tailWord_7864025).sum := by decide
  have hdescent : baseEnd_7864025 < baseStart_7864025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864055 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 2, 7]
def baseStart_7864055 : Nat := 118140960795 + 7864055 * 2 ^ 59
def prefixEnd_7864055 : Nat := 4983230072969 + 3 ^ 40 * 7864055 * 2
def baseEnd_7864055 : Nat := 1346013369464444860782125

theorem tailTrace_7864055 : CollatzResearch.WordTrace tailWord_7864055 prefixEnd_7864055 1346013369464444860782125 := by
  unfold tailWord_7864055
  simp only [CollatzResearch.WordTrace]
  refine ⟨286825649524879283511553619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191217099683252855674369079 286825649524879283511553619)
  ·
    refine ⟨430238474287318925267330429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286825649524879283511553619 430238474287318925267330429)
    ·
      refine ⟨161339427857744596975248911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430238474287318925267330429 161339427857744596975248911)
      ·
        refine ⟨242009141786616895462873367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161339427857744596975248911 242009141786616895462873367)
        ·
          refine ⟨363013712679925343194310051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242009141786616895462873367 363013712679925343194310051)
          ·
            refine ⟨544520569019888014791465077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363013712679925343194310051 544520569019888014791465077)
            ·
              refine ⟨51048803345614501386699851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 544520569019888014791465077 51048803345614501386699851)
              ·
                refine ⟨76573205018421752080049777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51048803345614501386699851 76573205018421752080049777)
                ·
                  refine ⟨57429903763816314060037333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76573205018421752080049777 57429903763816314060037333)
                  ·
                    refine ⟨1346013369464444860782125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57429903763816314060037333 1346013369464444860782125)
                    ·
                      rfl

theorem cell23_7864055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_7864055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864055 prefixEnd_7864055 := by exact prefixLift 7864055
  have htrace : WordTrace (prefixWord ++ tailWord_7864055) baseStart_7864055 baseEnd_7864055 := by
    simpa [prefixWord, tailWord_7864055, baseEnd_7864055] using wordTrace_append hprefix tailTrace_7864055
  have hstable : (prefixWord ++ tailWord_7864055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864055).length < 2 ^ (prefixWord ++ tailWord_7864055).sum := by decide
  have hdescent : baseEnd_7864055 < baseStart_7864055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864096 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7864096 : Nat := 118140960795 + 7864096 * 2 ^ 59
def prefixEnd_7864096 : Nat := 4983230072969 + 3 ^ 40 * 7864096 * 2
def baseEnd_7864096 : Nat := 4038061161100168921933687

theorem tailTrace_7864096 : CollatzResearch.WordTrace tailWord_7864096 prefixEnd_7864096 4038061161100168921933687 := by
  unfold tailWord_7864096
  simp only [CollatzResearch.WordTrace]
  refine ⟨143413572458865373756898071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191218096611820498342530761 143413572458865373756898071)
  ·
    refine ⟨215120358688298060635347107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143413572458865373756898071 215120358688298060635347107)
    ·
      refine ⟨322680538032447090953020661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215120358688298060635347107 322680538032447090953020661)
      ·
        refine ⟨30251300440541914776845687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322680538032447090953020661 30251300440541914776845687)
        ·
          refine ⟨45376950660812872165268531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30251300440541914776845687 45376950660812872165268531)
          ·
            refine ⟨68065425991219308247902797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45376950660812872165268531 68065425991219308247902797)
            ·
              refine ⟨25524534746707240592963549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68065425991219308247902797 25524534746707240592963549)
              ·
                refine ⟨9571700530015215222361331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25524534746707240592963549 9571700530015215222361331)
                ·
                  refine ⟨14357550795022822833541997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9571700530015215222361331 14357550795022822833541997)
                  ·
                    refine ⟨5384081548133558562578249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14357550795022822833541997 5384081548133558562578249)
                    ·
                      refine ⟨4038061161100168921933687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384081548133558562578249 4038061161100168921933687)
                      ·
                        rfl

theorem cell23_7864096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7864096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864096 prefixEnd_7864096 := by exact prefixLift 7864096
  have htrace : WordTrace (prefixWord ++ tailWord_7864096) baseStart_7864096 baseEnd_7864096 := by
    simpa [prefixWord, tailWord_7864096, baseEnd_7864096] using wordTrace_append hprefix tailTrace_7864096
  have hstable : (prefixWord ++ tailWord_7864096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864096).length < 2 ^ (prefixWord ++ tailWord_7864096).sum := by decide
  have hdescent : baseEnd_7864096 < baseStart_7864096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_7864105 : Nat := 118140960795 + 7864105 * 2 ^ 59
def prefixEnd_7864105 : Nat := 4983230072969 + 3 ^ 40 * 7864105 * 2
def baseEnd_7864105 : Nat := 4038065782426059386721145

theorem tailTrace_7864105 : CollatzResearch.WordTrace tailWord_7864105 prefixEnd_7864105 4038065782426059386721145 := by
  unfold tailWord_7864105
  simp only [CollatzResearch.WordTrace]
  refine ⟨286827473174698142050873769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191218315449798761367249179 286827473174698142050873769)
  ·
    refine ⟨215120604881023606538155327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286827473174698142050873769 215120604881023606538155327)
    ·
      refine ⟨322680907321535409807232991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215120604881023606538155327 322680907321535409807232991)
      ·
        refine ⟨484021360982303114710849487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322680907321535409807232991 484021360982303114710849487)
        ·
          refine ⟨726032041473454672066274231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484021360982303114710849487 726032041473454672066274231)
          ·
            refine ⟨1089048062210182008099411347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726032041473454672066274231 1089048062210182008099411347)
            ·
              refine ⟨1633572093315273012149117021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089048062210182008099411347 1633572093315273012149117021)
              ·
                refine ⟨612589534993227379555918883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1633572093315273012149117021 612589534993227379555918883)
                ·
                  refine ⟨918884302489841069333878325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612589534993227379555918883 918884302489841069333878325)
                  ·
                    refine ⟨86145403358422600250051093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 918884302489841069333878325 86145403358422600250051093)
                    ·
                      refine ⟨4038065782426059386721145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86145403358422600250051093 4038065782426059386721145)
                      ·
                        rfl

theorem cell23_7864105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_7864105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864105 prefixEnd_7864105 := by exact prefixLift 7864105
  have htrace : WordTrace (prefixWord ++ tailWord_7864105) baseStart_7864105 baseEnd_7864105 := by
    simpa [prefixWord, tailWord_7864105, baseEnd_7864105] using wordTrace_append hprefix tailTrace_7864105
  have hstable : (prefixWord ++ tailWord_7864105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864105).length < 2 ^ (prefixWord ++ tailWord_7864105).sum := by decide
  have hdescent : baseEnd_7864105 < baseStart_7864105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864172 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_7864172 : Nat := 118140960795 + 7864172 * 2 ^ 59
def prefixEnd_7864172 : Nat := 4983230072969 + 3 ^ 40 * 7864172 * 2
def baseEnd_7864172 : Nat := 4038100185629910624583337

theorem tailTrace_7864172 : CollatzResearch.WordTrace tailWord_7864172 prefixEnd_7864172 4038100185629910624583337 := by
  unfold tailWord_7864172
  simp only [CollatzResearch.WordTrace]
  refine ⟨143414958432727706246781385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191219944576970274995708513 143414958432727706246781385)
  ·
    refine ⟨107561218824545779685086039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143414958432727706246781385 107561218824545779685086039)
    ·
      refine ⟨161341828236818669527629059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107561218824545779685086039 161341828236818669527629059)
      ·
        refine ⟨242012742355228004291443589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161341828236818669527629059 242012742355228004291443589)
        ·
          refine ⟨45377389191605250804645673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242012742355228004291443589 45377389191605250804645673)
          ·
            refine ⟨34033041893703938103484255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45377389191605250804645673 34033041893703938103484255)
            ·
              refine ⟨51049562840555907155226383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34033041893703938103484255 51049562840555907155226383)
              ·
                refine ⟨76574344260833860732839575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51049562840555907155226383 76574344260833860732839575)
                ·
                  refine ⟨114861516391250791099259363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76574344260833860732839575 114861516391250791099259363)
                  ·
                    refine ⟨172292274586876186648889045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114861516391250791099259363 172292274586876186648889045)
                    ·
                      refine ⟨4038100185629910624583337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172292274586876186648889045 4038100185629910624583337)
                      ·
                        rfl

theorem cell23_7864172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_7864172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864172 prefixEnd_7864172 := by exact prefixLift 7864172
  have htrace : WordTrace (prefixWord ++ tailWord_7864172) baseStart_7864172 baseEnd_7864172 := by
    simpa [prefixWord, tailWord_7864172, baseEnd_7864172] using wordTrace_append hprefix tailTrace_7864172
  have hstable : (prefixWord ++ tailWord_7864172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864172).length < 2 ^ (prefixWord ++ tailWord_7864172).sum := by decide
  have hdescent : baseEnd_7864172 < baseStart_7864172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864253 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_7864253 : Nat := 118140960795 + 7864253 * 2 ^ 59
def prefixEnd_7864253 : Nat := 4983230072969 + 3 ^ 40 * 7864253 * 2
def baseEnd_7864253 : Nat := 4038141777562924807670465

theorem tailTrace_7864253 : CollatzResearch.WordTrace tailWord_7864253 prefixEnd_7864253 4038141777562924807670465 := by
  unfold tailWord_7864253
  simp only [CollatzResearch.WordTrace]
  refine ⟨286832871178161963327261413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191221914118774642218174275 286832871178161963327261413)
  ·
    refine ⟨53781163345905368123861515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286832871178161963327261413 53781163345905368123861515)
    ·
      refine ⟨80671745018858052185792273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53781163345905368123861515 80671745018858052185792273)
      ·
        refine ⟨60503808764143539139344205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80671745018858052185792273 60503808764143539139344205)
        ·
          refine ⟨22688928286553827177254077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60503808764143539139344205 22688928286553827177254077)
          ·
            refine ⟨8508348107457685191470279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22688928286553827177254077 8508348107457685191470279)
            ·
              refine ⟨12762522161186527787205419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8508348107457685191470279 12762522161186527787205419)
              ·
                refine ⟨19143783241779791680808129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12762522161186527787205419 19143783241779791680808129)
                ·
                  refine ⟨14357837431334843760606097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19143783241779791680808129 14357837431334843760606097)
                  ·
                    refine ⟨10768378073501132820454573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14357837431334843760606097 10768378073501132820454573)
                    ·
                      refine ⟨4038141777562924807670465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10768378073501132820454573 4038141777562924807670465)
                      ·
                        rfl

theorem cell23_7864253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_7864253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864253 prefixEnd_7864253 := by exact prefixLift 7864253
  have htrace : WordTrace (prefixWord ++ tailWord_7864253) baseStart_7864253 baseEnd_7864253 := by
    simpa [prefixWord, tailWord_7864253, baseEnd_7864253] using wordTrace_append hprefix tailTrace_7864253
  have hstable : (prefixWord ++ tailWord_7864253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864253).length < 2 ^ (prefixWord ++ tailWord_7864253).sum := by decide
  have hdescent : baseEnd_7864253 < baseStart_7864253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864289 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7864289 : Nat := 118140960795 + 7864289 * 2 ^ 59
def prefixEnd_7864289 : Nat := 4983230072969 + 3 ^ 40 * 7864289 * 2
def baseEnd_7864289 : Nat := 4038160262866486666820299

theorem tailTrace_7864289 : CollatzResearch.WordTrace tailWord_7864289 prefixEnd_7864289 4038160262866486666820299 := by
  unfold tailWord_7864289
  simp only [CollatzResearch.WordTrace]
  refine ⟨286834184206031541475571921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191222789470687694317047947 286834184206031541475571921)
  ·
    refine ⟨215125638154523656106678941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286834184206031541475571921 215125638154523656106678941)
    ·
      refine ⟨80672114307946371040004603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215125638154523656106678941 80672114307946371040004603)
      ·
        refine ⟨121008171461919556560006905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80672114307946371040004603 121008171461919556560006905)
        ·
          refine ⟨90756128596439667420005179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121008171461919556560006905 90756128596439667420005179)
          ·
            refine ⟨136134192894659501130007769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90756128596439667420005179 136134192894659501130007769)
            ·
              refine ⟨102100644670994625847505827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136134192894659501130007769 102100644670994625847505827)
              ·
                refine ⟨153150967006491938771258741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102100644670994625847505827 153150967006491938771258741)
                ·
                  refine ⟨14357903156858619259805507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153150967006491938771258741 14357903156858619259805507)
                  ·
                    refine ⟨21536854735287928889708261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14357903156858619259805507 21536854735287928889708261)
                    ·
                      refine ⟨4038160262866486666820299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21536854735287928889708261 4038160262866486666820299)
                      ·
                        rfl

theorem cell23_7864289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7864289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864289 prefixEnd_7864289 := by exact prefixLift 7864289
  have htrace : WordTrace (prefixWord ++ tailWord_7864289) baseStart_7864289 baseEnd_7864289 := by
    simpa [prefixWord, tailWord_7864289, baseEnd_7864289] using wordTrace_append hprefix tailTrace_7864289
  have hstable : (prefixWord ++ tailWord_7864289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864289).length < 2 ^ (prefixWord ++ tailWord_7864289).sum := by decide
  have hdescent : baseEnd_7864289 < baseStart_7864289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864290 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_7864290 : Nat := 118140960795 + 7864290 * 2 ^ 59
def prefixEnd_7864290 : Nat := 4983230072969 + 3 ^ 40 * 7864290 * 2
def baseEnd_7864290 : Nat := 448684530705237906989755

theorem tailTrace_7864290 : CollatzResearch.WordTrace tailWord_7864290 prefixEnd_7864290 448684530705237906989755 := by
  unfold tailWord_7864290
  simp only [CollatzResearch.WordTrace]
  refine ⟨71708555169756979661589581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191222813786018612430905549 71708555169756979661589581)
  ·
    refine ⟨26890708188658867373096093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71708555169756979661589581 26890708188658867373096093)
    ·
      refine ⟨10084015570747075264911035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26890708188658867373096093 10084015570747075264911035)
      ·
        refine ⟨15126023356120612897366553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10084015570747075264911035 15126023356120612897366553)
        ·
          refine ⟨11344517517090459673024915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15126023356120612897366553 11344517517090459673024915)
          ·
            refine ⟨17016776275635689509537373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11344517517090459673024915 17016776275635689509537373)
            ·
              refine ⟨6381291103363383566076515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17016776275635689509537373 6381291103363383566076515)
              ·
                refine ⟨9571936655045075349114773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381291103363383566076515 9571936655045075349114773)
                ·
                  refine ⟨448684530705237906989755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9571936655045075349114773 448684530705237906989755)
                  ·
                    rfl

theorem cell23_7864290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_7864290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864290 prefixEnd_7864290 := by exact prefixLift 7864290
  have htrace : WordTrace (prefixWord ++ tailWord_7864290) baseStart_7864290 baseEnd_7864290 := by
    simpa [prefixWord, tailWord_7864290, baseEnd_7864290] using wordTrace_append hprefix tailTrace_7864290
  have hstable : (prefixWord ++ tailWord_7864290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864290).length < 2 ^ (prefixWord ++ tailWord_7864290).sum := by decide
  have hdescent : baseEnd_7864290 < baseStart_7864290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864319 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_7864319 : Nat := 118140960795 + 7864319 * 2 ^ 59
def prefixEnd_7864319 : Nat := 4983230072969 + 3 ^ 40 * 7864319 * 2
def baseEnd_7864319 : Nat := 4038175667286121549445161

theorem tailTrace_7864319 : CollatzResearch.WordTrace tailWord_7864319 prefixEnd_7864319 4038175667286121549445161 := by
  unfold tailWord_7864319
  simp only [CollatzResearch.WordTrace]
  refine ⟨286835278395922856599164011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191223518930615237732776007 286835278395922856599164011)
  ·
    refine ⟨430252917593884284898746017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286835278395922856599164011 430252917593884284898746017)
    ·
      refine ⟨322689688195413213674059513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430252917593884284898746017 322689688195413213674059513)
      ·
        refine ⟨242017266146559910255544635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322689688195413213674059513 242017266146559910255544635)
        ·
          refine ⟨363025899219839865383316953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242017266146559910255544635 363025899219839865383316953)
          ·
            refine ⟨272269424414879899037487715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363025899219839865383316953 272269424414879899037487715)
            ·
              refine ⟨408404136622319848556231573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272269424414879899037487715 408404136622319848556231573)
              ·
                refine ⟨19143943904171242901073355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408404136622319848556231573 19143943904171242901073355)
                ·
                  refine ⟨28715915856256864351610033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19143943904171242901073355 28715915856256864351610033)
                  ·
                    refine ⟨21536936892192648263707525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28715915856256864351610033 21536936892192648263707525)
                    ·
                      refine ⟨4038175667286121549445161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21536936892192648263707525 4038175667286121549445161)
                      ·
                        rfl

theorem cell23_7864319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_7864319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864319 prefixEnd_7864319 := by exact prefixLift 7864319
  have htrace : WordTrace (prefixWord ++ tailWord_7864319) baseStart_7864319 baseEnd_7864319 := by
    simpa [prefixWord, tailWord_7864319, baseEnd_7864319] using wordTrace_append hprefix tailTrace_7864319
  have hstable : (prefixWord ++ tailWord_7864319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864319).length < 2 ^ (prefixWord ++ tailWord_7864319).sum := by decide
  have hdescent : baseEnd_7864319 < baseStart_7864319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864360 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7864360 : Nat := 118140960795 + 7864360 * 2 ^ 59
def prefixEnd_7864360 : Nat := 4983230072969 + 3 ^ 40 * 7864360 * 2
def baseEnd_7864360 : Nat := 4038196719992955889032473

theorem tailTrace_7864360 : CollatzResearch.WordTrace tailWord_7864360 prefixEnd_7864360 4038196719992955889032473 := by
  unfold tailWord_7864360
  simp only [CollatzResearch.WordTrace]
  refine ⟨143418386894387160300703267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191224515859182880400937689 143418386894387160300703267)
  ·
    refine ⟨215127580341580740451054901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143418386894387160300703267 215127580341580740451054901)
    ·
      refine ⟨20168210657023194417286397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215127580341580740451054901 20168210657023194417286397)
      ·
        refine ⟨7563078996383697906482399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20168210657023194417286397 7563078996383697906482399)
        ·
          refine ⟨11344618494575546859723599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563078996383697906482399 11344618494575546859723599)
          ·
            refine ⟨17016927741863320289585399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11344618494575546859723599 17016927741863320289585399)
            ·
              refine ⟨25525391612794980434378099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17016927741863320289585399 25525391612794980434378099)
              ·
                refine ⟨38288087419192470651567149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25525391612794980434378099 38288087419192470651567149)
                ·
                  refine ⟨14358032782197176494337681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38288087419192470651567149 14358032782197176494337681)
                  ·
                    refine ⟨10768524586647882370753261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14358032782197176494337681 10768524586647882370753261)
                    ·
                      refine ⟨4038196719992955889032473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10768524586647882370753261 4038196719992955889032473)
                      ·
                        rfl

theorem cell23_7864360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7864360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864360 prefixEnd_7864360 := by exact prefixLift 7864360
  have htrace : WordTrace (prefixWord ++ tailWord_7864360) baseStart_7864360 baseEnd_7864360 := by
    simpa [prefixWord, tailWord_7864360, baseEnd_7864360] using wordTrace_append hprefix tailTrace_7864360
  have hstable : (prefixWord ++ tailWord_7864360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864360).length < 2 ^ (prefixWord ++ tailWord_7864360).sum := by decide
  have hdescent : baseEnd_7864360 < baseStart_7864360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864383 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 1, 3, 2]
def baseStart_7864383 : Nat := 118140960795 + 7864383 * 2 ^ 59
def prefixEnd_7864383 : Nat := 4983230072969 + 3 ^ 40 * 7864383 * 2
def baseEnd_7864383 : Nat := 4038208530048009299044867

theorem tailTrace_7864383 : CollatzResearch.WordTrace tailWord_7864383 prefixEnd_7864383 4038208530048009299044867 := by
  unfold tailWord_7864383
  simp only [CollatzResearch.WordTrace]
  refine ⟨286837612667690995529493803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191225075111793997019662535 286837612667690995529493803)
  ·
    refine ⟨430256419001536493294240705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286837612667690995529493803 430256419001536493294240705)
    ·
      refine ⟨322692314251152369970680529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430256419001536493294240705 322692314251152369970680529)
      ·
        refine ⟨242019235688364277478010397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322692314251152369970680529 242019235688364277478010397)
        ·
          refine ⟨90757213383136604054253899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242019235688364277478010397 90757213383136604054253899)
          ·
            refine ⟨136135820074704906081380849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90757213383136604054253899 136135820074704906081380849)
            ·
              refine ⟨102101865056028679561035637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136135820074704906081380849 102101865056028679561035637)
              ·
                refine ⟨9572049849002688708847091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102101865056028679561035637 9572049849002688708847091)
                ·
                  refine ⟨14358074773504033063270637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9572049849002688708847091 14358074773504033063270637)
                  ·
                    refine ⟨5384278040064012398726489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14358074773504033063270637 5384278040064012398726489)
                    ·
                      refine ⟨4038208530048009299044867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384278040064012398726489 4038208530048009299044867)
                      ·
                        rfl

theorem cell23_7864383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_7864383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864383 prefixEnd_7864383 := by exact prefixLift 7864383
  have htrace : WordTrace (prefixWord ++ tailWord_7864383) baseStart_7864383 baseEnd_7864383 := by
    simpa [prefixWord, tailWord_7864383, baseEnd_7864383] using wordTrace_append hprefix tailTrace_7864383
  have hstable : (prefixWord ++ tailWord_7864383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864383).length < 2 ^ (prefixWord ++ tailWord_7864383).sum := by decide
  have hdescent : baseEnd_7864383 < baseStart_7864383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864389 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_7864389 : Nat := 118140960795 + 7864389 * 2 ^ 59
def prefixEnd_7864389 : Nat := 4983230072969 + 3 ^ 40 * 7864389 * 2
def baseEnd_7864389 : Nat := 1346070536977312091856613

theorem tailTrace_7864389 : CollatzResearch.WordTrace tailWord_7864389 prefixEnd_7864389 1346070536977312091856613 := by
  unfold tailWord_7864389
  simp only [CollatzResearch.WordTrace]
  refine ⟨286837831505669258554212221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191225221003779505702808147 286837831505669258554212221)
  ·
    refine ⟨107564186814625971957829583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286837831505669258554212221 107564186814625971957829583)
    ·
      refine ⟨161346280221938957936744375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107564186814625971957829583 161346280221938957936744375)
      ·
        refine ⟨242019420332908436905116563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161346280221938957936744375 242019420332908436905116563)
        ·
          refine ⟨363029130499362655357674845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242019420332908436905116563 363029130499362655357674845)
          ·
            refine ⟨136135923937260995759128067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363029130499362655357674845 136135923937260995759128067)
            ·
              refine ⟨204203885905891493638692101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136135923937260995759128067 204203885905891493638692101)
              ·
                refine ⟨38288228607354655057254769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204203885905891493638692101 38288228607354655057254769)
                ·
                  refine ⟨28716171455515991292941077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38288228607354655057254769 28716171455515991292941077)
                  ·
                    refine ⟨1346070536977312091856613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28716171455515991292941077 1346070536977312091856613)
                    ·
                      rfl

theorem cell23_7864389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_7864389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864389 prefixEnd_7864389 := by exact prefixLift 7864389
  have htrace : WordTrace (prefixWord ++ tailWord_7864389) baseStart_7864389 baseEnd_7864389 := by
    simpa [prefixWord, tailWord_7864389, baseEnd_7864389] using wordTrace_append hprefix tailTrace_7864389
  have hstable : (prefixWord ++ tailWord_7864389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864389).length < 2 ^ (prefixWord ++ tailWord_7864389).sum := by decide
  have hdescent : baseEnd_7864389 < baseStart_7864389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864419 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 9]
def baseStart_7864419 : Nat := 118140960795 + 7864419 * 2 ^ 59
def prefixEnd_7864419 : Nat := 4983230072969 + 3 ^ 40 * 7864419 * 2
def baseEnd_7864419 : Nat := 448691890594619017577189

theorem tailTrace_7864419 : CollatzResearch.WordTrace tailWord_7864419 prefixEnd_7864419 448691890594619017577189 := by
  unfold tailWord_7864419
  simp only [CollatzResearch.WordTrace]
  refine ⟨286838925695560573677804311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191225950463707049118536207 286838925695560573677804311)
  ·
    refine ⟨430258388543340860516706467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286838925695560573677804311 430258388543340860516706467)
    ·
      refine ⟨645387582815011290775059701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430258388543340860516706467 645387582815011290775059701)
      ·
        refine ⟨60505085888907308510161847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 645387582815011290775059701 60505085888907308510161847)
        ·
          refine ⟨90757628833360962765242771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60505085888907308510161847 90757628833360962765242771)
          ·
            refine ⟨136136443250041444147864157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90757628833360962765242771 136136443250041444147864157)
            ·
              refine ⟨51051166218765541555449059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136136443250041444147864157 51051166218765541555449059)
              ·
                refine ⟨76576749328148312333173589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51051166218765541555449059 76576749328148312333173589)
                ·
                  refine ⟨448691890594619017577189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76576749328148312333173589 448691890594619017577189)
                  ·
                    rfl

theorem cell23_7864419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 9].length) (baseStart_7864419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864419 prefixEnd_7864419 := by exact prefixLift 7864419
  have htrace : WordTrace (prefixWord ++ tailWord_7864419) baseStart_7864419 baseEnd_7864419 := by
    simpa [prefixWord, tailWord_7864419, baseEnd_7864419] using wordTrace_append hprefix tailTrace_7864419
  have hstable : (prefixWord ++ tailWord_7864419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864419).length < 2 ^ (prefixWord ++ tailWord_7864419).sum := by decide
  have hdescent : baseEnd_7864419 < baseStart_7864419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864430 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_7864430 : Nat := 118140960795 + 7864430 * 2 ^ 59
def prefixEnd_7864430 : Nat := 4983230072969 + 3 ^ 40 * 7864430 * 2
def baseEnd_7864430 : Nat := 4038232663638770615157151

theorem tailTrace_7864430 : CollatzResearch.WordTrace tailWord_7864430 prefixEnd_7864430 4038232663638770615157151 := by
  unfold tailWord_7864430
  simp only [CollatzResearch.WordTrace]
  refine ⟨35854915862315090319556843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191226217932347148370969829 35854915862315090319556843)
  ·
    refine ⟨53782373793472635479335265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35854915862315090319556843 53782373793472635479335265)
    ·
      refine ⟨40336780345104476609501449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53782373793472635479335265 40336780345104476609501449)
      ·
        refine ⟨30252585258828357457126087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40336780345104476609501449 30252585258828357457126087)
        ·
          refine ⟨45378877888242536185689131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30252585258828357457126087 45378877888242536185689131)
          ·
            refine ⟨68068316832363804278533697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45378877888242536185689131 68068316832363804278533697)
            ·
              refine ⟨51051237624272853208900273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68068316832363804278533697 51051237624272853208900273)
              ·
                refine ⟨38288428218204639906675205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51051237624272853208900273 38288428218204639906675205)
                ·
                  refine ⟨7179080290913369982501601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38288428218204639906675205 7179080290913369982501601)
                  ·
                    refine ⟨5384310218185027486876201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179080290913369982501601 5384310218185027486876201)
                    ·
                      refine ⟨4038232663638770615157151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384310218185027486876201 4038232663638770615157151)
                      ·
                        rfl

theorem cell23_7864430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_7864430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864430 prefixEnd_7864430 := by exact prefixLift 7864430
  have htrace : WordTrace (prefixWord ++ tailWord_7864430) baseStart_7864430 baseEnd_7864430 := by
    simpa [prefixWord, tailWord_7864430, baseEnd_7864430] using wordTrace_append hprefix tailTrace_7864430
  have hstable : (prefixWord ++ tailWord_7864430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864430).length < 2 ^ (prefixWord ++ tailWord_7864430).sum := by decide
  have hdescent : baseEnd_7864430 < baseStart_7864430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864453 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 5]
def baseStart_7864453 : Nat := 118140960795 + 7864453 * 2 ^ 59
def prefixEnd_7864453 : Nat := 4983230072969 + 3 ^ 40 * 7864453 * 2
def baseEnd_7864453 : Nat := 448693830410424891685505

theorem tailTrace_7864453 : CollatzResearch.WordTrace tailWord_7864453 prefixEnd_7864453 448693830410424891685505 := by
  unfold tailWord_7864453
  simp only [CollatzResearch.WordTrace]
  refine ⟨286840165777437397484542013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191226777184958264989694675 286840165777437397484542013)
  ·
    refine ⟨107565062166539024056703255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286840165777437397484542013 107565062166539024056703255)
    ·
      refine ⟨161347593249808536085054883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107565062166539024056703255 161347593249808536085054883)
      ·
        refine ⟨242021389874712804127582325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161347593249808536085054883 242021389874712804127582325)
        ·
          refine ⟨22689505300754325386960843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242021389874712804127582325 22689505300754325386960843)
          ·
            refine ⟨34034257951131488080441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22689505300754325386960843 34034257951131488080441265)
            ·
              refine ⟨25525693463348616060330949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34034257951131488080441265 25525693463348616060330949)
              ·
                refine ⟨4786067524377865511312053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25525693463348616060330949 4786067524377865511312053)
                ·
                  refine ⟨448693830410424891685505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786067524377865511312053 448693830410424891685505)
                  ·
                    rfl

theorem cell23_7864453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_7864453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864453 prefixEnd_7864453 := by exact prefixLift 7864453
  have htrace : WordTrace (prefixWord ++ tailWord_7864453) baseStart_7864453 baseEnd_7864453 := by
    simpa [prefixWord, tailWord_7864453, baseEnd_7864453] using wordTrace_append hprefix tailTrace_7864453
  have hstable : (prefixWord ++ tailWord_7864453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864453).length < 2 ^ (prefixWord ++ tailWord_7864453).sum := by decide
  have hdescent : baseEnd_7864453 < baseStart_7864453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864466 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_7864466 : Nat := 118140960795 + 7864466 * 2 ^ 59
def prefixEnd_7864466 : Nat := 4983230072969 + 3 ^ 40 * 7864466 * 2
def baseEnd_7864466 : Nat := 1346083716314110824768995

theorem tailTrace_7864466 : CollatzResearch.WordTrace tailWord_7864466 prefixEnd_7864466 1346083716314110824768995 := by
  unfold tailWord_7864466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71710159981597575176191313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191227093284260200469843501 71710159981597575176191313)
  ·
    refine ⟨53782619986198181382143485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71710159981597575176191313 53782619986198181382143485)
    ·
      refine ⟨20168482494824318018303807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53782619986198181382143485 20168482494824318018303807)
      ·
        refine ⟨30252723742236477027455711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20168482494824318018303807 30252723742236477027455711)
        ·
          refine ⟨45379085613354715541183567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30252723742236477027455711 45379085613354715541183567)
          ·
            refine ⟨68068628420032073311775351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45379085613354715541183567 68068628420032073311775351)
            ·
              refine ⟨102102942630048109967663027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68068628420032073311775351 102102942630048109967663027)
              ·
                refine ⟨153154413945072164951494541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102102942630048109967663027 153154413945072164951494541)
                ·
                  refine ⟨57432905229402061856810453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153154413945072164951494541 57432905229402061856810453)
                  ·
                    refine ⟨1346083716314110824768995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57432905229402061856810453 1346083716314110824768995)
                    ·
                      rfl

theorem cell23_7864466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_7864466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864466 prefixEnd_7864466 := by exact prefixLift 7864466
  have htrace : WordTrace (prefixWord ++ tailWord_7864466) baseStart_7864466 baseEnd_7864466 := by
    simpa [prefixWord, tailWord_7864466, baseEnd_7864466] using wordTrace_append hprefix tailTrace_7864466
  have hstable : (prefixWord ++ tailWord_7864466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864466).length < 2 ^ (prefixWord ++ tailWord_7864466).sum := by decide
  have hdescent : baseEnd_7864466 < baseStart_7864466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864487 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 5]
def baseStart_7864487 : Nat := 118140960795 + 7864487 * 2 ^ 59
def prefixEnd_7864487 : Nat := 4983230072969 + 3 ^ 40 * 7864487 * 2
def baseEnd_7864487 : Nat := 448695770226230765793821

theorem tailTrace_7864487 : CollatzResearch.WordTrace tailWord_7864487 prefixEnd_7864487 448695770226230765793821 := by
  unfold tailWord_7864487
  simp only [CollatzResearch.WordTrace]
  refine ⟨286841405859314221291279715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191227603906209480860853143 286841405859314221291279715)
  ·
    refine ⟨430262108788971331936919573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286841405859314221291279715 430262108788971331936919573)
    ·
      refine ⟨20168536349483031184543105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 430262108788971331936919573 20168536349483031184543105)
      ·
        refine ⟨15126402262112273388407329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20168536349483031184543105 15126402262112273388407329)
        ·
          refine ⟨11344801696584205041305497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15126402262112273388407329 11344801696584205041305497)
          ·
            refine ⟨8508601272438153780979123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11344801696584205041305497 8508601272438153780979123)
            ·
              refine ⟨12762901908657230671468685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8508601272438153780979123 12762901908657230671468685)
              ·
                refine ⟨4786088215746461501800757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12762901908657230671468685 4786088215746461501800757)
                ·
                  refine ⟨448695770226230765793821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786088215746461501800757 448695770226230765793821)
                  ·
                    rfl

theorem cell23_7864487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 5].length) (baseStart_7864487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864487 prefixEnd_7864487 := by exact prefixLift 7864487
  have htrace : WordTrace (prefixWord ++ tailWord_7864487) baseStart_7864487 baseEnd_7864487 := by
    simpa [prefixWord, tailWord_7864487, baseEnd_7864487] using wordTrace_append hprefix tailTrace_7864487
  have hstable : (prefixWord ++ tailWord_7864487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864487).length < 2 ^ (prefixWord ++ tailWord_7864487).sum := by decide
  have hdescent : baseEnd_7864487 < baseStart_7864487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864489 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_7864489 : Nat := 118140960795 + 7864489 * 2 ^ 59
def prefixEnd_7864489 : Nat := 4983230072969 + 3 ^ 40 * 7864489 * 2
def baseEnd_7864489 : Nat := 4038262958997385884319379

theorem tailTrace_7864489 : CollatzResearch.WordTrace tailWord_7864489 prefixEnd_7864489 4038262958997385884319379 := by
  unfold tailWord_7864489
  simp only [CollatzResearch.WordTrace]
  refine ⟨286841478805306975632852521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191227652536871317088568347 286841478805306975632852521)
  ·
    refine ⟨215131109103980231724639391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286841478805306975632852521 215131109103980231724639391)
    ·
      refine ⟨322696663655970347586959087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215131109103980231724639391 322696663655970347586959087)
      ·
        refine ⟨484044995483955521380438631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322696663655970347586959087 484044995483955521380438631)
        ·
          refine ⟨726067493225933282070657947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484044995483955521380438631 726067493225933282070657947)
          ·
            refine ⟨1089101239838899923105986921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726067493225933282070657947 1089101239838899923105986921)
            ·
              refine ⟨816825929879174942329490191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089101239838899923105986921 816825929879174942329490191)
              ·
                refine ⟨1225238894818762413494235287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816825929879174942329490191 1225238894818762413494235287)
                ·
                  refine ⟨1837858342228143620241352931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225238894818762413494235287 1837858342228143620241352931)
                  ·
                    refine ⟨2756787513342215430362029397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1837858342228143620241352931 2756787513342215430362029397)
                    ·
                      refine ⟨4038262958997385884319379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2756787513342215430362029397 4038262958997385884319379)
                      ·
                        rfl

theorem cell23_7864489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_7864489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864489 prefixEnd_7864489 := by exact prefixLift 7864489
  have htrace : WordTrace (prefixWord ++ tailWord_7864489) baseStart_7864489 baseEnd_7864489 := by
    simpa [prefixWord, tailWord_7864489, baseEnd_7864489] using wordTrace_append hprefix tailTrace_7864489
  have hstable : (prefixWord ++ tailWord_7864489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864489).length < 2 ^ (prefixWord ++ tailWord_7864489).sum := by decide
  have hdescent : baseEnd_7864489 < baseStart_7864489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864503 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_7864503 : Nat := 118140960795 + 7864503 * 2 ^ 59
def prefixEnd_7864503 : Nat := 4983230072969 + 3 ^ 40 * 7864503 * 2
def baseEnd_7864503 : Nat := 4038270147726548829544315

theorem tailTrace_7864503 : CollatzResearch.WordTrace tailWord_7864503 prefixEnd_7864503 4038270147726548829544315 := by
  unfold tailWord_7864503
  simp only [CollatzResearch.WordTrace]
  refine ⟨286841989427256256023862163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191227992951504170682574775 286841989427256256023862163)
  ·
    refine ⟨430262984140884384035793245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286841989427256256023862163 430262984140884384035793245)
    ·
      refine ⟨161348619052831644013422467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430262984140884384035793245 161348619052831644013422467)
      ·
        refine ⟨242022928579247466020133701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161348619052831644013422467 242022928579247466020133701)
        ·
          refine ⟨45379299108608899878775069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242022928579247466020133701 45379299108608899878775069)
          ·
            refine ⟨17017237165728337454540651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45379299108608899878775069 17017237165728337454540651)
            ·
              refine ⟨25525855748592506181810977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17017237165728337454540651 25525855748592506181810977)
              ·
                refine ⟨19144391811444379636358233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25525855748592506181810977 19144391811444379636358233)
                ·
                  refine ⟨14358293858583284727268675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19144391811444379636358233 14358293858583284727268675)
                  ·
                    refine ⟨21537440787874927090903013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14358293858583284727268675 21537440787874927090903013)
                    ·
                      refine ⟨4038270147726548829544315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21537440787874927090903013 4038270147726548829544315)
                      ·
                        rfl

theorem cell23_7864503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_7864503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864503 prefixEnd_7864503 := by exact prefixLift 7864503
  have htrace : WordTrace (prefixWord ++ tailWord_7864503) baseStart_7864503 baseEnd_7864503 := by
    simpa [prefixWord, tailWord_7864503, baseEnd_7864503] using wordTrace_append hprefix tailTrace_7864503
  have hstable : (prefixWord ++ tailWord_7864503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864503).length < 2 ^ (prefixWord ++ tailWord_7864503).sum := by decide
  have hdescent : baseEnd_7864503 < baseStart_7864503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864553 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 3]
def baseStart_7864553 : Nat := 118140960795 + 7864553 * 2 ^ 59
def prefixEnd_7864553 : Nat := 4983230072969 + 3 ^ 40 * 7864553 * 2
def baseEnd_7864553 : Nat := 4038295821759273633919085

theorem tailTrace_7864553 : CollatzResearch.WordTrace tailWord_7864553 prefixEnd_7864553 4038295821759273633919085 := by
  unfold tailWord_7864553
  simp only [CollatzResearch.WordTrace]
  refine ⟨286843813077075114563182313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191229208718050076375454875 286843813077075114563182313)
  ·
    refine ⟨215132859807806335922386735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286843813077075114563182313 215132859807806335922386735)
    ·
      refine ⟨322699289711709503883580103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215132859807806335922386735 322699289711709503883580103)
      ·
        refine ⟨484048934567564255825370155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322699289711709503883580103 484048934567564255825370155)
        ·
          refine ⟨726073401851346383738055233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484048934567564255825370155 726073401851346383738055233)
          ·
            refine ⟨544555051388509787803541425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726073401851346383738055233 544555051388509787803541425)
            ·
              refine ⟨408416288541382340852656069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544555051388509787803541425 408416288541382340852656069)
              ·
                refine ⟨76578054101509188909873013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408416288541382340852656069 76578054101509188909873013)
                ·
                  refine ⟨7179192572016486460300595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76578054101509188909873013 7179192572016486460300595)
                  ·
                    refine ⟨10768788858024729690450893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7179192572016486460300595 10768788858024729690450893)
                    ·
                      refine ⟨4038295821759273633919085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10768788858024729690450893 4038295821759273633919085)
                      ·
                        rfl

theorem cell23_7864553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_7864553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864553 prefixEnd_7864553 := by exact prefixLift 7864553
  have htrace : WordTrace (prefixWord ++ tailWord_7864553) baseStart_7864553 baseEnd_7864553 := by
    simpa [prefixWord, tailWord_7864553, baseEnd_7864553] using wordTrace_append hprefix tailTrace_7864553
  have hstable : (prefixWord ++ tailWord_7864553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864553).length < 2 ^ (prefixWord ++ tailWord_7864553).sum := by decide
  have hdescent : baseEnd_7864553 < baseStart_7864553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864593 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_7864593 : Nat := 118140960795 + 7864593 * 2 ^ 59
def prefixEnd_7864593 : Nat := 4983230072969 + 3 ^ 40 * 7864593 * 2
def baseEnd_7864593 : Nat := 4038316360985453477418901

theorem tailTrace_7864593 : CollatzResearch.WordTrace tailWord_7864593 prefixEnd_7864593 4038316360985453477418901 := by
  unfold tailWord_7864593
  simp only [CollatzResearch.WordTrace]
  refine ⟨286845271996930201394638433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191230181331286800929758955 286845271996930201394638433)
  ·
    refine ⟨215133953997697651045978825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286845271996930201394638433 215133953997697651045978825)
    ·
      refine ⟨161350465498273238284484119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215133953997697651045978825 161350465498273238284484119)
      ·
        refine ⟨242025698247409857426726179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161350465498273238284484119 242025698247409857426726179)
        ·
          refine ⟨363038547371114786140089269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242025698247409857426726179 363038547371114786140089269)
          ·
            refine ⟨34034863816042011200633369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 363038547371114786140089269 34034863816042011200633369)
            ·
              refine ⟨25526147862031508400475027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34034863816042011200633369 25526147862031508400475027)
              ·
                refine ⟨38289221793047262600712541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25526147862031508400475027 38289221793047262600712541)
                ·
                  refine ⟨14358458172392723475267203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38289221793047262600712541 14358458172392723475267203)
                  ·
                    refine ⟨21537687258589085212900805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14358458172392723475267203 21537687258589085212900805)
                    ·
                      refine ⟨4038316360985453477418901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21537687258589085212900805 4038316360985453477418901)
                      ·
                        rfl

theorem cell23_7864593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_7864593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864593 prefixEnd_7864593 := by exact prefixLift 7864593
  have htrace : WordTrace (prefixWord ++ tailWord_7864593) baseStart_7864593 baseEnd_7864593 := by
    simpa [prefixWord, tailWord_7864593, baseEnd_7864593] using wordTrace_append hprefix tailTrace_7864593
  have hstable : (prefixWord ++ tailWord_7864593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864593).length < 2 ^ (prefixWord ++ tailWord_7864593).sum := by decide
  have hdescent : baseEnd_7864593 < baseStart_7864593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864607 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 1, 5]
def baseStart_7864607 : Nat := 118140960795 + 7864607 * 2 ^ 59
def prefixEnd_7864607 : Nat := 4983230072969 + 3 ^ 40 * 7864607 * 2
def baseEnd_7864607 : Nat := 1346107849904872140881279

theorem tailTrace_7864607 : CollatzResearch.WordTrace tailWord_7864607 prefixEnd_7864607 1346107849904872140881279 := by
  unfold tailWord_7864607
  simp only [CollatzResearch.WordTrace]
  refine ⟨286845782618879481785648075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191230521745919654523765383 286845782618879481785648075)
  ·
    refine ⟨430268673928319222678472113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286845782618879481785648075 430268673928319222678472113)
    ·
      refine ⟨322701505446239417008854085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430268673928319222678472113 322701505446239417008854085)
      ·
        refine ⟨60506532271169890689160141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322701505446239417008854085 60506532271169890689160141)
        ·
          refine ⟨22689949601688709008435053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60506532271169890689160141 22689949601688709008435053)
          ·
            refine ⟨8508731100633265878163145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22689949601688709008435053 8508731100633265878163145)
            ·
              refine ⟨6381548325474949408622359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8508731100633265878163145 6381548325474949408622359)
              ·
                refine ⟨9572322488212424112933539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381548325474949408622359 9572322488212424112933539)
                ·
                  refine ⟨14358483732318636169400309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9572322488212424112933539 14358483732318636169400309)
                  ·
                    refine ⟨1346107849904872140881279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14358483732318636169400309 1346107849904872140881279)
                    ·
                      rfl

theorem cell23_7864607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 5].length) (baseStart_7864607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864607 prefixEnd_7864607 := by exact prefixLift 7864607
  have htrace : WordTrace (prefixWord ++ tailWord_7864607) baseStart_7864607 baseEnd_7864607 := by
    simpa [prefixWord, tailWord_7864607, baseEnd_7864607] using wordTrace_append hprefix tailTrace_7864607
  have hstable : (prefixWord ++ tailWord_7864607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864607).length < 2 ^ (prefixWord ++ tailWord_7864607).sum := by decide
  have hdescent : baseEnd_7864607 < baseStart_7864607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864620 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_7864620 : Nat := 118140960795 + 7864620 * 2 ^ 59
def prefixEnd_7864620 : Nat := 4983230072969 + 3 ^ 40 * 7864620 * 2
def baseEnd_7864620 : Nat := 1346110074987708290593759

theorem tailTrace_7864620 : CollatzResearch.WordTrace tailWord_7864620 prefixEnd_7864620 1346110074987708290593759 := by
  unfold tailWord_7864620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143423128383916192502935657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191230837845221590003914209 143423128383916192502935657)
  ·
    refine ⟨107567346287937144377201743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143423128383916192502935657 107567346287937144377201743)
    ·
      refine ⟨161351019431905716565802615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107567346287937144377201743 161351019431905716565802615)
      ·
        refine ⟨242026529147858574848703923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161351019431905716565802615 242026529147858574848703923)
        ·
          refine ⟨363039793721787862273055885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242026529147858574848703923 363039793721787862273055885)
          ·
            refine ⟨136139922645670448352395957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363039793721787862273055885 136139922645670448352395957)
            ·
              refine ⟨12763117748031604533037121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136139922645670448352395957 12763117748031604533037121)
              ·
                refine ⟨9572338311023703399777841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12763117748031604533037121 9572338311023703399777841)
                ·
                  refine ⟨7179253733267777549833381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9572338311023703399777841 7179253733267777549833381)
                  ·
                    refine ⟨1346110074987708290593759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7179253733267777549833381 1346110074987708290593759)
                    ·
                      rfl

theorem cell23_7864620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_7864620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864620 prefixEnd_7864620 := by exact prefixLift 7864620
  have htrace : WordTrace (prefixWord ++ tailWord_7864620) baseStart_7864620 baseEnd_7864620 := by
    simpa [prefixWord, tailWord_7864620, baseEnd_7864620] using wordTrace_append hprefix tailTrace_7864620
  have hstable : (prefixWord ++ tailWord_7864620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864620).length < 2 ^ (prefixWord ++ tailWord_7864620).sum := by decide
  have hdescent : baseEnd_7864620 < baseStart_7864620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864627 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 3, 2, 2]
def baseStart_7864627 : Nat := 118140960795 + 7864627 * 2 ^ 59
def prefixEnd_7864627 : Nat := 4983230072969 + 3 ^ 40 * 7864627 * 2
def baseEnd_7864627 : Nat := 4038333819327706344393745

theorem tailTrace_7864627 : CollatzResearch.WordTrace tailWord_7864627 prefixEnd_7864627 4038333819327706344393745 := by
  unfold tailWord_7864627
  simp only [CollatzResearch.WordTrace]
  refine ⟨286846512078807025201376135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191231008052538016800917423 286846512078807025201376135)
  ·
    refine ⟨430269768118210537802064203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286846512078807025201376135 430269768118210537802064203)
    ·
      refine ⟨645404652177315806703096305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430269768118210537802064203 645404652177315806703096305)
      ·
        refine ⟨484053489132986855027322229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645404652177315806703096305 484053489132986855027322229)
        ·
          refine ⟨45380014606217517658811459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484053489132986855027322229 45380014606217517658811459)
          ·
            refine ⟨68070021909326276488217189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45380014606217517658811459 68070021909326276488217189)
            ·
              refine ⟨12763129107998676841540723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68070021909326276488217189 12763129107998676841540723)
              ·
                refine ⟨19144693661998015262311085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12763129107998676841540723 19144693661998015262311085)
                ·
                  refine ⟨7179260123249255723366657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19144693661998015262311085 7179260123249255723366657)
                  ·
                    refine ⟨5384445092436941792524993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179260123249255723366657 5384445092436941792524993)
                    ·
                      refine ⟨4038333819327706344393745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384445092436941792524993 4038333819327706344393745)
                      ·
                        rfl

theorem cell23_7864627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 2, 2].length) (baseStart_7864627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864627 prefixEnd_7864627 := by exact prefixLift 7864627
  have htrace : WordTrace (prefixWord ++ tailWord_7864627) baseStart_7864627 baseEnd_7864627 := by
    simpa [prefixWord, tailWord_7864627, baseEnd_7864627] using wordTrace_append hprefix tailTrace_7864627
  have hstable : (prefixWord ++ tailWord_7864627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864627).length < 2 ^ (prefixWord ++ tailWord_7864627).sum := by decide
  have hdescent : baseEnd_7864627 < baseStart_7864627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864644 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7864644 : Nat := 118140960795 + 7864644 * 2 ^ 59
def prefixEnd_7864644 : Nat := 4983230072969 + 3 ^ 40 * 7864644 * 2
def baseEnd_7864644 : Nat := 4038342548498832777881167

theorem tailTrace_7864644 : CollatzResearch.WordTrace tailWord_7864644 prefixEnd_7864644 4038342548498832777881167 := by
  unfold tailWord_7864644
  simp only [CollatzResearch.WordTrace]
  refine ⟨143423566059872718552372493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191231421413163624736496657 143423566059872718552372493)
  ·
    refine ⟨53783837272452269457139685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143423566059872718552372493 53783837272452269457139685)
    ·
      refine ⟨10084469488584800523213691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53783837272452269457139685 10084469488584800523213691)
      ·
        refine ⟨15126704232877200784820537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10084469488584800523213691 15126704232877200784820537)
        ·
          refine ⟨11345028174657900588615403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15126704232877200784820537 11345028174657900588615403)
          ·
            refine ⟨17017542261986850882923105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345028174657900588615403 17017542261986850882923105)
            ·
              refine ⟨12763156696490138162192329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17017542261986850882923105 12763156696490138162192329)
              ·
                refine ⟨9572367522367603621644247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12763156696490138162192329 9572367522367603621644247)
                ·
                  refine ⟨14358551283551405432466371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9572367522367603621644247 14358551283551405432466371)
                  ·
                    refine ⟨21537826925327108148699557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14358551283551405432466371 21537826925327108148699557)
                    ·
                      refine ⟨4038342548498832777881167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21537826925327108148699557 4038342548498832777881167)
                      ·
                        rfl

theorem cell23_7864644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7864644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864644 prefixEnd_7864644 := by exact prefixLift 7864644
  have htrace : WordTrace (prefixWord ++ tailWord_7864644) baseStart_7864644 baseEnd_7864644 := by
    simpa [prefixWord, tailWord_7864644, baseEnd_7864644] using wordTrace_append hprefix tailTrace_7864644
  have hstable : (prefixWord ++ tailWord_7864644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864644).length < 2 ^ (prefixWord ++ tailWord_7864644).sum := by decide
  have hdescent : baseEnd_7864644 < baseStart_7864644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864703 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_7864703 : Nat := 118140960795 + 7864703 * 2 ^ 59
def prefixEnd_7864703 : Nat := 4983230072969 + 3 ^ 40 * 7864703 * 2
def baseEnd_7864703 : Nat := 4038372843857448047043395

theorem tailTrace_7864703 : CollatzResearch.WordTrace tailWord_7864703 prefixEnd_7864703 4038372843857448047043395 := by
  unfold tailWord_7864703
  simp only [CollatzResearch.WordTrace]
  refine ⟨286849284026531690181142763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191232856017687793454095175 286849284026531690181142763)
  ·
    refine ⟨430273926039797535271714145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286849284026531690181142763 430273926039797535271714145)
    ·
      refine ⟨322705444529848151453785609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430273926039797535271714145 322705444529848151453785609)
      ·
        refine ⟨242029083397386113590339207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322705444529848151453785609 242029083397386113590339207)
        ·
          refine ⟨363043625096079170385508811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242029083397386113590339207 363043625096079170385508811)
          ·
            refine ⟨544565437644118755578263217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363043625096079170385508811 544565437644118755578263217)
            ·
              refine ⟨408424078233089066683697413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544565437644118755578263217 408424078233089066683697413)
              ·
                refine ⟨76579514668704200003193265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408424078233089066683697413 76579514668704200003193265)
                ·
                  refine ⟨57434636001528150002394949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76579514668704200003193265 57434636001528150002394949)
                  ·
                    refine ⟨10768994250286528125449053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57434636001528150002394949 10768994250286528125449053)
                    ·
                      refine ⟨4038372843857448047043395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10768994250286528125449053 4038372843857448047043395)
                      ·
                        rfl

theorem cell23_7864703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_7864703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864703 prefixEnd_7864703 := by exact prefixLift 7864703
  have htrace : WordTrace (prefixWord ++ tailWord_7864703) baseStart_7864703 baseEnd_7864703 := by
    simpa [prefixWord, tailWord_7864703, baseEnd_7864703] using wordTrace_append hprefix tailTrace_7864703
  have hstable : (prefixWord ++ tailWord_7864703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864703).length < 2 ^ (prefixWord ++ tailWord_7864703).sum := by decide
  have hdescent : baseEnd_7864703 < baseStart_7864703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864760 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 4, 5, 2]
def baseStart_7864760 : Nat := 118140960795 + 7864760 * 2 ^ 59
def prefixEnd_7864760 : Nat := 4983230072969 + 3 ^ 40 * 7864760 * 2
def baseEnd_7864760 : Nat := 4038402112254754324030633

theorem tailTrace_7864760 : CollatzResearch.WordTrace tailWord_7864760 prefixEnd_7864760 4038402112254754324030633 := by
  unfold tailWord_7864760
  simp only [CollatzResearch.WordTrace]
  refine ⟨143425681493662594457983867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191234241991550125943978489 143425681493662594457983867)
  ·
    refine ⟨215138522240493891686975801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143425681493662594457983867 215138522240493891686975801)
    ·
      refine ⟨161353891680370418765231851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215138522240493891686975801 161353891680370418765231851)
      ·
        refine ⟨242030837520555628147847777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161353891680370418765231851 242030837520555628147847777)
        ·
          refine ⟨181523128140416721110885833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242030837520555628147847777 181523128140416721110885833)
          ·
            refine ⟨136142346105312540833164375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181523128140416721110885833 136142346105312540833164375)
            ·
              refine ⟨204213519157968811249746563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136142346105312540833164375 204213519157968811249746563)
              ·
                refine ⟨306320278736953216874619845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204213519157968811249746563 306320278736953216874619845)
                ·
                  refine ⟨57435052263178728163991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306320278736953216874619845 57435052263178728163991221)
                  ·
                    refine ⟨5384536149673005765374177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57435052263178728163991221 5384536149673005765374177)
                    ·
                      refine ⟨4038402112254754324030633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384536149673005765374177 4038402112254754324030633)
                      ·
                        rfl

theorem cell23_7864760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_7864760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864760 prefixEnd_7864760 := by exact prefixLift 7864760
  have htrace : WordTrace (prefixWord ++ tailWord_7864760) baseStart_7864760 baseEnd_7864760 := by
    simpa [prefixWord, tailWord_7864760, baseEnd_7864760] using wordTrace_append hprefix tailTrace_7864760
  have hstable : (prefixWord ++ tailWord_7864760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864760).length < 2 ^ (prefixWord ++ tailWord_7864760).sum := by decide
  have hdescent : baseEnd_7864760 < baseStart_7864760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864807 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_7864807 : Nat := 118140960795 + 7864807 * 2 ^ 59
def prefixEnd_7864807 : Nat := 4983230072969 + 3 ^ 40 * 7864807 * 2
def baseEnd_7864807 : Nat := 4038426245845515640142917

theorem tailTrace_7864807 : CollatzResearch.WordTrace tailWord_7864807 prefixEnd_7864807 4038426245845515640142917 := by
  unfold tailWord_7864807
  simp only [CollatzResearch.WordTrace]
  refine ⟨286853077218154915942928675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191235384812103277295285783 286853077218154915942928675)
  ·
    refine ⟨430279615827232373914393013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286853077218154915942928675 430279615827232373914393013)
    ·
      refine ⟨40338713983803035054474345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430279615827232373914393013 40338713983803035054474345)
      ·
        refine ⟨30254035487852276290855759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40338713983803035054474345 30254035487852276290855759)
        ·
          refine ⟨45381053231778414436283639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30254035487852276290855759 45381053231778414436283639)
          ·
            refine ⟨68071579847667621654425459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45381053231778414436283639 68071579847667621654425459)
            ·
              refine ⟨102107369771501432481638189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68071579847667621654425459 102107369771501432481638189)
              ·
                refine ⟨38290263664313037180614321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102107369771501432481638189 38290263664313037180614321)
                ·
                  refine ⟨28717697748234777885460741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38290263664313037180614321 28717697748234777885460741)
                  ·
                    refine ⟨5384568327794020853523889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28717697748234777885460741 5384568327794020853523889)
                    ·
                      refine ⟨4038426245845515640142917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384568327794020853523889 4038426245845515640142917)
                      ·
                        rfl

theorem cell23_7864807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_7864807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864807 prefixEnd_7864807 := by exact prefixLift 7864807
  have htrace : WordTrace (prefixWord ++ tailWord_7864807) baseStart_7864807 baseEnd_7864807 := by
    simpa [prefixWord, tailWord_7864807, baseEnd_7864807] using wordTrace_append hprefix tailTrace_7864807
  have hstable : (prefixWord ++ tailWord_7864807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864807).length < 2 ^ (prefixWord ++ tailWord_7864807).sum := by decide
  have hdescent : baseEnd_7864807 < baseStart_7864807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864890 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_7864890 : Nat := 118140960795 + 7864890 * 2 ^ 59
def prefixEnd_7864890 : Nat := 4983230072969 + 3 ^ 40 * 7864890 * 2
def baseEnd_7864890 : Nat := 1346156288246612938468345

theorem tailTrace_7864890 : CollatzResearch.WordTrace tailWord_7864890 prefixEnd_7864890 1346156288246612938468345 := by
  unfold tailWord_7864890
  simp only [CollatzResearch.WordTrace]
  refine ⟨71714026119213555279550031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191237402984569480745466749 71714026119213555279550031)
  ·
    refine ⟨107571039178820332919325047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71714026119213555279550031 107571039178820332919325047)
    ·
      refine ⟨161356558768230499378987571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107571039178820332919325047 161356558768230499378987571)
      ·
        refine ⟨242034838152345749068481357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161356558768230499378987571 242034838152345749068481357)
        ·
          refine ⟨90763064307129655900680509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242034838152345749068481357 90763064307129655900680509)
          ·
            refine ⟨34036149115173620962755191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90763064307129655900680509 34036149115173620962755191)
            ·
              refine ⟨51054223672760431444132787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34036149115173620962755191 51054223672760431444132787)
              ·
                refine ⟨76581335509140647166199181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51054223672760431444132787 76581335509140647166199181)
                ·
                  refine ⟨28718000815927742687324693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76581335509140647166199181 28718000815927742687324693)
                  ·
                    refine ⟨1346156288246612938468345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28718000815927742687324693 1346156288246612938468345)
                    ·
                      rfl

theorem cell23_7864890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_7864890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864890 prefixEnd_7864890 := by exact prefixLift 7864890
  have htrace : WordTrace (prefixWord ++ tailWord_7864890) baseStart_7864890 baseEnd_7864890 := by
    simpa [prefixWord, tailWord_7864890, baseEnd_7864890] using wordTrace_append hprefix tailTrace_7864890
  have hstable : (prefixWord ++ tailWord_7864890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864890).length < 2 ^ (prefixWord ++ tailWord_7864890).sum := by decide
  have hdescent : baseEnd_7864890 < baseStart_7864890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864907 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 2, 4]
def baseStart_7864907 : Nat := 118140960795 + 7864907 * 2 ^ 59
def prefixEnd_7864907 : Nat := 4983230072969 + 3 ^ 40 * 7864907 * 2
def baseEnd_7864907 : Nat := 1346159197970321749630819

theorem tailTrace_7864907 : CollatzResearch.WordTrace tailWord_7864907 prefixEnd_7864907 1346159197970321749630819 := by
  unfold tailWord_7864907
  simp only [CollatzResearch.WordTrace]
  refine ⟨286856724517792633021568975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191237816345195088681045983 286856724517792633021568975)
  ·
    refine ⟨430285086776688949532353463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286856724517792633021568975 430285086776688949532353463)
    ·
      refine ⟨645427630165033424298530195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430285086776688949532353463 645427630165033424298530195)
      ·
        refine ⟨968141445247550136447795293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645427630165033424298530195 968141445247550136447795293)
        ·
          refine ⟨363053041967831301167923235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968141445247550136447795293 363053041967831301167923235)
          ·
            refine ⟨544579562951746951751884853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363053041967831301167923235 544579562951746951751884853)
            ·
              refine ⟨51054334026726276726739205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 544579562951746951751884853 51054334026726276726739205)
              ·
                refine ⟨9572687630011176886263601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51054334026726276726739205 9572687630011176886263601)
                ·
                  refine ⟨7179515722508382664697701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9572687630011176886263601 7179515722508382664697701)
                  ·
                    refine ⟨1346159197970321749630819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7179515722508382664697701 1346159197970321749630819)
                    ·
                      rfl

theorem cell23_7864907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 4].length) (baseStart_7864907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864907 prefixEnd_7864907 := by exact prefixLift 7864907
  have htrace : WordTrace (prefixWord ++ tailWord_7864907) baseStart_7864907 baseEnd_7864907 := by
    simpa [prefixWord, tailWord_7864907, baseEnd_7864907] using wordTrace_append hprefix tailTrace_7864907
  have hstable : (prefixWord ++ tailWord_7864907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864907).length < 2 ^ (prefixWord ++ tailWord_7864907).sum := by decide
  have hdescent : baseEnd_7864907 < baseStart_7864907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864910 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_7864910 : Nat := 118140960795 + 7864910 * 2 ^ 59
def prefixEnd_7864910 : Nat := 4983230072969 + 3 ^ 40 * 7864910 * 2
def baseEnd_7864910 : Nat := 4038479134352928737154943

theorem tailTrace_7864910 : CollatzResearch.WordTrace tailWord_7864910 prefixEnd_7864910 4038479134352928737154943 := by
  unfold tailWord_7864910
  simp only [CollatzResearch.WordTrace]
  refine ⟨35857104242097720566741023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191237889291187843022618789 35857104242097720566741023)
  ·
    refine ⟨53785656363146580850111535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35857104242097720566741023 53785656363146580850111535)
    ·
      refine ⟨80678484544719871275167303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53785656363146580850111535 80678484544719871275167303)
      ·
        refine ⟨121017726817079806912750955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80678484544719871275167303 121017726817079806912750955)
        ·
          refine ⟨181526590225619710369126433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121017726817079806912750955 181526590225619710369126433)
          ·
            refine ⟨136144942669214782776844825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181526590225619710369126433 136144942669214782776844825)
            ·
              refine ⟨102108707001911087082633619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136144942669214782776844825 102108707001911087082633619)
              ·
                refine ⟨153163060502866630623950429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102108707001911087082633619 153163060502866630623950429)
                ·
                  refine ⟨57436147688574986483981411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153163060502866630623950429 57436147688574986483981411)
                  ·
                    refine ⟨86154221532862479725972117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57436147688574986483981411 86154221532862479725972117)
                    ·
                      refine ⟨4038479134352928737154943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86154221532862479725972117 4038479134352928737154943)
                      ·
                        rfl

theorem cell23_7864910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_7864910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864910 prefixEnd_7864910 := by exact prefixLift 7864910
  have htrace : WordTrace (prefixWord ++ tailWord_7864910) baseStart_7864910 baseEnd_7864910 := by
    simpa [prefixWord, tailWord_7864910, baseEnd_7864910] using wordTrace_append hprefix tailTrace_7864910
  have hstable : (prefixWord ++ tailWord_7864910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864910).length < 2 ^ (prefixWord ++ tailWord_7864910).sum := by decide
  have hdescent : baseEnd_7864910 < baseStart_7864910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864917 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7864917 : Nat := 118140960795 + 7864917 * 2 ^ 59
def prefixEnd_7864917 : Nat := 4983230072969 + 3 ^ 40 * 7864917 * 2
def baseEnd_7864917 : Nat := 4038482728717510209767411

theorem tailTrace_7864917 : CollatzResearch.WordTrace tailWord_7864917 prefixEnd_7864917 4038482728717510209767411 := by
  unfold tailWord_7864917
  simp only [CollatzResearch.WordTrace]
  refine ⟨286857089247756404729433005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191238059498504269819622003 286857089247756404729433005)
  ·
    refine ⟨107571408467908651773537377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286857089247756404729433005 107571408467908651773537377)
    ·
      refine ⟨80678556350931488830153033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107571408467908651773537377 80678556350931488830153033)
      ·
        refine ⟨60508917263198616622614775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80678556350931488830153033 60508917263198616622614775)
        ·
          refine ⟨90763375894797924933922163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60508917263198616622614775 90763375894797924933922163)
          ·
            refine ⟨136145063842196887400883245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90763375894797924933922163 136145063842196887400883245)
            ·
              refine ⟨51054398940823832775331217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136145063842196887400883245 51054398940823832775331217)
              ·
                refine ⟨38290799205617874581498413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51054398940823832775331217 38290799205617874581498413)
                ·
                  refine ⟨14359049702106702968061905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38290799205617874581498413 14359049702106702968061905)
                  ·
                    refine ⟨10769287276580027226046429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14359049702106702968061905 10769287276580027226046429)
                    ·
                      refine ⟨4038482728717510209767411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769287276580027226046429 4038482728717510209767411)
                      ·
                        rfl

theorem cell23_7864917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7864917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864917 prefixEnd_7864917 := by exact prefixLift 7864917
  have htrace : WordTrace (prefixWord ++ tailWord_7864917) baseStart_7864917 baseEnd_7864917 := by
    simpa [prefixWord, tailWord_7864917, baseEnd_7864917] using wordTrace_append hprefix tailTrace_7864917
  have hstable : (prefixWord ++ tailWord_7864917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864917).length < 2 ^ (prefixWord ++ tailWord_7864917).sum := by decide
  have hdescent : baseEnd_7864917 < baseStart_7864917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864920 : List Nat := [2, 1, 2, 2, 1, 2, 5, 8]
def baseStart_7864920 : Nat := 118140960795 + 7864920 * 2 ^ 59
def prefixEnd_7864920 : Nat := 4983230072969 + 3 ^ 40 * 7864920 * 2
def baseEnd_7864920 : Nat := 149573491450350877704811

theorem tailTrace_7864920 : CollatzResearch.WordTrace tailWord_7864920 prefixEnd_7864920 149573491450350877704811 := by
  unfold tailWord_7864920
  simp only [CollatzResearch.WordTrace]
  refine ⟨143428599333372768120896107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191238132444497024161194809 143428599333372768120896107)
  ·
    refine ⟨215142899000059152181344161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143428599333372768120896107 215142899000059152181344161)
    ·
      refine ⟨161357174250044364136008121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215142899000059152181344161 161357174250044364136008121)
      ·
        refine ⟨121017880687533273102006091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161357174250044364136008121 121017880687533273102006091)
        ·
          refine ⟨181526821031299909653009137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121017880687533273102006091 181526821031299909653009137)
          ·
            refine ⟨136145115773474932239756853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181526821031299909653009137 136145115773474932239756853)
            ·
              refine ⟨12763604603763274897477205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136145115773474932239756853 12763604603763274897477205)
              ·
                refine ⟨149573491450350877704811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12763604603763274897477205 149573491450350877704811)
                ·
                  rfl

theorem cell23_7864920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 8].length) (baseStart_7864920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864920 prefixEnd_7864920 := by exact prefixLift 7864920
  have htrace : WordTrace (prefixWord ++ tailWord_7864920) baseStart_7864920 baseEnd_7864920 := by
    simpa [prefixWord, tailWord_7864920, baseEnd_7864920] using wordTrace_append hprefix tailTrace_7864920
  have hstable : (prefixWord ++ tailWord_7864920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864920).length < 2 ^ (prefixWord ++ tailWord_7864920).sum := by decide
  have hdescent : baseEnd_7864920 < baseStart_7864920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864924 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7864924 : Nat := 118140960795 + 7864924 * 2 ^ 59
def prefixEnd_7864924 : Nat := 4983230072969 + 3 ^ 40 * 7864924 * 2
def baseEnd_7864924 : Nat := 1346162107694030560793293

theorem tailTrace_7864924 : CollatzResearch.WordTrace tailWord_7864924 prefixEnd_7864924 1346162107694030560793293 := by
  unfold tailWord_7864924
  simp only [CollatzResearch.WordTrace]
  refine ⟨143428672279365522462468913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191238229705820696616625217 143428672279365522462468913)
  ·
    refine ⟨107571504209524141846851685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143428672279365522462468913 107571504209524141846851685)
    ·
      refine ⟨20169657039285776596284691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107571504209524141846851685 20169657039285776596284691)
      ·
        refine ⟨30254485558928664894427037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20169657039285776596284691 30254485558928664894427037)
        ·
          refine ⟨11345432084598249335410139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30254485558928664894427037 11345432084598249335410139)
          ·
            refine ⟨17018148126897374003115209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345432084598249335410139 17018148126897374003115209)
            ·
              refine ⟨12763611095173030502336407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17018148126897374003115209 12763611095173030502336407)
              ·
                refine ⟨19145416642759545753504611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12763611095173030502336407 19145416642759545753504611)
                ·
                  refine ⟨28718124964139318630256917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19145416642759545753504611 28718124964139318630256917)
                  ·
                    refine ⟨1346162107694030560793293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28718124964139318630256917 1346162107694030560793293)
                    ·
                      rfl

theorem cell23_7864924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7864924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864924 prefixEnd_7864924 := by exact prefixLift 7864924
  have htrace : WordTrace (prefixWord ++ tailWord_7864924) baseStart_7864924 baseEnd_7864924 := by
    simpa [prefixWord, tailWord_7864924, baseEnd_7864924] using wordTrace_append hprefix tailTrace_7864924
  have hstable : (prefixWord ++ tailWord_7864924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864924).length < 2 ^ (prefixWord ++ tailWord_7864924).sum := by decide
  have hdescent : baseEnd_7864924 < baseStart_7864924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864999 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7864999 : Nat := 118140960795 + 7864999 * 2 ^ 59
def prefixEnd_7864999 : Nat := 4983230072969 + 3 ^ 40 * 7864999 * 2
def baseEnd_7864999 : Nat := 4038524834131178888942035

theorem tailTrace_7864999 : CollatzResearch.WordTrace tailWord_7864999 prefixEnd_7864999 4038524834131178888942035 := by
  unfold tailWord_7864999
  simp only [CollatzResearch.WordTrace]
  refine ⟨286860080033459332733918051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191240053355639555155945367 286860080033459332733918051)
  ·
    refine ⟨430290120050188999100877077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286860080033459332733918051 430290120050188999100877077)
    ·
      refine ⟨20169849377352609332853613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 430290120050188999100877077 20169849377352609332853613)
      ·
        refine ⟨7563693516507228499820105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20169849377352609332853613 7563693516507228499820105)
        ·
          refine ⟨5672770137380421374865079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7563693516507228499820105 5672770137380421374865079)
          ·
            refine ⟨8509155206070632062297619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672770137380421374865079 8509155206070632062297619)
            ·
              refine ⟨12763732809105948093446429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509155206070632062297619 12763732809105948093446429)
              ·
                refine ⟨4786399803414730535042411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12763732809105948093446429 4786399803414730535042411)
                ·
                  refine ⟨7179599705122095802563617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786399803414730535042411 7179599705122095802563617)
                  ·
                    refine ⟨5384699778841571851922713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179599705122095802563617 5384699778841571851922713)
                    ·
                      refine ⟨4038524834131178888942035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384699778841571851922713 4038524834131178888942035)
                      ·
                        rfl

theorem cell23_7864999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7864999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7864999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7864999 prefixEnd_7864999 := by exact prefixLift 7864999
  have htrace : WordTrace (prefixWord ++ tailWord_7864999) baseStart_7864999 baseEnd_7864999 := by
    simpa [prefixWord, tailWord_7864999, baseEnd_7864999] using wordTrace_append hprefix tailTrace_7864999
  have hstable : (prefixWord ++ tailWord_7864999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864999).length < 2 ^ (prefixWord ++ tailWord_7864999).sum := by decide
  have hdescent : baseEnd_7864999 < baseStart_7864999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865007 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_7865007 : Nat := 118140960795 + 7865007 * 2 ^ 59
def prefixEnd_7865007 : Nat := 4983230072969 + 3 ^ 40 * 7865007 * 2
def baseEnd_7865007 : Nat := 4038528941976414857641997

theorem tailTrace_7865007 : CollatzResearch.WordTrace tailWord_7865007 prefixEnd_7865007 4038528941976414857641997 := by
  unfold tailWord_7865007
  simp only [CollatzResearch.WordTrace]
  refine ⟨286860371817430350100209275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191240247878286900066806183 286860371817430350100209275)
  ·
    refine ⟨430290557726145525150313913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286860371817430350100209275 430290557726145525150313913)
    ·
      refine ⟨322717918294609143862735435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430290557726145525150313913 322717918294609143862735435)
      ·
        refine ⟨484076877441913715794103153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322717918294609143862735435 484076877441913715794103153)
        ·
          refine ⟨363057658081435286845577365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484076877441913715794103153 363057658081435286845577365)
          ·
            refine ⟨17018327722567279070886439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 363057658081435286845577365 17018327722567279070886439)
            ·
              refine ⟨25527491583850918606329659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17018327722567279070886439 25527491583850918606329659)
              ·
                refine ⟨38291237375776377909494489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25527491583850918606329659 38291237375776377909494489)
                ·
                  refine ⟨28718428031832283432120867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38291237375776377909494489 28718428031832283432120867)
                  ·
                    refine ⟨43077642047748425148181301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28718428031832283432120867 43077642047748425148181301)
                    ·
                      refine ⟨4038528941976414857641997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43077642047748425148181301 4038528941976414857641997)
                      ·
                        rfl

theorem cell23_7865007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_7865007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865007 prefixEnd_7865007 := by exact prefixLift 7865007
  have htrace : WordTrace (prefixWord ++ tailWord_7865007) baseStart_7865007 baseEnd_7865007 := by
    simpa [prefixWord, tailWord_7865007, baseEnd_7865007] using wordTrace_append hprefix tailTrace_7865007
  have hstable : (prefixWord ++ tailWord_7865007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865007).length < 2 ^ (prefixWord ++ tailWord_7865007).sum := by decide
  have hdescent : baseEnd_7865007 < baseStart_7865007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865021 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_7865021 : Nat := 118140960795 + 7865021 * 2 ^ 59
def prefixEnd_7865021 : Nat := 4983230072969 + 3 ^ 40 * 7865021 * 2
def baseEnd_7865021 : Nat := 4038536130705577802866933

theorem tailTrace_7865021 : CollatzResearch.WordTrace tailWord_7865021 prefixEnd_7865021 4038536130705577802866933 := by
  unfold tailWord_7865021
  simp only [CollatzResearch.WordTrace]
  refine ⟨286860882439379630491218917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191240588292919753660812611 286860882439379630491218917)
  ·
    refine ⟨53786415457383680717103547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286860882439379630491218917 53786415457383680717103547)
    ·
      refine ⟨80679623186075521075655321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53786415457383680717103547 80679623186075521075655321)
      ·
        refine ⟨60509717389556640806741491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80679623186075521075655321 60509717389556640806741491)
        ·
          refine ⟨90764576084334961210112237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60509717389556640806741491 90764576084334961210112237)
          ·
            refine ⟨34036716031625610453792089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90764576084334961210112237 34036716031625610453792089)
            ·
              refine ⟨25527537023719207840344067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34036716031625610453792089 25527537023719207840344067)
              ·
                refine ⟨38291305535578811760516101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25527537023719207840344067 38291305535578811760516101)
                ·
                  refine ⟨7179619787921027205096769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38291305535578811760516101 7179619787921027205096769)
                  ·
                    refine ⟨5384714840940770403822577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179619787921027205096769 5384714840940770403822577)
                    ·
                      refine ⟨4038536130705577802866933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384714840940770403822577 4038536130705577802866933)
                      ·
                        rfl

theorem cell23_7865021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_7865021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865021 prefixEnd_7865021 := by exact prefixLift 7865021
  have htrace : WordTrace (prefixWord ++ tailWord_7865021) baseStart_7865021 baseEnd_7865021 := by
    simpa [prefixWord, tailWord_7865021, baseEnd_7865021] using wordTrace_append hprefix tailTrace_7865021
  have hstable : (prefixWord ++ tailWord_7865021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865021).length < 2 ^ (prefixWord ++ tailWord_7865021).sum := by decide
  have hdescent : baseEnd_7865021 < baseStart_7865021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865038 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_7865038 : Nat := 118140960795 + 7865038 * 2 ^ 59
def prefixEnd_7865038 : Nat := 4983230072969 + 3 ^ 40 * 7865038 * 2
def baseEnd_7865038 : Nat := 4038544859876704236354355

theorem tailTrace_7865038 : CollatzResearch.WordTrace tailWord_7865038 prefixEnd_7865038 4038544859876704236354355 := by
  unfold tailWord_7865038
  simp only [CollatzResearch.WordTrace]
  refine ⟨35857687810039755299323471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191241001653545361596391845 35857687810039755299323471)
  ·
    refine ⟨53786531715059632948985207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35857687810039755299323471 53786531715059632948985207)
    ·
      refine ⟨80679797572589449423477811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53786531715059632948985207 80679797572589449423477811)
      ·
        refine ⟨121019696358884174135216717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80679797572589449423477811 121019696358884174135216717)
        ·
          refine ⟨45382386134581565300706269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121019696358884174135216717 45382386134581565300706269)
          ·
            refine ⟨17018394800468086987764851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45382386134581565300706269 17018394800468086987764851)
            ·
              refine ⟨25527592200702130481647277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17018394800468086987764851 25527592200702130481647277)
              ·
                refine ⟨9572847075263298930617729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25527592200702130481647277 9572847075263298930617729)
                ·
                  refine ⟨7179635306447474197963297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9572847075263298930617729 7179635306447474197963297)
                  ·
                    refine ⟨5384726479835605648472473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179635306447474197963297 5384726479835605648472473)
                    ·
                      refine ⟨4038544859876704236354355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384726479835605648472473 4038544859876704236354355)
                      ·
                        rfl

theorem cell23_7865038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_7865038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865038 prefixEnd_7865038 := by exact prefixLift 7865038
  have htrace : WordTrace (prefixWord ++ tailWord_7865038) baseStart_7865038 baseEnd_7865038 := by
    simpa [prefixWord, tailWord_7865038, baseEnd_7865038] using wordTrace_append hprefix tailTrace_7865038
  have hstable : (prefixWord ++ tailWord_7865038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865038).length < 2 ^ (prefixWord ++ tailWord_7865038).sum := by decide
  have hdescent : baseEnd_7865038 < baseStart_7865038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865074 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_7865074 : Nat := 118140960795 + 7865074 * 2 ^ 59
def prefixEnd_7865074 : Nat := 4983230072969 + 3 ^ 40 * 7865074 * 2
def baseEnd_7865074 : Nat := 1346187781726755365168063

theorem tailTrace_7865074 : CollatzResearch.WordTrace tailWord_7865074 prefixEnd_7865074 1346187781726755365168063 := by
  unfold tailWord_7865074
  simp only [CollatzResearch.WordTrace]
  refine ⟨71715703877046905135724569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191241877005458413695265517 71715703877046905135724569)
  ·
    refine ⟨53786777907785178851793427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71715703877046905135724569 53786777907785178851793427)
    ·
      refine ⟨80680166861677768277690141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53786777907785178851793427 80680166861677768277690141)
      ·
        refine ⟨30255062573129163104133803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80680166861677768277690141 30255062573129163104133803)
        ·
          refine ⟨45382593859693744656200705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30255062573129163104133803 45382593859693744656200705)
          ·
            refine ⟨34036945394770308492150529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45382593859693744656200705 34036945394770308492150529)
            ·
              refine ⟨25527709046077731369112897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34036945394770308492150529 25527709046077731369112897)
              ·
                refine ⟨19145781784558298526834673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25527709046077731369112897 19145781784558298526834673)
                ·
                  refine ⟨14359336338418723895126005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19145781784558298526834673 14359336338418723895126005)
                  ·
                    refine ⟨1346187781726755365168063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14359336338418723895126005 1346187781726755365168063)
                    ·
                      rfl

theorem cell23_7865074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_7865074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865074 prefixEnd_7865074 := by exact prefixLift 7865074
  have htrace : WordTrace (prefixWord ++ tailWord_7865074) baseStart_7865074 baseEnd_7865074 := by
    simpa [prefixWord, tailWord_7865074, baseEnd_7865074] using wordTrace_append hprefix tailTrace_7865074
  have hstable : (prefixWord ++ tailWord_7865074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865074).length < 2 ^ (prefixWord ++ tailWord_7865074).sum := by decide
  have hdescent : baseEnd_7865074 < baseStart_7865074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865114 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_7865114 : Nat := 118140960795 + 7865114 * 2 ^ 59
def prefixEnd_7865114 : Nat := 4983230072969 + 3 ^ 40 * 7865114 * 2
def baseEnd_7865114 : Nat := 4038583884406445939004005

theorem tailTrace_7865114 : CollatzResearch.WordTrace tailWord_7865114 prefixEnd_7865114 4038583884406445939004005 := by
  unfold tailWord_7865114
  simp only [CollatzResearch.WordTrace]
  refine ⟨71716068607010676843588599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191242849618695138249569597 71716068607010676843588599)
  ·
    refine ⟨107574102910516015265382899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71716068607010676843588599 107574102910516015265382899)
    ·
      refine ⟨161361154365774022898074349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107574102910516015265382899 161361154365774022898074349)
      ·
        refine ⟨60510432887165258586777881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161361154365774022898074349 60510432887165258586777881)
        ·
          refine ⟨45382824665373943940083411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60510432887165258586777881 45382824665373943940083411)
          ·
            refine ⟨68074236998060915910125117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45382824665373943940083411 68074236998060915910125117)
            ·
              refine ⟨25527838874272843466296919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68074236998060915910125117 25527838874272843466296919)
              ·
                refine ⟨38291758311409265199445379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25527838874272843466296919 38291758311409265199445379)
                ·
                  refine ⟨57437637467113897799168069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38291758311409265199445379 57437637467113897799168069)
                  ·
                    refine ⟨10769557025083855837344013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57437637467113897799168069 10769557025083855837344013)
                    ·
                      refine ⟨4038583884406445939004005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769557025083855837344013 4038583884406445939004005)
                      ·
                        rfl

theorem cell23_7865114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_7865114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865114 prefixEnd_7865114 := by exact prefixLift 7865114
  have htrace : WordTrace (prefixWord ++ tailWord_7865114) baseStart_7865114 baseEnd_7865114 := by
    simpa [prefixWord, tailWord_7865114, baseEnd_7865114] using wordTrace_append hprefix tailTrace_7865114
  have hstable : (prefixWord ++ tailWord_7865114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865114).length < 2 ^ (prefixWord ++ tailWord_7865114).sum := by decide
  have hdescent : baseEnd_7865114 < baseStart_7865114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865137 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_7865137 : Nat := 118140960795 + 7865137 * 2 ^ 59
def prefixEnd_7865137 : Nat := 4983230072969 + 3 ^ 40 * 7865137 * 2
def baseEnd_7865137 : Nat := 4038595694461499349016399

theorem tailTrace_7865137 : CollatzResearch.WordTrace tailWord_7865137 prefixEnd_7865137 4038595694461499349016399 := by
  unfold tailWord_7865137
  simp only [CollatzResearch.WordTrace]
  refine ⟨286865113306959382302441665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191243408871306254868294443 286865113306959382302441665)
  ·
    refine ⟨215148834980219536726831249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286865113306959382302441665 215148834980219536726831249)
    ·
      refine ⟨161361626235164652545123437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215148834980219536726831249 161361626235164652545123437)
      ·
        refine ⟨60510609838186744704421289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161361626235164652545123437 60510609838186744704421289)
        ·
          refine ⟨45382957378640058528315967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60510609838186744704421289 45382957378640058528315967)
          ·
            refine ⟨68074436067960087792473951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45382957378640058528315967 68074436067960087792473951)
            ·
              refine ⟨102111654101940131688710927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68074436067960087792473951 102111654101940131688710927)
              ·
                refine ⟨153167481152910197533066391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102111654101940131688710927 153167481152910197533066391)
                ·
                  refine ⟨229751221729365296299599587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153167481152910197533066391 229751221729365296299599587)
                  ·
                    refine ⟨344626832594047944449399381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229751221729365296299599587 344626832594047944449399381)
                    ·
                      refine ⟨4038595694461499349016399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 344626832594047944449399381 4038595694461499349016399)
                      ·
                        rfl

theorem cell23_7865137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_7865137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865137 prefixEnd_7865137 := by exact prefixLift 7865137
  have htrace : WordTrace (prefixWord ++ tailWord_7865137) baseStart_7865137 baseEnd_7865137 := by
    simpa [prefixWord, tailWord_7865137, baseEnd_7865137] using wordTrace_append hprefix tailTrace_7865137
  have hstable : (prefixWord ++ tailWord_7865137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865137).length < 2 ^ (prefixWord ++ tailWord_7865137).sum := by decide
  have hdescent : baseEnd_7865137 < baseStart_7865137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865151 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 6]
def baseStart_7865151 : Nat := 118140960795 + 7865151 * 2 ^ 59
def prefixEnd_7865151 : Nat := 4983230072969 + 3 ^ 40 * 7865151 * 2
def baseEnd_7865151 : Nat := 448733653687851366026815

theorem tailTrace_7865151 : CollatzResearch.WordTrace tailWord_7865151 prefixEnd_7865151 448733653687851366026815 := by
  unfold tailWord_7865151
  simp only [CollatzResearch.WordTrace]
  refine ⟨286865623928908662693451307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191243749285939108462300871 286865623928908662693451307)
  ·
    refine ⟨430298435893362994040176961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286865623928908662693451307 430298435893362994040176961)
    ·
      refine ⟨322723826920022245530132721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430298435893362994040176961 322723826920022245530132721)
      ·
        refine ⟨242042870190016684147599541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322723826920022245530132721 242042870190016684147599541)
        ·
          refine ⟨22691519080314064138837457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242042870190016684147599541 22691519080314064138837457)
          ·
            refine ⟨17018639310235548104128093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22691519080314064138837457 17018639310235548104128093)
            ·
              refine ⟨6381989741338330539048035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17018639310235548104128093 6381989741338330539048035)
              ·
                refine ⟨9572984612007495808572053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381989741338330539048035 9572984612007495808572053)
                ·
                  refine ⟨448733653687851366026815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9572984612007495808572053 448733653687851366026815)
                  ·
                    rfl

theorem cell23_7865151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 6].length) (baseStart_7865151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865151 prefixEnd_7865151 := by exact prefixLift 7865151
  have htrace : WordTrace (prefixWord ++ tailWord_7865151) baseStart_7865151 baseEnd_7865151 := by
    simpa [prefixWord, tailWord_7865151, baseEnd_7865151] using wordTrace_append hprefix tailTrace_7865151
  have hstable : (prefixWord ++ tailWord_7865151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865151).length < 2 ^ (prefixWord ++ tailWord_7865151).sum := by decide
  have hdescent : baseEnd_7865151 < baseStart_7865151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865161 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 3]
def baseStart_7865161 : Nat := 118140960795 + 7865161 * 2 ^ 59
def prefixEnd_7865161 : Nat := 4983230072969 + 3 ^ 40 * 7865161 * 2
def baseEnd_7865161 : Nat := 4038608017997207255116289

theorem tailTrace_7865161 : CollatzResearch.WordTrace tailWord_7865161 prefixEnd_7865161 4038608017997207255116289 := by
  unfold tailWord_7865161
  simp only [CollatzResearch.WordTrace]
  refine ⟨286865988658872434401315337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191243992439248289600876891 286865988658872434401315337)
  ·
    refine ⟨215149491494154325800986503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286865988658872434401315337 215149491494154325800986503)
    ·
      refine ⟨322724237241231488701479755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215149491494154325800986503 322724237241231488701479755)
      ·
        refine ⟨484086355861847233052219633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322724237241231488701479755 484086355861847233052219633)
        ·
          refine ⟨363064766896385424789164725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484086355861847233052219633 363064766896385424789164725)
          ·
            refine ⟨34037321896536133573984193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 363064766896385424789164725 34037321896536133573984193)
            ·
              refine ⟨25527991422402100180488145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34037321896536133573984193 25527991422402100180488145)
              ·
                refine ⟨19145993566801575135366109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25527991422402100180488145 19145993566801575135366109)
                ·
                  refine ⟨7179747587550590675762291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19145993566801575135366109 7179747587550590675762291)
                  ·
                    refine ⟨10769621381325886013643437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7179747587550590675762291 10769621381325886013643437)
                    ·
                      refine ⟨4038608017997207255116289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769621381325886013643437 4038608017997207255116289)
                      ·
                        rfl

theorem cell23_7865161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_7865161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865161 prefixEnd_7865161 := by exact prefixLift 7865161
  have htrace : WordTrace (prefixWord ++ tailWord_7865161) baseStart_7865161 baseEnd_7865161 := by
    simpa [prefixWord, tailWord_7865161, baseEnd_7865161] using wordTrace_append hprefix tailTrace_7865161
  have hstable : (prefixWord ++ tailWord_7865161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865161).length < 2 ^ (prefixWord ++ tailWord_7865161).sum := by decide
  have hdescent : baseEnd_7865161 < baseStart_7865161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865167 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_7865167 : Nat := 118140960795 + 7865167 * 2 ^ 59
def prefixEnd_7865167 : Nat := 4983230072969 + 3 ^ 40 * 7865167 * 2
def baseEnd_7865167 : Nat := 4038611098881134231641261

theorem tailTrace_7865167 : CollatzResearch.WordTrace tailWord_7865167 prefixEnd_7865167 4038611098881134231641261 := by
  unfold tailWord_7865167
  simp only [CollatzResearch.WordTrace]
  refine ⟨286866207496850697426033755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191244138331233798284022503 286866207496850697426033755)
  ·
    refine ⟨430299311245276046139050633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286866207496850697426033755 430299311245276046139050633)
    ·
      refine ⟨322724483433957034604287975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430299311245276046139050633 322724483433957034604287975)
      ·
        refine ⟨484086725150935551906431963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322724483433957034604287975 484086725150935551906431963)
        ·
          refine ⟨726130087726403327859647945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484086725150935551906431963 726130087726403327859647945)
          ·
            refine ⟨544597565794802495894735959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726130087726403327859647945 544597565794802495894735959)
            ·
              refine ⟨816896348692203743842103939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544597565794802495894735959 816896348692203743842103939)
              ·
                refine ⟨1225344523038305615763155909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816896348692203743842103939 1225344523038305615763155909)
                ·
                  refine ⟨229752098069682302955591733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225344523038305615763155909 229752098069682302955591733)
                  ·
                    refine ⟨21539259194032715902086725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229752098069682302955591733 21539259194032715902086725)
                    ·
                      refine ⟨4038611098881134231641261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21539259194032715902086725 4038611098881134231641261)
                      ·
                        rfl

theorem cell23_7865167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_7865167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865167 prefixEnd_7865167 := by exact prefixLift 7865167
  have htrace : WordTrace (prefixWord ++ tailWord_7865167) baseStart_7865167 baseEnd_7865167 := by
    simpa [prefixWord, tailWord_7865167, baseEnd_7865167] using wordTrace_append hprefix tailTrace_7865167
  have hstable : (prefixWord ++ tailWord_7865167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865167).length < 2 ^ (prefixWord ++ tailWord_7865167).sum := by decide
  have hdescent : baseEnd_7865167 < baseStart_7865167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865172 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_7865172 : Nat := 118140960795 + 7865172 * 2 ^ 59
def prefixEnd_7865172 : Nat := 4983230072969 + 3 ^ 40 * 7865172 * 2
def baseEnd_7865172 : Nat := 1346204555428135570692913

theorem tailTrace_7865172 : CollatzResearch.WordTrace tailWord_7865172 prefixEnd_7865172 1346204555428135570692913 := by
  unfold tailWord_7865172
  simp only [CollatzResearch.WordTrace]
  refine ⟨143433194930916291639982885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191244259907888388853310513 143433194930916291639982885)
  ·
    refine ⟨26893724049546804682496791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143433194930916291639982885 26893724049546804682496791)
    ·
      refine ⟨40340586074320207023745187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26893724049546804682496791 40340586074320207023745187)
      ·
        refine ⟨60510879111480310535617781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40340586074320207023745187 60510879111480310535617781)
        ·
          refine ⟨5672894916701279112714167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60510879111480310535617781 5672894916701279112714167)
          ·
            refine ⟨8509342375051918669071251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672894916701279112714167 8509342375051918669071251)
            ·
              refine ⟨12764013562577878003606877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509342375051918669071251 12764013562577878003606877)
              ·
                refine ⟨4786505085966704251352579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12764013562577878003606877 4786505085966704251352579)
                ·
                  refine ⟨7179757628950056377028869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786505085966704251352579 7179757628950056377028869)
                  ·
                    refine ⟨1346204555428135570692913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7179757628950056377028869 1346204555428135570692913)
                    ·
                      rfl

theorem cell23_7865172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_7865172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865172 prefixEnd_7865172 := by exact prefixLift 7865172
  have htrace : WordTrace (prefixWord ++ tailWord_7865172) baseStart_7865172 baseEnd_7865172 := by
    simpa [prefixWord, tailWord_7865172, baseEnd_7865172] using wordTrace_append hprefix tailTrace_7865172
  have hstable : (prefixWord ++ tailWord_7865172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865172).length < 2 ^ (prefixWord ++ tailWord_7865172).sum := by decide
  have hdescent : baseEnd_7865172 < baseStart_7865172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865188 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_7865188 : Nat := 118140960795 + 7865188 * 2 ^ 59
def prefixEnd_7865188 : Nat := 4983230072969 + 3 ^ 40 * 7865188 * 2
def baseEnd_7865188 : Nat := 4038621881974878649478665

theorem tailTrace_7865188 : CollatzResearch.WordTrace tailWord_7865188 prefixEnd_7865188 4038621881974878649478665 := by
  unfold tailWord_7865188
  simp only [CollatzResearch.WordTrace]
  refine ⟨143433486714887309006274109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191244648953183078675032145 143433486714887309006274109)
  ·
    refine ⟨53787557518082740877352791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143433486714887309006274109 53787557518082740877352791)
    ·
      refine ⟨80681336277124111316029187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53787557518082740877352791 80681336277124111316029187)
      ·
        refine ⟨121022004415686166974043781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80681336277124111316029187 121022004415686166974043781)
        ·
          refine ⟨22691625827941156307633209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121022004415686166974043781 22691625827941156307633209)
          ·
            refine ⟨17018719370955867230724907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22691625827941156307633209 17018719370955867230724907)
            ·
              refine ⟨25528079056433800846087361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17018719370955867230724907 25528079056433800846087361)
              ·
                refine ⟨19146059292325350634565521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25528079056433800846087361 19146059292325350634565521)
                ·
                  refine ⟨14359544469244012975924141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19146059292325350634565521 14359544469244012975924141)
                  ·
                    refine ⟨5384829175966504865971553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14359544469244012975924141 5384829175966504865971553)
                    ·
                      refine ⟨4038621881974878649478665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384829175966504865971553 4038621881974878649478665)
                      ·
                        rfl

theorem cell23_7865188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_7865188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865188 prefixEnd_7865188 := by exact prefixLift 7865188
  have htrace : WordTrace (prefixWord ++ tailWord_7865188) baseStart_7865188 baseEnd_7865188 := by
    simpa [prefixWord, tailWord_7865188, baseEnd_7865188] using wordTrace_append hprefix tailTrace_7865188
  have hstable : (prefixWord ++ tailWord_7865188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865188).length < 2 ^ (prefixWord ++ tailWord_7865188).sum := by decide
  have hdescent : baseEnd_7865188 < baseStart_7865188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865221 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_7865221 : Nat := 118140960795 + 7865221 * 2 ^ 59
def prefixEnd_7865221 : Nat := 4983230072969 + 3 ^ 40 * 7865221 * 2
def baseEnd_7865221 : Nat := 4038638826836477020366013

theorem tailTrace_7865221 : CollatzResearch.WordTrace tailWord_7865221 prefixEnd_7865221 4038638826836477020366013 := by
  unfold tailWord_7865221
  simp only [CollatzResearch.WordTrace]
  refine ⟨286868177038655064648499517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191245451359103376432333011 286868177038655064648499517)
  ·
    refine ⟨107575566389495649243187319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286868177038655064648499517 107575566389495649243187319)
    ·
      refine ⟨161363349584243473864780979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107575566389495649243187319 161363349584243473864780979)
      ·
        refine ⟨242045024376365210797171469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161363349584243473864780979 242045024376365210797171469)
        ·
          refine ⟨90766884141136954048939301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242045024376365210797171469 90766884141136954048939301)
          ·
            refine ⟨17018790776463178884176119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90766884141136954048939301 17018790776463178884176119)
            ·
              refine ⟨25528186164694768326264179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17018790776463178884176119 25528186164694768326264179)
              ·
                refine ⟨38292279247042152489396269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25528186164694768326264179 38292279247042152489396269)
                ·
                  refine ⟨14359604717640807183523601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38292279247042152489396269 14359604717640807183523601)
                  ·
                    refine ⟨10769703538230605387642701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14359604717640807183523601 10769703538230605387642701)
                    ·
                      refine ⟨4038638826836477020366013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769703538230605387642701 4038638826836477020366013)
                      ·
                        rfl

theorem cell23_7865221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_7865221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865221 prefixEnd_7865221 := by exact prefixLift 7865221
  have htrace : WordTrace (prefixWord ++ tailWord_7865221) baseStart_7865221 baseEnd_7865221 := by
    simpa [prefixWord, tailWord_7865221, baseEnd_7865221] using wordTrace_append hprefix tailTrace_7865221
  have hstable : (prefixWord ++ tailWord_7865221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865221).length < 2 ^ (prefixWord ++ tailWord_7865221).sum := by decide
  have hdescent : baseEnd_7865221 < baseStart_7865221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865224 : List Nat := [2, 1, 3, 3, 2, 1, 2, 9]
def baseStart_7865224 : Nat := 118140960795 + 7865224 * 2 ^ 59
def prefixEnd_7865224 : Nat := 4983230072969 + 3 ^ 40 * 7865224 * 2
def baseEnd_7865224 : Nat := 149579272862164463282537

theorem tailTrace_7865224 : CollatzResearch.WordTrace tailWord_7865224 prefixEnd_7865224 149579272862164463282537 := by
  unfold tailWord_7865224
  simp only [CollatzResearch.WordTrace]
  refine ⟨143434143228822098080429363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191245524305096130773905817 143434143228822098080429363)
  ·
    refine ⟨215151214843233147120644045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143434143228822098080429363 215151214843233147120644045)
    ·
      refine ⟨80681705566212430170241517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215151214843233147120644045 80681705566212430170241517)
      ·
        refine ⟨30255639587329661313840569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80681705566212430170241517 30255639587329661313840569)
        ·
          refine ⟨22691729690497245985380427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30255639587329661313840569 22691729690497245985380427)
          ·
            refine ⟨34037594535745868978070641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22691729690497245985380427 34037594535745868978070641)
            ·
              refine ⟨25528195901809401733552981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34037594535745868978070641 25528195901809401733552981)
              ·
                refine ⟨149579272862164463282537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25528195901809401733552981 149579272862164463282537)
                ·
                  rfl

theorem cell23_7865224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 9].length) (baseStart_7865224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865224 prefixEnd_7865224 := by exact prefixLift 7865224
  have htrace : WordTrace (prefixWord ++ tailWord_7865224) baseStart_7865224 baseEnd_7865224 := by
    simpa [prefixWord, tailWord_7865224, baseEnd_7865224] using wordTrace_append hprefix tailTrace_7865224
  have hstable : (prefixWord ++ tailWord_7865224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865224).length < 2 ^ (prefixWord ++ tailWord_7865224).sum := by decide
  have hdescent : baseEnd_7865224 < baseStart_7865224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865251 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 3]
def baseStart_7865251 : Nat := 118140960795 + 7865251 * 2 ^ 59
def prefixEnd_7865251 : Nat := 4983230072969 + 3 ^ 40 * 7865251 * 2
def baseEnd_7865251 : Nat := 4038654231256111902990875

theorem tailTrace_7865251 : CollatzResearch.WordTrace tailWord_7865251 prefixEnd_7865251 4038654231256111902990875 := by
  unfold tailWord_7865251
  simp only [CollatzResearch.WordTrace]
  refine ⟨286869271228546379772091607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191246180819030919848061071 286869271228546379772091607)
  ·
    refine ⟨430303906842819569658137411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286869271228546379772091607 430303906842819569658137411)
    ·
      refine ⟨645455860264229354487206117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430303906842819569658137411 645455860264229354487206117)
      ·
        refine ⟨121022973799543003966351147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 645455860264229354487206117 121022973799543003966351147)
        ·
          refine ⟨181534460699314505949526721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121022973799543003966351147 181534460699314505949526721)
          ·
            refine ⟨136150845524485879462145041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181534460699314505949526721 136150845524485879462145041)
            ·
              refine ⟨102113134143364409596608781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136150845524485879462145041 102113134143364409596608781)
              ·
                refine ⟨38292425303761653598728293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102113134143364409596608781 38292425303761653598728293)
                ·
                  refine ⟨7179829744455310049761555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38292425303761653598728293 7179829744455310049761555)
                  ·
                    refine ⟨10769744616682965074642333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7179829744455310049761555 10769744616682965074642333)
                    ·
                      refine ⟨4038654231256111902990875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769744616682965074642333 4038654231256111902990875)
                      ·
                        rfl

theorem cell23_7865251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_7865251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865251 prefixEnd_7865251 := by exact prefixLift 7865251
  have htrace : WordTrace (prefixWord ++ tailWord_7865251) baseStart_7865251 baseEnd_7865251 := by
    simpa [prefixWord, tailWord_7865251, baseEnd_7865251] using wordTrace_append hprefix tailTrace_7865251
  have hstable : (prefixWord ++ tailWord_7865251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865251).length < 2 ^ (prefixWord ++ tailWord_7865251).sum := by decide
  have hdescent : baseEnd_7865251 < baseStart_7865251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865274 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_7865274 : Nat := 118140960795 + 7865274 * 2 ^ 59
def prefixEnd_7865274 : Nat := 4983230072969 + 3 ^ 40 * 7865274 * 2
def baseEnd_7865274 : Nat := 4038666041311165313003269

theorem tailTrace_7865274 : CollatzResearch.WordTrace tailWord_7865274 prefixEnd_7865274 4038666041311165313003269 := by
  unfold tailWord_7865274
  simp only [CollatzResearch.WordTrace]
  refine ⟨71717527526865763675044719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191246740071642036466785917 71717527526865763675044719)
  ·
    refine ⟨107576291290298645512567079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71717527526865763675044719 107576291290298645512567079)
    ·
      refine ⟨161364436935447968268850619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107576291290298645512567079 161364436935447968268850619)
      ·
        refine ⟨242046655403171952403275929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161364436935447968268850619 242046655403171952403275929)
        ·
          refine ⟨181534991552378964302456947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242046655403171952403275929 181534991552378964302456947)
          ·
            refine ⟨272302487328568446453685421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181534991552378964302456947 272302487328568446453685421)
            ·
              refine ⟨102113432748213167420132033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272302487328568446453685421 102113432748213167420132033)
              ·
                refine ⟨76585074561159875565099025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102113432748213167420132033 76585074561159875565099025)
                ·
                  refine ⟨57438805920869906673824269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76585074561159875565099025 57438805920869906673824269)
                  ·
                    refine ⟨21539552220326215002684101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57438805920869906673824269 21539552220326215002684101)
                    ·
                      refine ⟨4038666041311165313003269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21539552220326215002684101 4038666041311165313003269)
                      ·
                        rfl

theorem cell23_7865274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_7865274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865274 prefixEnd_7865274 := by exact prefixLift 7865274
  have htrace : WordTrace (prefixWord ++ tailWord_7865274) baseStart_7865274 baseEnd_7865274 := by
    simpa [prefixWord, tailWord_7865274, baseEnd_7865274] using wordTrace_append hprefix tailTrace_7865274
  have hstable : (prefixWord ++ tailWord_7865274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865274).length < 2 ^ (prefixWord ++ tailWord_7865274).sum := by decide
  have hdescent : baseEnd_7865274 < baseStart_7865274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865278 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_7865278 : Nat := 118140960795 + 7865278 * 2 ^ 59
def prefixEnd_7865278 : Nat := 4983230072969 + 3 ^ 40 * 7865278 * 2
def baseEnd_7865278 : Nat := 4038668095233783297353251

theorem tailTrace_7865278 : CollatzResearch.WordTrace tailWord_7865278 prefixEnd_7865278 4038668095233783297353251 := by
  unfold tailWord_7865278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35858781999931070422915561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191246837332965708922216325 35858781999931070422915561)
  ·
    refine ⟨26894086499948302817186671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35858781999931070422915561 26894086499948302817186671)
    ·
      refine ⟨40341129749922454225780007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26894086499948302817186671 40341129749922454225780007)
      ·
        refine ⟨60511694624883681338670011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40341129749922454225780007 60511694624883681338670011)
        ·
          refine ⟨90767541937325522008005017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60511694624883681338670011 90767541937325522008005017)
          ·
            refine ⟨68075656452994141506003763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90767541937325522008005017 68075656452994141506003763)
            ·
              refine ⟨102113484679491212259005645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68075656452994141506003763 102113484679491212259005645)
              ·
                refine ⟨38292556754809204597127117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102113484679491212259005645 38292556754809204597127117)
                ·
                  refine ⟨14359708783053451723922669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38292556754809204597127117 14359708783053451723922669)
                  ·
                    refine ⟨5384890793645044396471001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14359708783053451723922669 5384890793645044396471001)
                    ·
                      refine ⟨4038668095233783297353251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384890793645044396471001 4038668095233783297353251)
                      ·
                        rfl

theorem cell23_7865278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_7865278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865278 prefixEnd_7865278 := by exact prefixLift 7865278
  have htrace : WordTrace (prefixWord ++ tailWord_7865278) baseStart_7865278 baseEnd_7865278 := by
    simpa [prefixWord, tailWord_7865278, baseEnd_7865278] using wordTrace_append hprefix tailTrace_7865278
  have hstable : (prefixWord ++ tailWord_7865278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865278).length < 2 ^ (prefixWord ++ tailWord_7865278).sum := by decide
  have hdescent : baseEnd_7865278 < baseStart_7865278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865295 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 1, 3, 2]
def baseStart_7865295 : Nat := 118140960795 + 7865295 * 2 ^ 59
def prefixEnd_7865295 : Nat := 4983230072969 + 3 ^ 40 * 7865295 * 2
def baseEnd_7865295 : Nat := 4038676824404909730840673

theorem tailTrace_7865295 : CollatzResearch.WordTrace tailWord_7865295 prefixEnd_7865295 4038676824404909730840673 := by
  unfold tailWord_7865295
  simp only [CollatzResearch.WordTrace]
  refine ⟨286870876040386975286693339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191247250693591316857795559 286870876040386975286693339)
  ·
    refine ⟨430306314060580462930040009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286870876040386975286693339 430306314060580462930040009)
    ·
      refine ⟨322729735545435347197530007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430306314060580462930040009 322729735545435347197530007)
      ·
        refine ⟨484094603318153020796295011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322729735545435347197530007 484094603318153020796295011)
        ·
          refine ⟨726141904977229531194442517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484094603318153020796295011 726141904977229531194442517)
          ·
            refine ⟨34037901795807634274739493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 726141904977229531194442517 34037901795807634274739493)
            ·
              refine ⟨6382106586713931426513655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34037901795807634274739493 6382106586713931426513655)
              ·
                refine ⟨9573159880070897139770483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382106586713931426513655 9573159880070897139770483)
                ·
                  refine ⟨14359739820106345709655725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573159880070897139770483 14359739820106345709655725)
                  ·
                    refine ⟨5384902432539879641120897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14359739820106345709655725 5384902432539879641120897)
                    ·
                      refine ⟨4038676824404909730840673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384902432539879641120897 4038676824404909730840673)
                      ·
                        rfl

theorem cell23_7865295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 3, 2].length) (baseStart_7865295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865295 prefixEnd_7865295 := by exact prefixLift 7865295
  have htrace : WordTrace (prefixWord ++ tailWord_7865295) baseStart_7865295 baseEnd_7865295 := by
    simpa [prefixWord, tailWord_7865295, baseEnd_7865295] using wordTrace_append hprefix tailTrace_7865295
  have hstable : (prefixWord ++ tailWord_7865295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865295).length < 2 ^ (prefixWord ++ tailWord_7865295).sum := by decide
  have hdescent : baseEnd_7865295 < baseStart_7865295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865302 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_7865302 : Nat := 118140960795 + 7865302 * 2 ^ 59
def prefixEnd_7865302 : Nat := 4983230072969 + 3 ^ 40 * 7865302 * 2
def baseEnd_7865302 : Nat := 4038680418769491203453141

theorem tailTrace_7865302 : CollatzResearch.WordTrace tailWord_7865302 prefixEnd_7865302 4038680418769491203453141 := by
  unfold tailWord_7865302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17929445709460100967637385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191247420900907743654798773 17929445709460100967637385)
  ·
    refine ⟨13447084282095075725728039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17929445709460100967637385 13447084282095075725728039)
    ·
      refine ⟨20170626423142613588592059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13447084282095075725728039 20170626423142613588592059)
      ·
        refine ⟨30255939634713920382888089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20170626423142613588592059 30255939634713920382888089)
        ·
          refine ⟨22691954726035440287166067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30255939634713920382888089 22691954726035440287166067)
          ·
            refine ⟨34037932089053160430749101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22691954726035440287166067 34037932089053160430749101)
            ·
              refine ⟨12764224533394935161530913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34037932089053160430749101 12764224533394935161530913)
              ·
                refine ⟨9573168400046201371148185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12764224533394935161530913 9573168400046201371148185)
                ·
                  refine ⟨7179876300034651028361139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9573168400046201371148185 7179876300034651028361139)
                  ·
                    refine ⟨10769814450051976542541709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7179876300034651028361139 10769814450051976542541709)
                    ·
                      refine ⟨4038680418769491203453141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769814450051976542541709 4038680418769491203453141)
                      ·
                        rfl

theorem cell23_7865302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_7865302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865302 prefixEnd_7865302 := by exact prefixLift 7865302
  have htrace : WordTrace (prefixWord ++ tailWord_7865302) baseStart_7865302 baseEnd_7865302 := by
    simpa [prefixWord, tailWord_7865302, baseEnd_7865302] using wordTrace_append hprefix tailTrace_7865302
  have hstable : (prefixWord ++ tailWord_7865302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865302).length < 2 ^ (prefixWord ++ tailWord_7865302).sum := by decide
  have hdescent : baseEnd_7865302 < baseStart_7865302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865365 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 5]
def baseStart_7865365 : Nat := 118140960795 + 7865365 * 2 ^ 59
def prefixEnd_7865365 : Nat := 4983230072969 + 3 ^ 40 * 7865365 * 2
def baseEnd_7865365 : Nat := 448745863116747161885039

theorem tailTrace_7865365 : CollatzResearch.WordTrace tailWord_7865365 prefixEnd_7865365 448745863116747161885039 := by
  unfold tailWord_7865365
  simp only [CollatzResearch.WordTrace]
  refine ⟨286873429150133377241741549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191248952766755584827827699 286873429150133377241741549)
  ·
    refine ⟨107577535931300016465653081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286873429150133377241741549 107577535931300016465653081)
    ·
      refine ⟨80683151948475012349239811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107577535931300016465653081 80683151948475012349239811)
      ·
        refine ⟨121024727922712518523859717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80683151948475012349239811 121024727922712518523859717)
        ·
          refine ⟨22692136485508597223223697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121024727922712518523859717 22692136485508597223223697)
          ·
            refine ⟨17019102364131447917417773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22692136485508597223223697 17019102364131447917417773)
            ·
              refine ⟨6382163386549292969031665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17019102364131447917417773 6382163386549292969031665)
              ·
                refine ⟨4786622539911969726773749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6382163386549292969031665 4786622539911969726773749)
                ·
                  refine ⟨448745863116747161885039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786622539911969726773749 448745863116747161885039)
                  ·
                    rfl

theorem cell23_7865365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_7865365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865365 prefixEnd_7865365 := by exact prefixLift 7865365
  have htrace : WordTrace (prefixWord ++ tailWord_7865365) baseStart_7865365 baseEnd_7865365 := by
    simpa [prefixWord, tailWord_7865365, baseEnd_7865365] using wordTrace_append hprefix tailTrace_7865365
  have hstable : (prefixWord ++ tailWord_7865365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865365).length < 2 ^ (prefixWord ++ tailWord_7865365).sum := by decide
  have hdescent : baseEnd_7865365 < baseStart_7865365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865376 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7865376 : Nat := 118140960795 + 7865376 * 2 ^ 59
def prefixEnd_7865376 : Nat := 4983230072969 + 3 ^ 40 * 7865376 * 2
def baseEnd_7865376 : Nat := 4038718416337923913927801

theorem tailTrace_7865376 : CollatzResearch.WordTrace tailWord_7865376 prefixEnd_7865376 4038718416337923913927801 := by
  unfold tailWord_7865376
  simp only [CollatzResearch.WordTrace]
  refine ⟨143436915176546763060195991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191249220235395684080261321 143436915176546763060195991)
  ·
    refine ⟨215155372764820144590293987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143436915176546763060195991 215155372764820144590293987)
    ·
      refine ⟨322733059147230216885440981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215155372764820144590293987 322733059147230216885440981)
      ·
        refine ⟨7564056073763208208252523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 322733059147230216885440981 7564056073763208208252523)
        ·
          refine ⟨11346084110644812312378785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564056073763208208252523 11346084110644812312378785)
          ·
            refine ⟨8509563082983609234284089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11346084110644812312378785 8509563082983609234284089)
            ·
              refine ⟨6382172312237706925713067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8509563082983609234284089 6382172312237706925713067)
              ·
                refine ⟨9573258468356560388569601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382172312237706925713067 9573258468356560388569601)
                ·
                  refine ⟨7179943851267420291427201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9573258468356560388569601 7179943851267420291427201)
                  ·
                    refine ⟨5384957888450565218570401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179943851267420291427201 5384957888450565218570401)
                    ·
                      refine ⟨4038718416337923913927801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5384957888450565218570401 4038718416337923913927801)
                      ·
                        rfl

theorem cell23_7865376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7865376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865376 prefixEnd_7865376 := by exact prefixLift 7865376
  have htrace : WordTrace (prefixWord ++ tailWord_7865376) baseStart_7865376 baseEnd_7865376 := by
    simpa [prefixWord, tailWord_7865376, baseEnd_7865376] using wordTrace_append hprefix tailTrace_7865376
  have hstable : (prefixWord ++ tailWord_7865376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865376).length < 2 ^ (prefixWord ++ tailWord_7865376).sum := by decide
  have hdescent : baseEnd_7865376 < baseStart_7865376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865381 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_7865381 : Nat := 118140960795 + 7865381 * 2 ^ 59
def prefixEnd_7865381 : Nat := 4983230072969 + 3 ^ 40 * 7865381 * 2
def baseEnd_7865381 : Nat := 4038720983741196394365277

theorem tailTrace_7865381 : CollatzResearch.WordTrace tailWord_7865381 prefixEnd_7865381 4038720983741196394365277 := by
  unfold tailWord_7865381
  simp only [CollatzResearch.WordTrace]
  refine ⟨286874012718075411974323997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191249341812050274649549331 286874012718075411974323997)
  ·
    refine ⟨107577754769278279490371499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286874012718075411974323997 107577754769278279490371499)
    ·
      refine ⟨161366632153917419235557249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107577754769278279490371499 161366632153917419235557249)
      ·
        refine ⟨121024974115438064426667937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161366632153917419235557249 121024974115438064426667937)
        ·
          refine ⟨90768730586578548320000953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121024974115438064426667937 90768730586578548320000953)
          ·
            refine ⟨68076547939933911240000715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90768730586578548320000953 68076547939933911240000715)
            ·
              refine ⟨102114821909900866860001073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68076547939933911240000715 102114821909900866860001073)
              ·
                refine ⟨76586116432425650145000805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102114821909900866860001073 76586116432425650145000805)
                ·
                  refine ⟨14359896831079809402187651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76586116432425650145000805 14359896831079809402187651)
                  ·
                    refine ⟨21539845246619714103281477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14359896831079809402187651 21539845246619714103281477)
                    ·
                      refine ⟨4038720983741196394365277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21539845246619714103281477 4038720983741196394365277)
                      ·
                        rfl

theorem cell23_7865381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_7865381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865381 prefixEnd_7865381 := by exact prefixLift 7865381
  have htrace : WordTrace (prefixWord ++ tailWord_7865381) baseStart_7865381 baseEnd_7865381 := by
    simpa [prefixWord, tailWord_7865381, baseEnd_7865381] using wordTrace_append hprefix tailTrace_7865381
  have hstable : (prefixWord ++ tailWord_7865381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865381).length < 2 ^ (prefixWord ++ tailWord_7865381).sum := by decide
  have hdescent : baseEnd_7865381 < baseStart_7865381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865418 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_7865418 : Nat := 118140960795 + 7865418 * 2 ^ 59
def prefixEnd_7865418 : Nat := 4983230072969 + 3 ^ 40 * 7865418 * 2
def baseEnd_7865418 : Nat := 4038739982525412749602607

theorem tailTrace_7865418 : CollatzResearch.WordTrace tailWord_7865418 prefixEnd_7865418 4038739982525412749602607 := by
  unfold tailWord_7865418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71718840554735341823355227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191250241479294244862280605 71718840554735341823355227)
  ·
    refine ⟨107578260832103012735032841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71718840554735341823355227 107578260832103012735032841)
    ·
      refine ⟨80683695624077259551274631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107578260832103012735032841 80683695624077259551274631)
      ·
        refine ⟨121025543436115889326911947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80683695624077259551274631 121025543436115889326911947)
        ·
          refine ⟨181538315154173833990367921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121025543436115889326911947 181538315154173833990367921)
          ·
            refine ⟨136153736365630375492775941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181538315154173833990367921 136153736365630375492775941)
            ·
              refine ⟨25528825568555695404895489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136153736365630375492775941 25528825568555695404895489)
              ·
                refine ⟨19146619176416771553671617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25528825568555695404895489 19146619176416771553671617)
                ·
                  refine ⟨14359964382312578665253713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19146619176416771553671617 14359964382312578665253713)
                  ·
                    refine ⟨10769973286734433998940285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14359964382312578665253713 10769973286734433998940285)
                    ·
                      refine ⟨4038739982525412749602607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769973286734433998940285 4038739982525412749602607)
                      ·
                        rfl

theorem cell23_7865418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_7865418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865418 prefixEnd_7865418 := by exact prefixLift 7865418
  have htrace : WordTrace (prefixWord ++ tailWord_7865418) baseStart_7865418 baseEnd_7865418 := by
    simpa [prefixWord, tailWord_7865418, baseEnd_7865418] using wordTrace_append hprefix tailTrace_7865418
  have hstable : (prefixWord ++ tailWord_7865418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865418).length < 2 ^ (prefixWord ++ tailWord_7865418).sum := by decide
  have hdescent : baseEnd_7865418 < baseStart_7865418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865431 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_7865431 : Nat := 118140960795 + 7865431 * 2 ^ 59
def prefixEnd_7865431 : Nat := 4983230072969 + 3 ^ 40 * 7865431 * 2
def baseEnd_7865431 : Nat := 4038746657773921198740047

theorem tailTrace_7865431 : CollatzResearch.WordTrace tailWord_7865431 prefixEnd_7865431 4038746657773921198740047 := by
  unfold tailWord_7865431
  simp only [CollatzResearch.WordTrace]
  refine ⟨286875836367894270513644147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191250557578596180342429431 286875836367894270513644147)
  ·
    refine ⟨430313754551841405770466221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286875836367894270513644147 430313754551841405770466221)
    ·
      refine ⟨161367657956940527163924833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430313754551841405770466221 161367657956940527163924833)
      ·
        refine ⟨121025743467705395372943625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161367657956940527163924833 121025743467705395372943625)
        ·
          refine ⟨90769307600779046529707719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121025743467705395372943625 90769307600779046529707719)
          ·
            refine ⟨136153961401168569794561579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90769307600779046529707719 136153961401168569794561579)
            ·
              refine ⟨204230942101752854691842369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136153961401168569794561579 204230942101752854691842369)
              ·
                refine ⟨153173206576314641018881777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204230942101752854691842369 153173206576314641018881777)
                ·
                  refine ⟨114879904932235980764161333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153173206576314641018881777 114879904932235980764161333)
                  ·
                    refine ⟨10769991087397123196640125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114879904932235980764161333 10769991087397123196640125)
                    ·
                      refine ⟨4038746657773921198740047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10769991087397123196640125 4038746657773921198740047)
                      ·
                        rfl

theorem cell23_7865431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_7865431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865431 prefixEnd_7865431 := by exact prefixLift 7865431
  have htrace : WordTrace (prefixWord ++ tailWord_7865431) baseStart_7865431 baseEnd_7865431 := by
    simpa [prefixWord, tailWord_7865431, baseEnd_7865431] using wordTrace_append hprefix tailTrace_7865431
  have hstable : (prefixWord ++ tailWord_7865431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865431).length < 2 ^ (prefixWord ++ tailWord_7865431).sum := by decide
  have hdescent : baseEnd_7865431 < baseStart_7865431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865468 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_7865468 : Nat := 118140960795 + 7865468 * 2 ^ 59
def prefixEnd_7865468 : Nat := 4983230072969 + 3 ^ 40 * 7865468 * 2
def baseEnd_7865468 : Nat := 1346255218852712517992459

theorem tailTrace_7865468 : CollatzResearch.WordTrace tailWord_7865468 prefixEnd_7865468 1346255218852712517992459 := by
  unfold tailWord_7865468
  simp only [CollatzResearch.WordTrace]
  refine ⟨143438592934380112916370529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191251457245840150555160705 143438592934380112916370529)
  ·
    refine ⟨107578944700785084687277897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143438592934380112916370529 107578944700785084687277897)
    ·
      refine ⟨80684208525588813515458423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107578944700785084687277897 80684208525588813515458423)
      ·
        refine ⟨121026312788383220273187635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80684208525588813515458423 121026312788383220273187635)
        ·
          refine ⟨181539469182574830409781453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121026312788383220273187635 181539469182574830409781453)
          ·
            refine ⟨68077300943465561403668045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181539469182574830409781453 68077300943465561403668045)
            ·
              refine ⟨25528987853799585526375517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68077300943465561403668045 25528987853799585526375517)
              ·
                refine ⟨9573370445174844572390819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25528987853799585526375517 9573370445174844572390819)
                ·
                  refine ⟨14360055667762266858586229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573370445174844572390819 14360055667762266858586229)
                  ·
                    refine ⟨1346255218852712517992459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14360055667762266858586229 1346255218852712517992459)
                    ·
                      rfl

theorem cell23_7865468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_7865468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865468 prefixEnd_7865468 := by exact prefixLift 7865468
  have htrace : WordTrace (prefixWord ++ tailWord_7865468) baseStart_7865468 baseEnd_7865468 := by
    simpa [prefixWord, tailWord_7865468, baseEnd_7865468] using wordTrace_append hprefix tailTrace_7865468
  have hstable : (prefixWord ++ tailWord_7865468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865468).length < 2 ^ (prefixWord ++ tailWord_7865468).sum := by decide
  have hdescent : baseEnd_7865468 < baseStart_7865468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865482 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_7865482 : Nat := 118140960795 + 7865482 * 2 ^ 59
def prefixEnd_7865482 : Nat := 4983230072969 + 3 ^ 40 * 7865482 * 2
def baseEnd_7865482 : Nat := 4038772845287300499202313

theorem tailTrace_7865482 : CollatzResearch.WordTrace tailWord_7865482 prefixEnd_7865482 4038772845287300499202313 := by
  unfold tailWord_7865482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71719424122677376555937675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191251797660473004149167133 71719424122677376555937675)
  ·
    refine ⟨107579136184016064833906513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71719424122677376555937675 107579136184016064833906513)
    ·
      refine ⟨80684352138012048625429885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107579136184016064833906513 80684352138012048625429885)
      ·
        refine ⟨30256632051754518234536207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80684352138012048625429885 30256632051754518234536207)
        ·
          refine ⟨45384948077631777351804311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30256632051754518234536207 45384948077631777351804311)
          ·
            refine ⟨68077422116447666027706467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45384948077631777351804311 68077422116447666027706467)
            ·
              refine ⟨102116133174671499041559701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68077422116447666027706467 102116133174671499041559701)
              ·
                refine ⟨4786693742562726517573111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102116133174671499041559701 4786693742562726517573111)
                ·
                  refine ⟨7180040613844089776359667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786693742562726517573111 7180040613844089776359667)
                  ·
                    refine ⟨10770060920766134664539501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7180040613844089776359667 10770060920766134664539501)
                    ·
                      refine ⟨4038772845287300499202313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10770060920766134664539501 4038772845287300499202313)
                      ·
                        rfl

theorem cell23_7865482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_7865482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865482 prefixEnd_7865482 := by exact prefixLift 7865482
  have htrace : WordTrace (prefixWord ++ tailWord_7865482) baseStart_7865482 baseEnd_7865482 := by
    simpa [prefixWord, tailWord_7865482, baseEnd_7865482] using wordTrace_append hprefix tailTrace_7865482
  have hstable : (prefixWord ++ tailWord_7865482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865482).length < 2 ^ (prefixWord ++ tailWord_7865482).sum := by decide
  have hdescent : baseEnd_7865482 < baseStart_7865482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865491 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5]
def baseStart_7865491 : Nat := 118140960795 + 7865491 * 2 ^ 59
def prefixEnd_7865491 : Nat := 4983230072969 + 3 ^ 40 * 7865491 * 2
def baseEnd_7865491 : Nat := 4038777466613190963989771

theorem tailTrace_7865491 : CollatzResearch.WordTrace tailWord_7865491 prefixEnd_7865491 4038777466613190963989771 := by
  unfold tailWord_7865491
  simp only [CollatzResearch.WordTrace]
  refine ⟨286878024747676900760828327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191252016498451267173885551 286878024747676900760828327)
  ·
    refine ⟨430317037121515351141242491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286878024747676900760828327 430317037121515351141242491)
    ·
      refine ⟨645475555682273026711863737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430317037121515351141242491 645475555682273026711863737)
      ·
        refine ⟨484106666761704770033897803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645475555682273026711863737 484106666761704770033897803)
        ·
          refine ⟨726160000142557155050846705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484106666761704770033897803 726160000142557155050846705)
          ·
            refine ⟨544620000106917866288135029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726160000142557155050846705 544620000106917866288135029)
            ·
              refine ⟨51058125010023549964512659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 544620000106917866288135029 51058125010023549964512659)
              ·
                refine ⟨76587187515035324946768989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51058125010023549964512659 76587187515035324946768989)
                ·
                  refine ⟨28720195318138246855038371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76587187515035324946768989 28720195318138246855038371)
                  ·
                    refine ⟨43080292977207370282557557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28720195318138246855038371 43080292977207370282557557)
                    ·
                      refine ⟨4038777466613190963989771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43080292977207370282557557 4038777466613190963989771)
                      ·
                        rfl

theorem cell23_7865491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_7865491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865491 prefixEnd_7865491 := by exact prefixLift 7865491
  have htrace : WordTrace (prefixWord ++ tailWord_7865491) baseStart_7865491 baseEnd_7865491 := by
    simpa [prefixWord, tailWord_7865491, baseEnd_7865491] using wordTrace_append hprefix tailTrace_7865491
  have hstable : (prefixWord ++ tailWord_7865491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865491).length < 2 ^ (prefixWord ++ tailWord_7865491).sum := by decide
  have hdescent : baseEnd_7865491 < baseStart_7865491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865502 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_7865502 : Nat := 118140960795 + 7865502 * 2 ^ 59
def prefixEnd_7865502 : Nat := 4983230072969 + 3 ^ 40 * 7865502 * 2
def baseEnd_7865502 : Nat := 1346261038300130140317407

theorem tailTrace_7865502 : CollatzResearch.WordTrace tailWord_7865502 prefixEnd_7865502 1346261038300130140317407 := by
  unfold tailWord_7865502
  simp only [CollatzResearch.WordTrace]
  refine ⟨35859803243829631204934845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191252283967091366426319173 35859803243829631204934845)
  ·
    refine ⟨13447426216436111701850567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35859803243829631204934845 13447426216436111701850567)
    ·
      refine ⟨20171139324654167552775851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13447426216436111701850567 20171139324654167552775851)
      ·
        refine ⟨30256708986981251329163777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20171139324654167552775851 30256708986981251329163777)
        ·
          refine ⟨22692531740235938496872833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30256708986981251329163777 22692531740235938496872833)
          ·
            refine ⟨17019398805176953872654625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22692531740235938496872833 17019398805176953872654625)
            ·
              refine ⟨12764549103882715404490969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17019398805176953872654625 12764549103882715404490969)
              ·
                refine ⟨9573411827912036553368227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12764549103882715404490969 9573411827912036553368227)
                ·
                  refine ⟨14360117741868054830052341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573411827912036553368227 14360117741868054830052341)
                  ·
                    refine ⟨1346261038300130140317407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14360117741868054830052341 1346261038300130140317407)
                    ·
                      rfl

theorem cell23_7865502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_7865502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865502 prefixEnd_7865502 := by exact prefixLift 7865502
  have htrace : WordTrace (prefixWord ++ tailWord_7865502) baseStart_7865502 baseEnd_7865502 := by
    simpa [prefixWord, tailWord_7865502, baseEnd_7865502] using wordTrace_append hprefix tailTrace_7865502
  have hstable : (prefixWord ++ tailWord_7865502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865502).length < 2 ^ (prefixWord ++ tailWord_7865502).sum := by decide
  have hdescent : baseEnd_7865502 < baseStart_7865502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865505 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7865505 : Nat := 118140960795 + 7865505 * 2 ^ 59
def prefixEnd_7865505 : Nat := 4983230072969 + 3 ^ 40 * 7865505 * 2
def baseEnd_7865505 : Nat := 4038784655342353909214707

theorem tailTrace_7865505 : CollatzResearch.WordTrace tailWord_7865505 prefixEnd_7865505 4038784655342353909214707 := by
  unfold tailWord_7865505
  simp only [CollatzResearch.WordTrace]
  refine ⟨286878535369626181151837969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191252356913084120767891979 286878535369626181151837969)
  ·
    refine ⟨215158901527219635863878477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286878535369626181151837969 215158901527219635863878477)
    ·
      refine ⟨80684588072707363448954429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215158901527219635863878477 80684588072707363448954429)
      ·
        refine ⟨30256720527265261293357911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80684588072707363448954429 30256720527265261293357911)
        ·
          refine ⟨45385080790897891940036867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30256720527265261293357911 45385080790897891940036867)
          ·
            refine ⟨68077621186346837910055301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45385080790897891940036867 68077621186346837910055301)
            ·
              refine ⟨12764553972440032108135369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68077621186346837910055301 12764553972440032108135369)
              ·
                refine ⟨9573415479330024081101527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12764553972440032108135369 9573415479330024081101527)
                ·
                  refine ⟨14360123218995036121652291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573415479330024081101527 14360123218995036121652291)
                  ·
                    refine ⟨21540184828492554182478437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14360123218995036121652291 21540184828492554182478437)
                    ·
                      refine ⟨4038784655342353909214707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21540184828492554182478437 4038784655342353909214707)
                      ·
                        rfl

theorem cell23_7865505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7865505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865505 prefixEnd_7865505 := by exact prefixLift 7865505
  have htrace : WordTrace (prefixWord ++ tailWord_7865505) baseStart_7865505 baseEnd_7865505 := by
    simpa [prefixWord, tailWord_7865505, baseEnd_7865505] using wordTrace_append hprefix tailTrace_7865505
  have hstable : (prefixWord ++ tailWord_7865505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865505).length < 2 ^ (prefixWord ++ tailWord_7865505).sum := by decide
  have hdescent : baseEnd_7865505 < baseStart_7865505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865526 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7865526 : Nat := 118140960795 + 7865526 * 2 ^ 59
def prefixEnd_7865526 : Nat := 4983230072969 + 3 ^ 40 * 7865526 * 2
def baseEnd_7865526 : Nat := 4038795438436098327052111

theorem tailTrace_7865526 : CollatzResearch.WordTrace tailWord_7865526 prefixEnd_7865526 4038795438436098327052111 := by
  unfold tailWord_7865526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17929956331409381358647027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191252867535033401158901621 17929956331409381358647027)
  ·
    refine ⟨26894934497114072037970541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17929956331409381358647027 26894934497114072037970541)
    ·
      refine ⟨10085600436417777014238953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26894934497114072037970541 10085600436417777014238953)
      ·
        refine ⟨7564200327313332760679215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10085600436417777014238953 7564200327313332760679215)
        ·
          refine ⟨11346300490969999141018823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564200327313332760679215 11346300490969999141018823)
          ·
            refine ⟨17019450736454998711528235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11346300490969999141018823 17019450736454998711528235)
            ·
              refine ⟨25529176104682498067292353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17019450736454998711528235 25529176104682498067292353)
              ·
                refine ⟨19146882078511873550469265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25529176104682498067292353 19146882078511873550469265)
                ·
                  refine ⟨14360161558883905162851949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19146882078511873550469265 14360161558883905162851949)
                  ·
                    refine ⟨5385060584581464436069481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14360161558883905162851949 5385060584581464436069481)
                    ·
                      refine ⟨4038795438436098327052111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385060584581464436069481 4038795438436098327052111)
                      ·
                        rfl

theorem cell23_7865526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7865526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865526 prefixEnd_7865526 := by exact prefixLift 7865526
  have htrace : WordTrace (prefixWord ++ tailWord_7865526) baseStart_7865526 baseEnd_7865526 := by
    simpa [prefixWord, tailWord_7865526, baseEnd_7865526] using wordTrace_append hprefix tailTrace_7865526
  have hstable : (prefixWord ++ tailWord_7865526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865526).length < 2 ^ (prefixWord ++ tailWord_7865526).sum := by decide
  have hdescent : baseEnd_7865526 < baseStart_7865526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865541 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_7865541 : Nat := 118140960795 + 7865541 * 2 ^ 59
def prefixEnd_7865541 : Nat := 4983230072969 + 3 ^ 40 * 7865541 * 2
def baseEnd_7865541 : Nat := 1346267713548638589454847

theorem tailTrace_7865541 : CollatzResearch.WordTrace tailWord_7865541 prefixEnd_7865541 1346267713548638589454847 := by
  unfold tailWord_7865541
  simp only [CollatzResearch.WordTrace]
  refine ⟨286879848397495759300148477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191253232264997172866765651 286879848397495759300148477)
  ·
    refine ⟨107579943149060909737555679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286879848397495759300148477 107579943149060909737555679)
    ·
      refine ⟨161369914723591364606333519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107579943149060909737555679 161369914723591364606333519)
      ·
        refine ⟨242054872085387046909500279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161369914723591364606333519 242054872085387046909500279)
        ·
          refine ⟨363082308128080570364250419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242054872085387046909500279 363082308128080570364250419)
          ·
            refine ⟨544623462192120855546375629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363082308128080570364250419 544623462192120855546375629)
            ·
              refine ⟨204233798322045320829890861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544623462192120855546375629 204233798322045320829890861)
              ·
                refine ⟨76587674370766995311209073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204233798322045320829890861 76587674370766995311209073)
                ·
                  refine ⟨57440755778075246483406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76587674370766995311209073 57440755778075246483406805)
                  ·
                    refine ⟨1346267713548638589454847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57440755778075246483406805 1346267713548638589454847)
                    ·
                      rfl

theorem cell23_7865541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_7865541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865541 prefixEnd_7865541 := by exact prefixLift 7865541
  have htrace : WordTrace (prefixWord ++ tailWord_7865541) baseStart_7865541 baseEnd_7865541 := by
    simpa [prefixWord, tailWord_7865541, baseEnd_7865541] using wordTrace_append hprefix tailTrace_7865541
  have hstable : (prefixWord ++ tailWord_7865541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865541).length < 2 ^ (prefixWord ++ tailWord_7865541).sum := by decide
  have hdescent : baseEnd_7865541 < baseStart_7865541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865551 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_7865551 : Nat := 118140960795 + 7865551 * 2 ^ 59
def prefixEnd_7865551 : Nat := 4983230072969 + 3 ^ 40 * 7865551 * 2
def baseEnd_7865551 : Nat := 4038808275452460729239495

theorem tailTrace_7865551 : CollatzResearch.WordTrace tailWord_7865551 prefixEnd_7865551 4038808275452460729239495 := by
  unfold tailWord_7865551
  simp only [CollatzResearch.WordTrace]
  refine ⟨286880213127459531008012507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191253475418306354005341671 286880213127459531008012507)
  ·
    refine ⟨430320319691189296512018761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286880213127459531008012507 430320319691189296512018761)
    ·
      refine ⟨322740239768391972384014071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430320319691189296512018761 322740239768391972384014071)
      ·
        refine ⟨484110359652587958576021107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322740239768391972384014071 484110359652587958576021107)
        ·
          refine ⟨726165539478881937864031661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484110359652587958576021107 726165539478881937864031661)
          ·
            refine ⟨272312077304580726699011873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726165539478881937864031661 272312077304580726699011873)
            ·
              refine ⟨204234057978435545024258905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272312077304580726699011873 204234057978435545024258905)
              ·
                refine ⟨153175543483826658768194179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204234057978435545024258905 153175543483826658768194179)
                ·
                  refine ⟨229763315225739988152291269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153175543483826658768194179 229763315225739988152291269)
                  ·
                    refine ⟨43080621604826247778554613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229763315225739988152291269 43080621604826247778554613)
                    ·
                      refine ⟨4038808275452460729239495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43080621604826247778554613 4038808275452460729239495)
                      ·
                        rfl

theorem cell23_7865551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_7865551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865551 prefixEnd_7865551 := by exact prefixLift 7865551
  have htrace : WordTrace (prefixWord ++ tailWord_7865551) baseStart_7865551 baseEnd_7865551 := by
    simpa [prefixWord, tailWord_7865551, baseEnd_7865551] using wordTrace_append hprefix tailTrace_7865551
  have hstable : (prefixWord ++ tailWord_7865551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865551).length < 2 ^ (prefixWord ++ tailWord_7865551).sum := by decide
  have hdescent : baseEnd_7865551 < baseStart_7865551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865555 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 3]
def baseStart_7865555 : Nat := 118140960795 + 7865555 * 2 ^ 59
def prefixEnd_7865555 : Nat := 4983230072969 + 3 ^ 40 * 7865555 * 2
def baseEnd_7865555 : Nat := 4038810329375078713589477

theorem tailTrace_7865555 : CollatzResearch.WordTrace tailWord_7865555 prefixEnd_7865555 4038810329375078713589477 := by
  unfold tailWord_7865555
  simp only [CollatzResearch.WordTrace]
  refine ⟨286880359019445039691158119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191253572679630026460772079 286880359019445039691158119)
  ·
    refine ⟨430320538529167559536737179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286880359019445039691158119 430320538529167559536737179)
    ·
      refine ⟨645480807793751339305105769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430320538529167559536737179 645480807793751339305105769)
      ·
        refine ⟨484110605845313504478829327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645480807793751339305105769 484110605845313504478829327)
        ·
          refine ⟨726165908767970256718243991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484110605845313504478829327 726165908767970256718243991)
          ·
            refine ⟨1089248863151955385077365987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726165908767970256718243991 1089248863151955385077365987)
            ·
              refine ⟨1633873294727933077616048981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089248863151955385077365987 1633873294727933077616048981)
              ·
                refine ⟨9573476336296482876656537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1633873294727933077616048981 9573476336296482876656537)
                ·
                  refine ⟨7180107252222362157492403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9573476336296482876656537 7180107252222362157492403)
                  ·
                    refine ⟨10770160878333543236238605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7180107252222362157492403 10770160878333543236238605)
                    ·
                      refine ⟨4038810329375078713589477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10770160878333543236238605 4038810329375078713589477)
                      ·
                        rfl

theorem cell23_7865555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_7865555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865555 prefixEnd_7865555 := by exact prefixLift 7865555
  have htrace : WordTrace (prefixWord ++ tailWord_7865555) baseStart_7865555 baseEnd_7865555 := by
    simpa [prefixWord, tailWord_7865555, baseEnd_7865555] using wordTrace_append hprefix tailTrace_7865555
  have hstable : (prefixWord ++ tailWord_7865555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865555).length < 2 ^ (prefixWord ++ tailWord_7865555).sum := by decide
  have hdescent : baseEnd_7865555 < baseStart_7865555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865556 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7865556 : Nat := 118140960795 + 7865556 * 2 ^ 59
def prefixEnd_7865556 : Nat := 4983230072969 + 3 ^ 40 * 7865556 * 2
def baseEnd_7865556 : Nat := 4038810842855733209676973

theorem tailTrace_7865556 : CollatzResearch.WordTrace tailWord_7865556 prefixEnd_7865556 4038810842855733209676973 := by
  unfold tailWord_7865556
  simp only [CollatzResearch.WordTrace]
  refine ⟨143440197746220708430972261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191253596994960944574629681 143440197746220708430972261)
  ·
    refine ⟨26895037077416382830807299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143440197746220708430972261 26895037077416382830807299)
    ·
      refine ⟨40342555616124574246210949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26895037077416382830807299 40342555616124574246210949)
      ·
        refine ⟨7564229178023357671164553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40342555616124574246210949 7564229178023357671164553)
        ·
          refine ⟨5673171883517518253373415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7564229178023357671164553 5673171883517518253373415)
          ·
            refine ⟨8509757825276277380060123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673171883517518253373415 8509757825276277380060123)
            ·
              refine ⟨12764636737914416070090185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509757825276277380060123 12764636737914416070090185)
              ·
                refine ⟨9573477553435812052567639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12764636737914416070090185 9573477553435812052567639)
                ·
                  refine ⟨14360216330153718078851459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573477553435812052567639 14360216330153718078851459)
                  ·
                    refine ⟨21540324495230577118277189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14360216330153718078851459 21540324495230577118277189)
                    ·
                      refine ⟨4038810842855733209676973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21540324495230577118277189 4038810842855733209676973)
                      ·
                        rfl

theorem cell23_7865556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7865556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865556 prefixEnd_7865556 := by exact prefixLift 7865556
  have htrace : WordTrace (prefixWord ++ tailWord_7865556) baseStart_7865556 baseEnd_7865556 := by
    simpa [prefixWord, tailWord_7865556, baseEnd_7865556] using wordTrace_append hprefix tailTrace_7865556
  have hstable : (prefixWord ++ tailWord_7865556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865556).length < 2 ^ (prefixWord ++ tailWord_7865556).sum := by decide
  have hdescent : baseEnd_7865556 < baseStart_7865556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865561 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_7865561 : Nat := 118140960795 + 7865561 * 2 ^ 59
def prefixEnd_7865561 : Nat := 4983230072969 + 3 ^ 40 * 7865561 * 2
def baseEnd_7865561 : Nat := 4038813410259005690114449

theorem tailTrace_7865561 : CollatzResearch.WordTrace tailWord_7865561 prefixEnd_7865561 4038813410259005690114449 := by
  unfold tailWord_7865561
  simp only [CollatzResearch.WordTrace]
  refine ⟨286880577857423302715876537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191253718571615535143917691 286880577857423302715876537)
  ·
    refine ⟨215160433393067477036907403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286880577857423302715876537 215160433393067477036907403)
    ·
      refine ⟨322740650089601215555361105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215160433393067477036907403 322740650089601215555361105)
      ·
        refine ⟨242055487567200911666520829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322740650089601215555361105 242055487567200911666520829)
        ·
          refine ⟨90770807837700341874945311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242055487567200911666520829 90770807837700341874945311)
          ·
            refine ⟨136156211756550512812417967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90770807837700341874945311 136156211756550512812417967)
            ·
              refine ⟨204234317634825769218626951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136156211756550512812417967 204234317634825769218626951)
              ·
                refine ⟨306351476452238653827940427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204234317634825769218626951 306351476452238653827940427)
                ·
                  refine ⟨459527214678357980741910641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306351476452238653827940427 459527214678357980741910641)
                  ·
                    refine ⟨344645411008768485556432981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 459527214678357980741910641 344645411008768485556432981)
                    ·
                      refine ⟨4038813410259005690114449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 344645411008768485556432981 4038813410259005690114449)
                      ·
                        rfl

theorem cell23_7865561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_7865561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865561 prefixEnd_7865561 := by exact prefixLift 7865561
  have htrace : WordTrace (prefixWord ++ tailWord_7865561) baseStart_7865561 baseEnd_7865561 := by
    simpa [prefixWord, tailWord_7865561, baseEnd_7865561] using wordTrace_append hprefix tailTrace_7865561
  have hstable : (prefixWord ++ tailWord_7865561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865561).length < 2 ^ (prefixWord ++ tailWord_7865561).sum := by decide
  have hdescent : baseEnd_7865561 < baseStart_7865561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865582 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_7865582 : Nat := 118140960795 + 7865582 * 2 ^ 59
def prefixEnd_7865582 : Nat := 4983230072969 + 3 ^ 40 * 7865582 * 2
def baseEnd_7865582 : Nat := 4038824193352750107951853

theorem tailTrace_7865582 : CollatzResearch.WordTrace tailWord_7865582 prefixEnd_7865582 4038824193352750107951853 := by
  unfold tailWord_7865582
  simp only [CollatzResearch.WordTrace]
  refine ⟨35860167973793402912798875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191254229193564815534927333 35860167973793402912798875)
  ·
    refine ⟨53790251960690104369198313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35860167973793402912798875 53790251960690104369198313)
    ·
      refine ⟨40342688970517578276898735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53790251960690104369198313 40342688970517578276898735)
      ·
        refine ⟨60514033455776367415348103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40342688970517578276898735 60514033455776367415348103)
        ·
          refine ⟨90771050183664551123022155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60514033455776367415348103 90771050183664551123022155)
          ·
            refine ⟨136156575275496826684533233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90771050183664551123022155 136156575275496826684533233)
            ·
              refine ⟨102117431456622620013399925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136156575275496826684533233 102117431456622620013399925)
              ·
                refine ⟨9573509199058370626256243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102117431456622620013399925 9573509199058370626256243)
                ·
                  refine ⟨14360263798587555939384365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573509199058370626256243 14360263798587555939384365)
                  ·
                    refine ⟨5385098924470333477269137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14360263798587555939384365 5385098924470333477269137)
                    ·
                      refine ⟨4038824193352750107951853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385098924470333477269137 4038824193352750107951853)
                      ·
                        rfl

theorem cell23_7865582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_7865582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865582 prefixEnd_7865582 := by exact prefixLift 7865582
  have htrace : WordTrace (prefixWord ++ tailWord_7865582) baseStart_7865582 baseEnd_7865582 := by
    simpa [prefixWord, tailWord_7865582, baseEnd_7865582] using wordTrace_append hprefix tailTrace_7865582
  have hstable : (prefixWord ++ tailWord_7865582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865582).length < 2 ^ (prefixWord ++ tailWord_7865582).sum := by decide
  have hdescent : baseEnd_7865582 < baseStart_7865582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865612 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 1, 4, 2]
def baseStart_7865612 : Nat := 118140960795 + 7865612 * 2 ^ 59
def prefixEnd_7865612 : Nat := 4983230072969 + 3 ^ 40 * 7865612 * 2
def baseEnd_7865612 : Nat := 4038839597772384990576715

theorem tailTrace_7865612 : CollatzResearch.WordTrace tailWord_7865612 prefixEnd_7865612 4038839597772384990576715 := by
  unfold tailWord_7865612
  simp only [CollatzResearch.WordTrace]
  refine ⟨143441218990119269212991545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191254958653492358950655393 143441218990119269212991545)
  ·
    refine ⟨107580914242589451909743659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143441218990119269212991545 107580914242589451909743659)
    ·
      refine ⟨161371371363884177864615489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107580914242589451909743659 161371371363884177864615489)
      ·
        refine ⟨121028528522913133398461617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161371371363884177864615489 121028528522913133398461617)
        ·
          refine ⟨90771396392184850048846213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121028528522913133398461617 90771396392184850048846213)
          ·
            refine ⟨17019636823534659384158665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90771396392184850048846213 17019636823534659384158665)
            ·
              refine ⟨12764727617650994538118999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17019636823534659384158665 12764727617650994538118999)
              ·
                refine ⟨19147091426476491807178499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12764727617650994538118999 19147091426476491807178499)
                ·
                  refine ⟨28720637139714737710767749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19147091426476491807178499 28720637139714737710767749)
                  ·
                    refine ⟨5385119463696513320768953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28720637139714737710767749 5385119463696513320768953)
                    ·
                      refine ⟨4038839597772384990576715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385119463696513320768953 4038839597772384990576715)
                      ·
                        rfl

theorem cell23_7865612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_7865612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865612 prefixEnd_7865612 := by exact prefixLift 7865612
  have htrace : WordTrace (prefixWord ++ tailWord_7865612) baseStart_7865612 baseEnd_7865612 := by
    simpa [prefixWord, tailWord_7865612, baseEnd_7865612] using wordTrace_append hprefix tailTrace_7865612
  have hstable : (prefixWord ++ tailWord_7865612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865612).length < 2 ^ (prefixWord ++ tailWord_7865612).sum := by decide
  have hdescent : baseEnd_7865612 < baseStart_7865612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865635 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 5]
def baseStart_7865635 : Nat := 118140960795 + 7865635 * 2 ^ 59
def prefixEnd_7865635 : Nat := 4983230072969 + 3 ^ 40 * 7865635 * 2
def baseEnd_7865635 : Nat := 448761267536382044509901

theorem tailTrace_7865635 : CollatzResearch.WordTrace tailWord_7865635 prefixEnd_7865635 448761267536382044509901 := by
  unfold tailWord_7865635
  simp only [CollatzResearch.WordTrace]
  refine ⟨286883276859155213354070359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191255517906103475569380239 286883276859155213354070359)
  ·
    refine ⟨430324915288732820031105539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286883276859155213354070359 430324915288732820031105539)
    ·
      refine ⟨645487372933099230046658309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430324915288732820031105539 645487372933099230046658309)
      ·
        refine ⟨121028882424956105633748433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 645487372933099230046658309 121028882424956105633748433)
        ·
          refine ⟨90771661818717079225311325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121028882424956105633748433 90771661818717079225311325)
          ·
            refine ⟨34039373182018904709491747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90771661818717079225311325 34039373182018904709491747)
            ·
              refine ⟨51059059773028357064237621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34039373182018904709491747 51059059773028357064237621)
              ·
                refine ⟨4786786853721408474772277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51059059773028357064237621 4786786853721408474772277)
                ·
                  refine ⟨448761267536382044509901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786786853721408474772277 448761267536382044509901)
                  ·
                    rfl

theorem cell23_7865635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 5].length) (baseStart_7865635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865635 prefixEnd_7865635 := by exact prefixLift 7865635
  have htrace : WordTrace (prefixWord ++ tailWord_7865635) baseStart_7865635 baseEnd_7865635 := by
    simpa [prefixWord, tailWord_7865635, baseEnd_7865635] using wordTrace_append hprefix tailTrace_7865635
  have hstable : (prefixWord ++ tailWord_7865635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865635).length < 2 ^ (prefixWord ++ tailWord_7865635).sum := by decide
  have hdescent : baseEnd_7865635 < baseStart_7865635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865648 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_7865648 : Nat := 118140960795 + 7865648 * 2 ^ 59
def prefixEnd_7865648 : Nat := 4983230072969 + 3 ^ 40 * 7865648 * 2
def baseEnd_7865648 : Nat := 1346286027691982283242183

theorem tailTrace_7865648 : CollatzResearch.WordTrace tailWord_7865648 prefixEnd_7865648 1346286027691982283242183 := by
  unfold tailWord_7865648
  simp only [CollatzResearch.WordTrace]
  refine ⟨143441875504054058287146799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191255834005405411049529065 143441875504054058287146799)
  ·
    refine ⟨215162813256081087430720199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143441875504054058287146799 215162813256081087430720199)
    ·
      refine ⟨322744219884121631146080299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215162813256081087430720199 322744219884121631146080299)
      ·
        refine ⟨484116329826182446719120449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322744219884121631146080299 484116329826182446719120449)
        ·
          refine ⟨363087247369636835039340337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484116329826182446719120449 363087247369636835039340337)
          ·
            refine ⟨272315435527227626279505253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363087247369636835039340337 272315435527227626279505253)
            ·
              refine ⟨51059144161355179927407235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272315435527227626279505253 51059144161355179927407235)
              ·
                refine ⟨76588716242032769891110853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51059144161355179927407235 76588716242032769891110853)
                ·
                  refine ⟨14360384295381144354583285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76588716242032769891110853 14360384295381144354583285)
                  ·
                    refine ⟨1346286027691982283242183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14360384295381144354583285 1346286027691982283242183)
                    ·
                      rfl

theorem cell23_7865648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_7865648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865648 prefixEnd_7865648 := by exact prefixLift 7865648
  have htrace : WordTrace (prefixWord ++ tailWord_7865648) baseStart_7865648 baseEnd_7865648 := by
    simpa [prefixWord, tailWord_7865648, baseEnd_7865648] using wordTrace_append hprefix tailTrace_7865648
  have hstable : (prefixWord ++ tailWord_7865648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865648).length < 2 ^ (prefixWord ++ tailWord_7865648).sum := by decide
  have hdescent : baseEnd_7865648 < baseStart_7865648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865652 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 5]
def baseStart_7865652 : Nat := 118140960795 + 7865652 * 2 ^ 59
def prefixEnd_7865652 : Nat := 4983230072969 + 3 ^ 40 * 7865652 * 2
def baseEnd_7865652 : Nat := 448762237444284981564059

theorem tailTrace_7865652 : CollatzResearch.WordTrace tailWord_7865652 prefixEnd_7865652 448762237444284981564059 := by
  unfold tailWord_7865652
  simp only [CollatzResearch.WordTrace]
  refine ⟨143441948450046812628719605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191255931266729083504959473 143441948450046812628719605)
  ·
    refine ⟨13447682667191888683942463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143441948450046812628719605 13447682667191888683942463)
    ·
      refine ⟨20171524000787833025913695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13447682667191888683942463 20171524000787833025913695)
      ·
        refine ⟨30257286001181749538870543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20171524000787833025913695 30257286001181749538870543)
        ·
          refine ⟨45385929001772624308305815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30257286001181749538870543 45385929001772624308305815)
          ·
            refine ⟨68078893502658936462458723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45385929001772624308305815 68078893502658936462458723)
            ·
              refine ⟨102118340253988404693688085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68078893502658936462458723 102118340253988404693688085)
              ·
                refine ⟨4786797199405706470016629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102118340253988404693688085 4786797199405706470016629)
                ·
                  refine ⟨448762237444284981564059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786797199405706470016629 448762237444284981564059)
                  ·
                    rfl

theorem cell23_7865652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_7865652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865652 prefixEnd_7865652 := by exact prefixLift 7865652
  have htrace : WordTrace (prefixWord ++ tailWord_7865652) baseStart_7865652 baseEnd_7865652 := by
    simpa [prefixWord, tailWord_7865652, baseEnd_7865652] using wordTrace_append hprefix tailTrace_7865652
  have hstable : (prefixWord ++ tailWord_7865652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865652).length < 2 ^ (prefixWord ++ tailWord_7865652).sum := by decide
  have hdescent : baseEnd_7865652 < baseStart_7865652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865658 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_7865658 : Nat := 118140960795 + 7865658 * 2 ^ 59
def prefixEnd_7865658 : Nat := 4983230072969 + 3 ^ 40 * 7865658 * 2
def baseEnd_7865658 : Nat := 4038863217882491810601503

theorem tailTrace_7865658 : CollatzResearch.WordTrace tailWord_7865658 prefixEnd_7865658 4038863217882491810601503 := by
  unfold tailWord_7865658
  simp only [CollatzResearch.WordTrace]
  refine ⟨71721028934517972070539407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191256077158714592188105085 71721028934517972070539407)
  ·
    refine ⟨107581543401776958105809111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71721028934517972070539407 107581543401776958105809111)
    ·
      refine ⟨161372315102665437158713667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107581543401776958105809111 161372315102665437158713667)
      ·
        refine ⟨242058472653998155738070501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161372315102665437158713667 242058472653998155738070501)
        ·
          refine ⟨45385963622624654200888219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242058472653998155738070501 45385963622624654200888219)
          ·
            refine ⟨68078945433936981301332329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45385963622624654200888219 68078945433936981301332329)
            ·
              refine ⟨51059209075452735975999247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68078945433936981301332329 51059209075452735975999247)
              ·
                refine ⟨76588813613179103963998871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51059209075452735975999247 76588813613179103963998871)
                ·
                  refine ⟨114883220419768655945998307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76588813613179103963998871 114883220419768655945998307)
                  ·
                    refine ⟨172324830629652983918997461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114883220419768655945998307 172324830629652983918997461)
                    ·
                      refine ⟨4038863217882491810601503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172324830629652983918997461 4038863217882491810601503)
                      ·
                        rfl

theorem cell23_7865658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_7865658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865658 prefixEnd_7865658 := by exact prefixLift 7865658
  have htrace : WordTrace (prefixWord ++ tailWord_7865658) baseStart_7865658 baseEnd_7865658 := by
    simpa [prefixWord, tailWord_7865658, baseEnd_7865658] using wordTrace_append hprefix tailTrace_7865658
  have hstable : (prefixWord ++ tailWord_7865658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865658).length < 2 ^ (prefixWord ++ tailWord_7865658).sum := by decide
  have hdescent : baseEnd_7865658 < baseStart_7865658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865665 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7865665 : Nat := 118140960795 + 7865665 * 2 ^ 59
def prefixEnd_7865665 : Nat := 4983230072969 + 3 ^ 40 * 7865665 * 2
def baseEnd_7865665 : Nat := 1346288937415691094404657

theorem tailTrace_7865665 : CollatzResearch.WordTrace tailWord_7865665 prefixEnd_7865665 1346288937415691094404657 := by
  unfold tailWord_7865665
  simp only [CollatzResearch.WordTrace]
  refine ⟨286884371049046528477662449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191256247366031018985108299 286884371049046528477662449)
  ·
    refine ⟨215163278286784896358246837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286884371049046528477662449 215163278286784896358246837)
    ·
      refine ⟨20171557339386084033585641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215163278286784896358246837 20171557339386084033585641)
      ·
        refine ⟨15128668004539563025189231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20171557339386084033585641 15128668004539563025189231)
        ·
          refine ⟨22693002006809344537783847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15128668004539563025189231 22693002006809344537783847)
          ·
            refine ⟨34039503010214016806675771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22693002006809344537783847 34039503010214016806675771)
            ·
              refine ⟨51059254515321025210013657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34039503010214016806675771 51059254515321025210013657)
              ·
                refine ⟨38294440886490768907510243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51059254515321025210013657 38294440886490768907510243)
                ·
                  refine ⟨57441661329736153361265365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38294440886490768907510243 57441661329736153361265365)
                  ·
                    refine ⟨1346288937415691094404657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57441661329736153361265365 1346288937415691094404657)
                    ·
                      rfl

theorem cell23_7865665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7865665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865665 prefixEnd_7865665 := by exact prefixLift 7865665
  have htrace : WordTrace (prefixWord ++ tailWord_7865665) baseStart_7865665 baseEnd_7865665 := by
    simpa [prefixWord, tailWord_7865665, baseEnd_7865665] using wordTrace_append hprefix tailTrace_7865665
  have hstable : (prefixWord ++ tailWord_7865665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865665).length < 2 ^ (prefixWord ++ tailWord_7865665).sum := by decide
  have hdescent : baseEnd_7865665 < baseStart_7865665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865678 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_7865678 : Nat := 118140960795 + 7865678 * 2 ^ 59
def prefixEnd_7865678 : Nat := 4983230072969 + 3 ^ 40 * 7865678 * 2
def baseEnd_7865678 : Nat := 1346291162498527244117137

theorem tailTrace_7865678 : CollatzResearch.WordTrace tailWord_7865678 prefixEnd_7865678 1346291162498527244117137 := by
  unfold tailWord_7865678
  simp only [CollatzResearch.WordTrace]
  refine ⟨35860605649749928962235711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191256563465332954465257125 35860605649749928962235711)
  ·
    refine ⟨53790908474624893443353567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35860605649749928962235711 53790908474624893443353567)
    ·
      refine ⟨80686362711937340165030351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53790908474624893443353567 80686362711937340165030351)
      ·
        refine ⟨121029544067906010247545527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80686362711937340165030351 121029544067906010247545527)
        ·
          refine ⟨181544316101859015371318291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121029544067906010247545527 181544316101859015371318291)
          ·
            refine ⟨272316474152788523056977437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181544316101859015371318291 272316474152788523056977437)
            ·
              refine ⟨102118677807295696146366539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272316474152788523056977437 102118677807295696146366539)
              ·
                refine ⟨153178016710943544219549809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102118677807295696146366539 153178016710943544219549809)
                ·
                  refine ⟨114883512533207658164662357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153178016710943544219549809 114883512533207658164662357)
                  ·
                    refine ⟨1346291162498527244117137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114883512533207658164662357 1346291162498527244117137)
                    ·
                      rfl

theorem cell23_7865678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_7865678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865678 prefixEnd_7865678 := by exact prefixLift 7865678
  have htrace : WordTrace (prefixWord ++ tailWord_7865678) baseStart_7865678 baseEnd_7865678 := by
    simpa [prefixWord, tailWord_7865678, baseEnd_7865678] using wordTrace_append hprefix tailTrace_7865678
  have hstable : (prefixWord ++ tailWord_7865678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865678).length < 2 ^ (prefixWord ++ tailWord_7865678).sum := by decide
  have hdescent : baseEnd_7865678 < baseStart_7865678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865685 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7865685 : Nat := 118140960795 + 7865685 * 2 ^ 59
def prefixEnd_7865685 : Nat := 4983230072969 + 3 ^ 40 * 7865685 * 2
def baseEnd_7865685 : Nat := 4038877081860163204963879

theorem tailTrace_7865685 : CollatzResearch.WordTrace tailWord_7865685 prefixEnd_7865685 4038877081860163204963879 := by
  unfold tailWord_7865685
  simp only [CollatzResearch.WordTrace]
  refine ⟨286885100508974071893390509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191256733672649381262260339 286885100508974071893390509)
  ·
    refine ⟨107581912690865276960021441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286885100508974071893390509 107581912690865276960021441)
    ·
      refine ⟨80686434518148957720016081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107581912690865276960021441 80686434518148957720016081)
      ·
        refine ⟨60514825888611718290012061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80686434518148957720016081 60514825888611718290012061)
        ·
          refine ⟨22693059708229394358754523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60514825888611718290012061 22693059708229394358754523)
          ·
            refine ⟨34039589562344091538131785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22693059708229394358754523 34039589562344091538131785)
            ·
              refine ⟨25529692171758068653598839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34039589562344091538131785 25529692171758068653598839)
              ·
                refine ⟨38294538257637102980398259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25529692171758068653598839 38294538257637102980398259)
                ·
                  refine ⟨57441807386455654470597389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38294538257637102980398259 57441807386455654470597389)
                  ·
                    refine ⟨21540677769920870426474021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57441807386455654470597389 21540677769920870426474021)
                    ·
                      refine ⟨4038877081860163204963879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21540677769920870426474021 4038877081860163204963879)
                      ·
                        rfl

theorem cell23_7865685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7865685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865685 prefixEnd_7865685 := by exact prefixLift 7865685
  have htrace : WordTrace (prefixWord ++ tailWord_7865685) baseStart_7865685 baseEnd_7865685 := by
    simpa [prefixWord, tailWord_7865685, baseEnd_7865685] using wordTrace_append hprefix tailTrace_7865685
  have hstable : (prefixWord ++ tailWord_7865685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865685).length < 2 ^ (prefixWord ++ tailWord_7865685).sum := by decide
  have hdescent : baseEnd_7865685 < baseStart_7865685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865725 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 6]
def baseStart_7865725 : Nat := 118140960795 + 7865725 * 2 ^ 59
def prefixEnd_7865725 : Nat := 4983230072969 + 3 ^ 40 * 7865725 * 2
def baseEnd_7865725 : Nat := 448766402342927005384855

theorem tailTrace_7865725 : CollatzResearch.WordTrace tailWord_7865725 prefixEnd_7865725 448766402342927005384855 := by
  unfold tailWord_7865725
  simp only [CollatzResearch.WordTrace]
  refine ⟨286886559428829158724846629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191257706285886105816564419 286886559428829158724846629)
  ·
    refine ⟨53791229892905467260908743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286886559428829158724846629 53791229892905467260908743)
    ·
      refine ⟨80686844839358200891363115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53791229892905467260908743 80686844839358200891363115)
      ·
        refine ⟨121030267259037301337044673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80686844839358200891363115 121030267259037301337044673)
        ·
          refine ⟨90772700444277976002783505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121030267259037301337044673 90772700444277976002783505)
          ·
            refine ⟨68079525333208482002087629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90772700444277976002783505 68079525333208482002087629)
            ·
              refine ⟨25529821999953180750782861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68079525333208482002087629 25529821999953180750782861)
              ·
                refine ⟨9573683249982442781543573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25529821999953180750782861 9573683249982442781543573)
                ·
                  refine ⟨448766402342927005384855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9573683249982442781543573 448766402342927005384855)
                  ·
                    rfl

theorem cell23_7865725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_7865725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865725 prefixEnd_7865725 := by exact prefixLift 7865725
  have htrace : WordTrace (prefixWord ++ tailWord_7865725) baseStart_7865725 baseEnd_7865725 := by
    simpa [prefixWord, tailWord_7865725, baseEnd_7865725] using wordTrace_append hprefix tailTrace_7865725
  have hstable : (prefixWord ++ tailWord_7865725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865725).length < 2 ^ (prefixWord ++ tailWord_7865725).sum := by decide
  have hdescent : baseEnd_7865725 < baseStart_7865725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865728 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_7865728 : Nat := 118140960795 + 7865728 * 2 ^ 59
def prefixEnd_7865728 : Nat := 4983230072969 + 3 ^ 40 * 7865728 * 2
def baseEnd_7865728 : Nat := 4038899161528306536726181

theorem tailTrace_7865728 : CollatzResearch.WordTrace tailWord_7865728 prefixEnd_7865728 4038899161528306536726181 := by
  unfold tailWord_7865728
  simp only [CollatzResearch.WordTrace]
  refine ⟨143443334423909145118602919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191257779231878860158137225 143443334423909145118602919)
  ·
    refine ⟨215165001635863717677904379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143443334423909145118602919 215165001635863717677904379)
    ·
      refine ⟨322747502453795576516856569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215165001635863717677904379 322747502453795576516856569)
      ·
        refine ⟨242060626840346682387642427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322747502453795576516856569 242060626840346682387642427)
        ·
          refine ⟨363090940260520023581463641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242060626840346682387642427 363090940260520023581463641)
          ·
            refine ⟨272318205195390017686097731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363090940260520023581463641 272318205195390017686097731)
            ·
              refine ⟨408477307793085026529146597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272318205195390017686097731 408477307793085026529146597)
              ·
                refine ⟨76589495211203442474214987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408477307793085026529146597 76589495211203442474214987)
                ·
                  refine ⟨114884242816805163711322481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76589495211203442474214987 114884242816805163711322481)
                  ·
                    refine ⟨86163182112603872783491861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114884242816805163711322481 86163182112603872783491861)
                    ·
                      refine ⟨4038899161528306536726181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86163182112603872783491861 4038899161528306536726181)
                      ·
                        rfl

theorem cell23_7865728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_7865728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865728 prefixEnd_7865728 := by exact prefixLift 7865728
  have htrace : WordTrace (prefixWord ++ tailWord_7865728) baseStart_7865728 baseEnd_7865728 := by
    simpa [prefixWord, tailWord_7865728, baseEnd_7865728] using wordTrace_append hprefix tailTrace_7865728
  have hstable : (prefixWord ++ tailWord_7865728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865728).length < 2 ^ (prefixWord ++ tailWord_7865728).sum := by decide
  have hdescent : baseEnd_7865728 < baseStart_7865728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865796 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7865796 : Nat := 118140960795 + 7865796 * 2 ^ 59
def prefixEnd_7865796 : Nat := 4983230072969 + 3 ^ 40 * 7865796 * 2
def baseEnd_7865796 : Nat := 4038934078212812270675869

theorem tailTrace_7865796 : CollatzResearch.WordTrace tailWord_7865796 prefixEnd_7865796 4038934078212812270675869 := by
  unfold tailWord_7865796
  simp only [CollatzResearch.WordTrace]
  refine ⟨143444574505785968925340621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191259432674381291900454161 143444574505785968925340621)
  ·
    refine ⟨53791715439669738347002733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143444574505785968925340621 53791715439669738347002733)
    ·
      refine ⟨20171893289876151880126025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53791715439669738347002733 20171893289876151880126025)
      ·
        refine ⟨15128919967407113910094519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20171893289876151880126025 15128919967407113910094519)
        ·
          refine ⟨22693379951110670865141779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15128919967407113910094519 22693379951110670865141779)
          ·
            refine ⟨34040069926666006297712669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22693379951110670865141779 34040069926666006297712669)
            ·
              refine ⟨12765026222499752361642251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34040069926666006297712669 12765026222499752361642251)
              ·
                refine ⟨19147539333749628542463377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12765026222499752361642251 19147539333749628542463377)
                ·
                  refine ⟨14360654500312221406847533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19147539333749628542463377 14360654500312221406847533)
                  ·
                    refine ⟨5385245437617083027567825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14360654500312221406847533 5385245437617083027567825)
                    ·
                      refine ⟨4038934078212812270675869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385245437617083027567825 4038934078212812270675869)
                      ·
                        rfl

theorem cell23_7865796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7865796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865796 prefixEnd_7865796 := by exact prefixLift 7865796
  have htrace : WordTrace (prefixWord ++ tailWord_7865796) baseStart_7865796 baseEnd_7865796 := by
    simpa [prefixWord, tailWord_7865796, baseEnd_7865796] using wordTrace_append hprefix tailTrace_7865796
  have hstable : (prefixWord ++ tailWord_7865796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865796).length < 2 ^ (prefixWord ++ tailWord_7865796).sum := by decide
  have hdescent : baseEnd_7865796 < baseStart_7865796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865846 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_7865846 : Nat := 118140960795 + 7865846 * 2 ^ 59
def prefixEnd_7865846 : Nat := 4983230072969 + 3 ^ 40 * 7865846 * 2
def baseEnd_7865846 : Nat := 4038959752245537075050639

theorem tailTrace_7865846 : CollatzResearch.WordTrace tailWord_7865846 prefixEnd_7865846 4038959752245537075050639 := by
  unfold tailWord_7865846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17930685791336924774375087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191260648440927197593334261 17930685791336924774375087)
  ·
    refine ⟨26896028687005387161562631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17930685791336924774375087 26896028687005387161562631)
    ·
      refine ⟨40344043030508080742343947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26896028687005387161562631 40344043030508080742343947)
      ·
        refine ⟨60516064545762121113515921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40344043030508080742343947 60516064545762121113515921)
        ·
          refine ⟨45387048409321590835136941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60516064545762121113515921 45387048409321590835136941)
          ·
            refine ⟨17020143153495596563176353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45387048409321590835136941 17020143153495596563176353)
            ·
              refine ⟨12765107365121697422382265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17020143153495596563176353 12765107365121697422382265)
              ·
                refine ⟨9573830523841273066786699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12765107365121697422382265 9573830523841273066786699)
                ·
                  refine ⟨14360745785761909600180049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573830523841273066786699 14360745785761909600180049)
                  ·
                    refine ⟨10770559339321432200135037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14360745785761909600180049 10770559339321432200135037)
                    ·
                      refine ⟨4038959752245537075050639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10770559339321432200135037 4038959752245537075050639)
                      ·
                        rfl

theorem cell23_7865846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_7865846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865846 prefixEnd_7865846 := by exact prefixLift 7865846
  have htrace : WordTrace (prefixWord ++ tailWord_7865846) baseStart_7865846 baseEnd_7865846 := by
    simpa [prefixWord, tailWord_7865846, baseEnd_7865846] using wordTrace_append hprefix tailTrace_7865846
  have hstable : (prefixWord ++ tailWord_7865846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865846).length < 2 ^ (prefixWord ++ tailWord_7865846).sum := by decide
  have hdescent : baseEnd_7865846 < baseStart_7865846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865905 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 9]
def baseStart_7865905 : Nat := 118140960795 + 7865905 * 2 ^ 59
def prefixEnd_7865905 : Nat := 4983230072969 + 3 ^ 40 * 7865905 * 2
def baseEnd_7865905 : Nat := 448776671956016927134763

theorem tailTrace_7865905 : CollatzResearch.WordTrace tailWord_7865905 prefixEnd_7865905 448776671956016927134763 := by
  unfold tailWord_7865905
  simp only [CollatzResearch.WordTrace]
  refine ⟨286893124568177049466399169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191262083045451366310932779 286893124568177049466399169)
  ·
    refine ⟨215169843426132787099799377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286893124568177049466399169 215169843426132787099799377)
    ·
      refine ⟨161377382569599590324849533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215169843426132787099799377 161377382569599590324849533)
      ·
        refine ⟨60516518463599846371818575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161377382569599590324849533 60516518463599846371818575)
        ·
          refine ⟨90774777695399769557727863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60516518463599846371818575 90774777695399769557727863)
          ·
            refine ⟨136162166543099654336591795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90774777695399769557727863 136162166543099654336591795)
            ·
              refine ⟨204243249814649481504887693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136162166543099654336591795 204243249814649481504887693)
              ·
                refine ⟨76591218680493555564332885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204243249814649481504887693 76591218680493555564332885)
                ·
                  refine ⟨448776671956016927134763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76591218680493555564332885 448776671956016927134763)
                  ·
                    rfl

theorem cell23_7865905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_7865905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865905 prefixEnd_7865905 := by exact prefixLift 7865905
  have htrace : WordTrace (prefixWord ++ tailWord_7865905) baseStart_7865905 baseEnd_7865905 := by
    simpa [prefixWord, tailWord_7865905, baseEnd_7865905] using wordTrace_append hprefix tailTrace_7865905
  have hstable : (prefixWord ++ tailWord_7865905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865905).length < 2 ^ (prefixWord ++ tailWord_7865905).sum := by decide
  have hdescent : baseEnd_7865905 < baseStart_7865905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865916 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_7865916 : Nat := 118140960795 + 7865916 * 2 ^ 59
def prefixEnd_7865916 : Nat := 4983230072969 + 3 ^ 40 * 7865916 * 2
def baseEnd_7865916 : Nat := 4038995695891351801175317

theorem tailTrace_7865916 : CollatzResearch.WordTrace tailWord_7865916 prefixEnd_7865916 4038995695891351801175317 := by
  unfold tailWord_7865916
  simp only [CollatzResearch.WordTrace]
  refine ⟨143446762885568599172524801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191262350514091465563366401 143446762885568599172524801)
  ·
    refine ⟨107585072164176449379393601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143446762885568599172524801 107585072164176449379393601)
    ·
      refine ⟨80688804123132337034545201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107585072164176449379393601 80688804123132337034545201)
      ·
        refine ⟨60516603092349252775908901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80688804123132337034545201 60516603092349252775908901)
        ·
          refine ⟨11346863079815484895482919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60516603092349252775908901 11346863079815484895482919)
          ·
            refine ⟨17020294619723227343224379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11346863079815484895482919 17020294619723227343224379)
            ·
              refine ⟨25530441929584841014836569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17020294619723227343224379 25530441929584841014836569)
              ·
                refine ⟨19147831447188630761127427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25530441929584841014836569 19147831447188630761127427)
                ·
                  refine ⟨28721747170782946141691141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19147831447188630761127427 28721747170782946141691141)
                  ·
                    refine ⟨5385327594521802401567089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28721747170782946141691141 5385327594521802401567089)
                    ·
                      refine ⟨4038995695891351801175317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385327594521802401567089 4038995695891351801175317)
                      ·
                        rfl

theorem cell23_7865916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_7865916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865916 prefixEnd_7865916 := by exact prefixLift 7865916
  have htrace : WordTrace (prefixWord ++ tailWord_7865916) baseStart_7865916 baseEnd_7865916 := by
    simpa [prefixWord, tailWord_7865916, baseEnd_7865916] using wordTrace_append hprefix tailTrace_7865916
  have hstable : (prefixWord ++ tailWord_7865916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865916).length < 2 ^ (prefixWord ++ tailWord_7865916).sum := by decide
  have hdescent : baseEnd_7865916 < baseStart_7865916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865935 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 3, 7]
def baseStart_7865935 : Nat := 118140960795 + 7865935 * 2 ^ 59
def prefixEnd_7865935 : Nat := 4983230072969 + 3 ^ 40 * 7865935 * 2
def baseEnd_7865935 : Nat := 1346335150674595742279243

theorem tailTrace_7865935 : CollatzResearch.WordTrace tailWord_7865935 prefixEnd_7865935 1346335150674595742279243 := by
  unfold tailWord_7865935
  simp only [CollatzResearch.WordTrace]
  refine ⟨286894218758068364589991259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191262812505378909726660839 286894218758068364589991259)
  ·
    refine ⟨430341328137102546884986889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286894218758068364589991259 430341328137102546884986889)
    ·
      refine ⟨322755996102826910163740167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430341328137102546884986889 322755996102826910163740167)
      ·
        refine ⟨484133994154240365245610251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322755996102826910163740167 484133994154240365245610251)
        ·
          refine ⟨726200991231360547868415377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484133994154240365245610251 726200991231360547868415377)
          ·
            refine ⟨544650743423520410901311533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726200991231360547868415377 544650743423520410901311533)
            ·
              refine ⟨204244028783820154087991825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544650743423520410901311533 204244028783820154087991825)
              ·
                refine ⟨153183021587865115565993869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204244028783820154087991825 153183021587865115565993869)
                ·
                  refine ⟨57443633095449418337247701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153183021587865115565993869 57443633095449418337247701)
                  ·
                    refine ⟨1346335150674595742279243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57443633095449418337247701 1346335150674595742279243)
                    ·
                      rfl

theorem cell23_7865935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_7865935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865935 prefixEnd_7865935 := by exact prefixLift 7865935
  have htrace : WordTrace (prefixWord ++ tailWord_7865935) baseStart_7865935 baseEnd_7865935 := by
    simpa [prefixWord, tailWord_7865935, baseEnd_7865935] using wordTrace_append hprefix tailTrace_7865935
  have hstable : (prefixWord ++ tailWord_7865935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865935).length < 2 ^ (prefixWord ++ tailWord_7865935).sum := by decide
  have hdescent : baseEnd_7865935 < baseStart_7865935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7865989 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 4, 4, 2]
def baseStart_7865989 : Nat := 118140960795 + 7865989 * 2 ^ 59
def prefixEnd_7865989 : Nat := 4983230072969 + 3 ^ 40 * 7865989 * 2
def baseEnd_7865989 : Nat := 4039033179979130015562481

theorem tailTrace_7865989 : CollatzResearch.WordTrace tailWord_7865989 prefixEnd_7865989 4039033179979130015562481 := by
  unfold tailWord_7865989
  simp only [CollatzResearch.WordTrace]
  refine ⟨286896188299872731812457021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191264125533248487874971347 286896188299872731812457021)
  ·
    refine ⟨107586070612452274429671383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286896188299872731812457021 107586070612452274429671383)
    ·
      refine ⟨161379105918678411644507075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107586070612452274429671383 161379105918678411644507075)
      ·
        refine ⟨242068658878017617466760613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161379105918678411644507075 242068658878017617466760613)
        ·
          refine ⟨45387873539628303275017615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242068658878017617466760613 45387873539628303275017615)
          ·
            refine ⟨68081810309442454912526423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45387873539628303275017615 68081810309442454912526423)
            ·
              refine ⟨102122715464163682368789635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68081810309442454912526423 102122715464163682368789635)
              ·
                refine ⟨153184073196245523553184453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102122715464163682368789635 153184073196245523553184453)
                ·
                  refine ⟨28722013724296035666222085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153184073196245523553184453 28722013724296035666222085)
                  ·
                    refine ⟨5385377573305506687416641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28722013724296035666222085 5385377573305506687416641)
                    ·
                      refine ⟨4039033179979130015562481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385377573305506687416641 4039033179979130015562481)
                      ·
                        rfl

theorem cell23_7865989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_7865989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7865989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7865989 prefixEnd_7865989 := by exact prefixLift 7865989
  have htrace : WordTrace (prefixWord ++ tailWord_7865989) baseStart_7865989 baseEnd_7865989 := by
    simpa [prefixWord, tailWord_7865989, baseEnd_7865989] using wordTrace_append hprefix tailTrace_7865989
  have hstable : (prefixWord ++ tailWord_7865989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7865989).length < 2 ^ (prefixWord ++ tailWord_7865989).sum := by decide
  have hdescent : baseEnd_7865989 < baseStart_7865989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7865989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866079 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_7866079 : Nat := 118140960795 + 7866079 * 2 ^ 59
def prefixEnd_7866079 : Nat := 4983230072969 + 3 ^ 40 * 7866079 * 2
def baseEnd_7866079 : Nat := 4039079393238034663437067

theorem tailTrace_7866079 : CollatzResearch.WordTrace tailWord_7866079 prefixEnd_7866079 4039079393238034663437067 := by
  unfold tailWord_7866079
  simp only [CollatzResearch.WordTrace]
  refine ⟨286899470869546677183233291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191266313913031118122155527 286899470869546677183233291)
  ·
    refine ⟨430349206304320015774849937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286899470869546677183233291 430349206304320015774849937)
    ·
      refine ⟨322761904728240011831137453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430349206304320015774849937 322761904728240011831137453)
      ·
        refine ⟨121035714273090004436676545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322761904728240011831137453 121035714273090004436676545)
        ·
          refine ⟨90776785704817503327507409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121035714273090004436676545 90776785704817503327507409)
          ·
            refine ⟨68082589278613127495630557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90776785704817503327507409 68082589278613127495630557)
            ·
              refine ⟨25530970979479922810861459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68082589278613127495630557 25530970979479922810861459)
              ·
                refine ⟨38296456469219884216292189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25530970979479922810861459 38296456469219884216292189)
                ·
                  refine ⟨14361171175957456581109571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38296456469219884216292189 14361171175957456581109571)
                  ·
                    refine ⟨21541756763936184871664357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14361171175957456581109571 21541756763936184871664357)
                    ·
                      refine ⟨4039079393238034663437067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21541756763936184871664357 4039079393238034663437067)
                      ·
                        rfl

theorem cell23_7866079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_7866079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866079 prefixEnd_7866079 := by exact prefixLift 7866079
  have htrace : WordTrace (prefixWord ++ tailWord_7866079) baseStart_7866079 baseEnd_7866079 := by
    simpa [prefixWord, tailWord_7866079, baseEnd_7866079] using wordTrace_append hprefix tailTrace_7866079
  have hstable : (prefixWord ++ tailWord_7866079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866079).length < 2 ^ (prefixWord ++ tailWord_7866079).sum := by decide
  have hdescent : baseEnd_7866079 < baseStart_7866079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866093 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_7866093 : Nat := 118140960795 + 7866093 * 2 ^ 59
def prefixEnd_7866093 : Nat := 4983230072969 + 3 ^ 40 * 7866093 * 2
def baseEnd_7866093 : Nat := 1346362193989065869554001

theorem tailTrace_7866093 : CollatzResearch.WordTrace tailWord_7866093 prefixEnd_7866093 1346362193989065869554001 := by
  unfold tailWord_7866093
  simp only [CollatzResearch.WordTrace]
  refine ⟨286899981491495957574242933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191266654327663971716161955 286899981491495957574242933)
  ·
    refine ⟨26896873264827746022585275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286899981491495957574242933 26896873264827746022585275)
    ·
      refine ⟨40345309897241619033877913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26896873264827746022585275 40345309897241619033877913)
      ·
        refine ⟨30258982422931214275408435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40345309897241619033877913 30258982422931214275408435)
        ·
          refine ⟨45388473634396821413112653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30258982422931214275408435 45388473634396821413112653)
          ·
            refine ⟨17020677612898808029917245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45388473634396821413112653 17020677612898808029917245)
            ·
              refine ⟨6382754104837053011218967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17020677612898808029917245 6382754104837053011218967)
              ·
                refine ⟨9574131157255579516828451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382754104837053011218967 9574131157255579516828451)
                ·
                  refine ⟨14361196735883369275242677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9574131157255579516828451 14361196735883369275242677)
                  ·
                    refine ⟨1346362193989065869554001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14361196735883369275242677 1346362193989065869554001)
                    ·
                      rfl

theorem cell23_7866093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_7866093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866093 prefixEnd_7866093 := by exact prefixLift 7866093
  have htrace : WordTrace (prefixWord ++ tailWord_7866093) baseStart_7866093 baseEnd_7866093 := by
    simpa [prefixWord, tailWord_7866093, baseEnd_7866093] using wordTrace_append hprefix tailTrace_7866093
  have hstable : (prefixWord ++ tailWord_7866093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866093).length < 2 ^ (prefixWord ++ tailWord_7866093).sum := by decide
  have hdescent : baseEnd_7866093 < baseStart_7866093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866096 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 7, 2, 2]
def baseStart_7866096 : Nat := 118140960795 + 7866096 * 2 ^ 59
def prefixEnd_7866096 : Nat := 4983230072969 + 3 ^ 40 * 7866096 * 2
def baseEnd_7866096 : Nat := 4039088122409161096924489

theorem tailTrace_7866096 : CollatzResearch.WordTrace tailWord_7866096 prefixEnd_7866096 4039088122409161096924489 := by
  unfold tailWord_7866096
  simp only [CollatzResearch.WordTrace]
  refine ⟨143450045455242544543301071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191266727273656726057734761 143450045455242544543301071)
  ·
    refine ⟨215175068182863816814951607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143450045455242544543301071 215175068182863816814951607)
    ·
      refine ⟨322762602274295725222427411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215175068182863816814951607 322762602274295725222427411)
      ·
        refine ⟨484143903411443587833641117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322762602274295725222427411 484143903411443587833641117)
        ·
          refine ⟨181553963779291345437615419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484143903411443587833641117 181553963779291345437615419)
          ·
            refine ⟨272330945668937018156423129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181553963779291345437615419 272330945668937018156423129)
            ·
              refine ⟨204248209251702763617317347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272330945668937018156423129 204248209251702763617317347)
              ·
                refine ⟨306372313877554145425976021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204248209251702763617317347 306372313877554145425976021)
                ·
                  refine ⟨7180601106505175283421313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 306372313877554145425976021 7180601106505175283421313)
                  ·
                    refine ⟨5385450829878881462565985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7180601106505175283421313 5385450829878881462565985)
                    ·
                      refine ⟨4039088122409161096924489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385450829878881462565985 4039088122409161096924489)
                      ·
                        rfl

theorem cell23_7866096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 2, 2].length) (baseStart_7866096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866096 prefixEnd_7866096 := by exact prefixLift 7866096
  have htrace : WordTrace (prefixWord ++ tailWord_7866096) baseStart_7866096 baseEnd_7866096 := by
    simpa [prefixWord, tailWord_7866096, baseEnd_7866096] using wordTrace_append hprefix tailTrace_7866096
  have hstable : (prefixWord ++ tailWord_7866096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866096).length < 2 ^ (prefixWord ++ tailWord_7866096).sum := by decide
  have hdescent : baseEnd_7866096 < baseStart_7866096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866099 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 5]
def baseStart_7866099 : Nat := 118140960795 + 7866099 * 2 ^ 59
def prefixEnd_7866099 : Nat := 4983230072969 + 3 ^ 40 * 7866099 * 2
def baseEnd_7866099 : Nat := 4039089662851124585186975

theorem tailTrace_7866099 : CollatzResearch.WordTrace tailWord_7866099 prefixEnd_7866099 4039089662851124585186975 := by
  unfold tailWord_7866099
  simp only [CollatzResearch.WordTrace]
  refine ⟨286900200329474220598961351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191266800219649480399307567 286900200329474220598961351)
  ·
    refine ⟨430350300494211330898442027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286900200329474220598961351 430350300494211330898442027)
    ·
      refine ⟨645525450741316996347663041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430350300494211330898442027 645525450741316996347663041)
      ·
        refine ⟨484144088055987747260747281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645525450741316996347663041 484144088055987747260747281)
        ·
          refine ⟨363108066041990810445560461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484144088055987747260747281 363108066041990810445560461)
          ·
            refine ⟨136165524765746553917085173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363108066041990810445560461 136165524765746553917085173)
            ·
              refine ⟨12765517946788739429726735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136165524765746553917085173 12765517946788739429726735)
              ·
                refine ⟨19148276920183109144590103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12765517946788739429726735 19148276920183109144590103)
                ·
                  refine ⟨28722415380274663716885155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19148276920183109144590103 28722415380274663716885155)
                  ·
                    refine ⟨43083623070411995575327733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28722415380274663716885155 43083623070411995575327733)
                    ·
                      refine ⟨4039089662851124585186975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43083623070411995575327733 4039089662851124585186975)
                      ·
                        rfl

theorem cell23_7866099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_7866099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866099 prefixEnd_7866099 := by exact prefixLift 7866099
  have htrace : WordTrace (prefixWord ++ tailWord_7866099) baseStart_7866099 baseEnd_7866099 := by
    simpa [prefixWord, tailWord_7866099, baseEnd_7866099] using wordTrace_append hprefix tailTrace_7866099
  have hstable : (prefixWord ++ tailWord_7866099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866099).length < 2 ^ (prefixWord ++ tailWord_7866099).sum := by decide
  have hdescent : baseEnd_7866099 < baseStart_7866099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866116 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7866116 : Nat := 118140960795 + 7866116 * 2 ^ 59
def prefixEnd_7866116 : Nat := 4983230072969 + 3 ^ 40 * 7866116 * 2
def baseEnd_7866116 : Nat := 4039098392022251018674397

theorem tailTrace_7866116 : CollatzResearch.WordTrace tailWord_7866116 prefixEnd_7866116 4039098392022251018674397 := by
  unfold tailWord_7866116
  simp only [CollatzResearch.WordTrace]
  refine ⟨143450410185206316251165101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191267213580275088334886801 143450410185206316251165101)
  ·
    refine ⟨53793903819452368594186913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143450410185206316251165101 53793903819452368594186913)
    ·
      refine ⟨40345427864589276445640185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53793903819452368594186913 40345427864589276445640185)
      ·
        refine ⟨30259070898441957334230139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40345427864589276445640185 30259070898441957334230139)
        ·
          refine ⟨45388606347662936001345209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30259070898441957334230139 45388606347662936001345209)
          ·
            refine ⟨34041454760747202001008907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45388606347662936001345209 34041454760747202001008907)
            ·
              refine ⟨51062182141120803001513361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34041454760747202001008907 51062182141120803001513361)
              ·
                refine ⟨38296636605840602251135021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51062182141120803001513361 38296636605840602251135021)
                ·
                  refine ⟨14361238727190225844175633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38296636605840602251135021 14361238727190225844175633)
                  ·
                    refine ⟨10770929045392669383131725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14361238727190225844175633 10770929045392669383131725)
                    ·
                      refine ⟨4039098392022251018674397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10770929045392669383131725 4039098392022251018674397)
                      ·
                        rfl

theorem cell23_7866116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7866116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866116 prefixEnd_7866116 := by exact prefixLift 7866116
  have htrace : WordTrace (prefixWord ++ tailWord_7866116) baseStart_7866116 baseEnd_7866116 := by
    simpa [prefixWord, tailWord_7866116, baseEnd_7866116] using wordTrace_append hprefix tailTrace_7866116
  have hstable : (prefixWord ++ tailWord_7866116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866116).length < 2 ^ (prefixWord ++ tailWord_7866116).sum := by decide
  have hdescent : baseEnd_7866116 < baseStart_7866116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866130 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7866130 : Nat := 118140960795 + 7866130 * 2 ^ 59
def prefixEnd_7866130 : Nat := 4983230072969 + 3 ^ 40 * 7866130 * 2
def baseEnd_7866130 : Nat := 4039105580751413963899333

theorem tailTrace_7866130 : CollatzResearch.WordTrace tailWord_7866130 prefixEnd_7866130 4039105580751413963899333 := by
  unfold tailWord_7866130
  simp only [CollatzResearch.WordTrace]
  refine ⟨71725332748090478223334961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191267553994907941928893229 71725332748090478223334961)
  ·
    refine ⟨53793999561067858667501221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71725332748090478223334961 53793999561067858667501221)
    ·
      refine ⟨10086374917700223500156479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53793999561067858667501221 10086374917700223500156479)
      ·
        refine ⟨15129562376550335250234719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10086374917700223500156479 15129562376550335250234719)
        ·
          refine ⟨22694343564825502875352079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15129562376550335250234719 22694343564825502875352079)
          ·
            refine ⟨34041515347238254313028119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22694343564825502875352079 34041515347238254313028119)
            ·
              refine ⟨51062273020857381469542179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34041515347238254313028119 51062273020857381469542179)
              ·
                refine ⟨76593409531286072204313269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51062273020857381469542179 76593409531286072204313269)
                ·
                  refine ⟨7180632143558069269154369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76593409531286072204313269 7180632143558069269154369)
                  ·
                    refine ⟨5385474107668551951865777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7180632143558069269154369 5385474107668551951865777)
                    ·
                      refine ⟨4039105580751413963899333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385474107668551951865777 4039105580751413963899333)
                      ·
                        rfl

theorem cell23_7866130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7866130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866130 prefixEnd_7866130 := by exact prefixLift 7866130
  have htrace : WordTrace (prefixWord ++ tailWord_7866130) baseStart_7866130 baseEnd_7866130 := by
    simpa [prefixWord, tailWord_7866130, baseEnd_7866130] using wordTrace_append hprefix tailTrace_7866130
  have hstable : (prefixWord ++ tailWord_7866130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866130).length < 2 ^ (prefixWord ++ tailWord_7866130).sum := by decide
  have hdescent : baseEnd_7866130 < baseStart_7866130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866146 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_7866146 : Nat := 118140960795 + 7866146 * 2 ^ 59
def prefixEnd_7866146 : Nat := 4983230072969 + 3 ^ 40 * 7866146 * 2
def baseEnd_7866146 : Nat := 4039113796441885901299259

theorem tailTrace_7866146 : CollatzResearch.WordTrace tailWord_7866146 prefixEnd_7866146 4039113796441885901299259 := by
  unfold tailWord_7866146
  simp only [CollatzResearch.WordTrace]
  refine ⟨71725478640075986906480573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191267943040202631750614861 71725478640075986906480573)
  ·
    refine ⟨26897054490028495089930215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71725478640075986906480573 26897054490028495089930215)
    ·
      refine ⟨40345581735042742634895323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26897054490028495089930215 40345581735042742634895323)
      ·
        refine ⟨60518372602564113952342985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40345581735042742634895323 60518372602564113952342985)
        ·
          refine ⟨45388779451923085464257239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60518372602564113952342985 45388779451923085464257239)
          ·
            refine ⟨68083169177884628196385859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45388779451923085464257239 68083169177884628196385859)
            ·
              refine ⟨102124753766826942294578789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68083169177884628196385859 102124753766826942294578789)
              ·
                refine ⟨19148391331280051680233523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102124753766826942294578789 19148391331280051680233523)
                ·
                  refine ⟨28722586996920077520350285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19148391331280051680233523 28722586996920077520350285)
                  ·
                    refine ⟨10770970123845029070131357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28722586996920077520350285 10770970123845029070131357)
                    ·
                      refine ⟨4039113796441885901299259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10770970123845029070131357 4039113796441885901299259)
                      ·
                        rfl

theorem cell23_7866146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_7866146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866146 prefixEnd_7866146 := by exact prefixLift 7866146
  have htrace : WordTrace (prefixWord ++ tailWord_7866146) baseStart_7866146 baseEnd_7866146 := by
    simpa [prefixWord, tailWord_7866146, baseEnd_7866146] using wordTrace_append hprefix tailTrace_7866146
  have hstable : (prefixWord ++ tailWord_7866146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866146).length < 2 ^ (prefixWord ++ tailWord_7866146).sum := by decide
  have hdescent : baseEnd_7866146 < baseStart_7866146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866163 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 3]
def baseStart_7866163 : Nat := 118140960795 + 7866163 * 2 ^ 59
def prefixEnd_7866163 : Nat := 4983230072969 + 3 ^ 40 * 7866163 * 2
def baseEnd_7866163 : Nat := 4039122525613012334786681

theorem tailTrace_7866163 : CollatzResearch.WordTrace tailWord_7866163 prefixEnd_7866163 4039122525613012334786681 := by
  unfold tailWord_7866163
  simp only [CollatzResearch.WordTrace]
  refine ⟨286902534601242359529291143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191268356400828239686194095 286902534601242359529291143)
  ·
    refine ⟨430353801901863539293936715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286902534601242359529291143 430353801901863539293936715)
    ·
      refine ⟨645530702852795308940905073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430353801901863539293936715 645530702852795308940905073)
      ·
        refine ⟨484148027139596481705678805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645530702852795308940905073 484148027139596481705678805)
        ·
          refine ⟨11347219386084292539976847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 484148027139596481705678805 11347219386084292539976847)
          ·
            refine ⟨17020829079126438809965271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347219386084292539976847 17020829079126438809965271)
            ·
              refine ⟨25531243618689658214947907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17020829079126438809965271 25531243618689658214947907)
              ·
                refine ⟨38296865428034487322421861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25531243618689658214947907 38296865428034487322421861)
                ·
                  refine ⟨7180662267756466372954099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38296865428034487322421861 7180662267756466372954099)
                  ·
                    refine ⟨10770993401634699559431149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7180662267756466372954099 10770993401634699559431149)
                    ·
                      refine ⟨4039122525613012334786681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10770993401634699559431149 4039122525613012334786681)
                      ·
                        rfl

theorem cell23_7866163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_7866163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866163 prefixEnd_7866163 := by exact prefixLift 7866163
  have htrace : WordTrace (prefixWord ++ tailWord_7866163) baseStart_7866163 baseEnd_7866163 := by
    simpa [prefixWord, tailWord_7866163, baseEnd_7866163] using wordTrace_append hprefix tailTrace_7866163
  have hstable : (prefixWord ++ tailWord_7866163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866163).length < 2 ^ (prefixWord ++ tailWord_7866163).sum := by decide
  have hdescent : baseEnd_7866163 < baseStart_7866163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866179 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 2, 6]
def baseStart_7866179 : Nat := 118140960795 + 7866179 * 2 ^ 59
def prefixEnd_7866179 : Nat := 4983230072969 + 3 ^ 40 * 7866179 * 2
def baseEnd_7866179 : Nat := 1346376913767828090728869

theorem tailTrace_7866179 : CollatzResearch.WordTrace tailWord_7866179 prefixEnd_7866179 1346376913767828090728869 := by
  unfold tailWord_7866179
  simp only [CollatzResearch.WordTrace]
  refine ⟨286903118169184394261873591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191268745446122929507915727 286903118169184394261873591)
  ·
    refine ⟨430354677253776591392810387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286903118169184394261873591 430354677253776591392810387)
    ·
      refine ⟨645532015880664887089215581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430354677253776591392810387 645532015880664887089215581)
      ·
        refine ⟨242074505955249332658455843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645532015880664887089215581 242074505955249332658455843)
        ·
          refine ⟨363111758932873998987683765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242074505955249332658455843 363111758932873998987683765)
          ·
            refine ⟨34041727399956937405095353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 363111758932873998987683765 34041727399956937405095353)
            ·
              refine ⟨25531295549967703053821515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34041727399956937405095353 25531295549967703053821515)
              ·
                refine ⟨38296943324951554580732273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25531295549967703053821515 38296943324951554580732273)
                ·
                  refine ⟨28722707493713665935549205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38296943324951554580732273 28722707493713665935549205)
                  ·
                    refine ⟨1346376913767828090728869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28722707493713665935549205 1346376913767828090728869)
                    ·
                      rfl

theorem cell23_7866179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 6].length) (baseStart_7866179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866179 prefixEnd_7866179 := by exact prefixLift 7866179
  have htrace : WordTrace (prefixWord ++ tailWord_7866179) baseStart_7866179 baseEnd_7866179 := by
    simpa [prefixWord, tailWord_7866179, baseEnd_7866179] using wordTrace_append hprefix tailTrace_7866179
  have hstable : (prefixWord ++ tailWord_7866179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866179).length < 2 ^ (prefixWord ++ tailWord_7866179).sum := by decide
  have hdescent : baseEnd_7866179 < baseStart_7866179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866239 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 6, 5]
def baseStart_7866239 : Nat := 118140960795 + 7866239 * 2 ^ 59
def prefixEnd_7866239 : Nat := 4983230072969 + 3 ^ 40 * 7866239 * 2
def baseEnd_7866239 : Nat := 1346387183380918012478777

theorem tailTrace_7866239 : CollatzResearch.WordTrace tailWord_7866239 prefixEnd_7866239 1346387183380918012478777 := by
  unfold tailWord_7866239
  simp only [CollatzResearch.WordTrace]
  refine ⟨286905306548967024509057771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191270204365978016339371847 286905306548967024509057771)
  ·
    refine ⟨430357959823450536763586657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286905306548967024509057771 430357959823450536763586657)
    ·
      refine ⟨322768469867587902572689993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430357959823450536763586657 322768469867587902572689993)
      ·
        refine ⟨242076352400690926929517495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322768469867587902572689993 242076352400690926929517495)
        ·
          refine ⟨363114528601036390394276243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242076352400690926929517495 363114528601036390394276243)
          ·
            refine ⟨544671792901554585591414365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363114528601036390394276243 544671792901554585591414365)
            ·
              refine ⟨204251922338082969596780387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544671792901554585591414365 204251922338082969596780387)
              ·
                refine ⟨306377883507124454395170581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204251922338082969596780387 306377883507124454395170581)
                ·
                  refine ⟨14361463289396458799773621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 306377883507124454395170581 14361463289396458799773621)
                  ·
                    refine ⟨1346387183380918012478777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14361463289396458799773621 1346387183380918012478777)
                    ·
                      rfl

theorem cell23_7866239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_7866239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866239 prefixEnd_7866239 := by exact prefixLift 7866239
  have htrace : WordTrace (prefixWord ++ tailWord_7866239) baseStart_7866239 baseEnd_7866239 := by
    simpa [prefixWord, tailWord_7866239, baseEnd_7866239] using wordTrace_append hprefix tailTrace_7866239
  have hstable : (prefixWord ++ tailWord_7866239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866239).length < 2 ^ (prefixWord ++ tailWord_7866239).sum := by decide
  have hdescent : baseEnd_7866239 < baseStart_7866239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866249 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_7866249 : Nat := 118140960795 + 7866249 * 2 ^ 59
def prefixEnd_7866249 : Nat := 4983230072969 + 3 ^ 40 * 7866249 * 2
def baseEnd_7866249 : Nat := 4039166684949298998311285

theorem tailTrace_7866249 : CollatzResearch.WordTrace tailWord_7866249 prefixEnd_7866249 4039166684949298998311285 := by
  unfold tailWord_7866249
  simp only [CollatzResearch.WordTrace]
  refine ⟨286905671278930796216921801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191270447519287197477947867 286905671278930796216921801)
  ·
    refine ⟨215179253459198097162691351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286905671278930796216921801 215179253459198097162691351)
    ·
      refine ⟨322768880188797145744037027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215179253459198097162691351 322768880188797145744037027)
      ·
        refine ⟨484153320283195718616055541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322768880188797145744037027 484153320283195718616055541)
        ·
          refine ⟨45389373776549598620255207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484153320283195718616055541 45389373776549598620255207)
          ·
            refine ⟨68084060664824397930382811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45389373776549598620255207 68084060664824397930382811)
            ·
              refine ⟨102126090997236596895574217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68084060664824397930382811 102126090997236596895574217)
              ·
                refine ⟨76594568247927447671680663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102126090997236596895574217 76594568247927447671680663)
                ·
                  refine ⟨114891852371891171507520995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76594568247927447671680663 114891852371891171507520995)
                  ·
                    refine ⟨172337778557836757261281493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114891852371891171507520995 172337778557836757261281493)
                    ·
                      refine ⟨4039166684949298998311285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172337778557836757261281493 4039166684949298998311285)
                      ·
                        rfl

theorem cell23_7866249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_7866249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866249 prefixEnd_7866249 := by exact prefixLift 7866249
  have htrace : WordTrace (prefixWord ++ tailWord_7866249) baseStart_7866249 baseEnd_7866249 := by
    simpa [prefixWord, tailWord_7866249, baseEnd_7866249] using wordTrace_append hprefix tailTrace_7866249
  have hstable : (prefixWord ++ tailWord_7866249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866249).length < 2 ^ (prefixWord ++ tailWord_7866249).sum := by decide
  have hdescent : baseEnd_7866249 < baseStart_7866249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866259 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4]
def baseStart_7866259 : Nat := 118140960795 + 7866259 * 2 ^ 59
def prefixEnd_7866259 : Nat := 4983230072969 + 3 ^ 40 * 7866259 * 2
def baseEnd_7866259 : Nat := 4039171819755843959186239

theorem tailTrace_7866259 : CollatzResearch.WordTrace tailWord_7866259 prefixEnd_7866259 4039171819755843959186239 := by
  unfold tailWord_7866259
  simp only [CollatzResearch.WordTrace]
  refine ⟨286906036008894567924785831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191270690672596378616523887 286906036008894567924785831)
  ·
    refine ⟨430359054013341851887178747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286906036008894567924785831 430359054013341851887178747)
    ·
      refine ⟨645538581020012777830768121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430359054013341851887178747 645538581020012777830768121)
      ·
        refine ⟨484153935765009583373076091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645538581020012777830768121 484153935765009583373076091)
        ·
          refine ⟨726230903647514375059614137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484153935765009583373076091 726230903647514375059614137)
          ·
            refine ⟨544673177735635781294710603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726230903647514375059614137 544673177735635781294710603)
            ·
              refine ⟨817009766603453671942065905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544673177735635781294710603 817009766603453671942065905)
              ·
                refine ⟨612757324952590253956549429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817009766603453671942065905 612757324952590253956549429)
                ·
                  refine ⟨57445999214305336308426509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 612757324952590253956549429 57445999214305336308426509)
                  ·
                    refine ⟨21542249705364501115659941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57445999214305336308426509 21542249705364501115659941)
                    ·
                      refine ⟨4039171819755843959186239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21542249705364501115659941 4039171819755843959186239)
                      ·
                        rfl

theorem cell23_7866259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_7866259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866259 prefixEnd_7866259 := by exact prefixLift 7866259
  have htrace : WordTrace (prefixWord ++ tailWord_7866259) baseStart_7866259 baseEnd_7866259 := by
    simpa [prefixWord, tailWord_7866259, baseEnd_7866259] using wordTrace_append hprefix tailTrace_7866259
  have hstable : (prefixWord ++ tailWord_7866259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866259).length < 2 ^ (prefixWord ++ tailWord_7866259).sum := by decide
  have hdescent : baseEnd_7866259 < baseStart_7866259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866266 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7866266 : Nat := 118140960795 + 7866266 * 2 ^ 59
def prefixEnd_7866266 : Nat := 4983230072969 + 3 ^ 40 * 7866266 * 2
def baseEnd_7866266 : Nat := 4039175414120425431798707

theorem tailTrace_7866266 : CollatzResearch.WordTrace tailWord_7866266 prefixEnd_7866266 4039175414120425431798707 := by
  unfold tailWord_7866266
  simp only [CollatzResearch.WordTrace]
  refine ⟨71726572829967302030072663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191270860879912805413527101 71726572829967302030072663)
  ·
    refine ⟨107589859244950953045108995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71726572829967302030072663 107589859244950953045108995)
    ·
      refine ⟨161384788867426429567663493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107589859244950953045108995 161384788867426429567663493)
      ·
        refine ⟨30259647912642455543936905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161384788867426429567663493 30259647912642455543936905)
        ·
          refine ⟨22694735934481841657952679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30259647912642455543936905 22694735934481841657952679)
          ·
            refine ⟨34042103901722762486929019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22694735934481841657952679 34042103901722762486929019)
            ·
              refine ⟨51063155852584143730393529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34042103901722762486929019 51063155852584143730393529)
              ·
                refine ⟨38297366889438107797795147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51063155852584143730393529 38297366889438107797795147)
                ·
                  refine ⟨57446050334157161696692721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38297366889438107797795147 57446050334157161696692721)
                  ·
                    refine ⟨43084537750617871272519541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57446050334157161696692721 43084537750617871272519541)
                    ·
                      refine ⟨4039175414120425431798707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43084537750617871272519541 4039175414120425431798707)
                      ·
                        rfl

theorem cell23_7866266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7866266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866266 prefixEnd_7866266 := by exact prefixLift 7866266
  have htrace : WordTrace (prefixWord ++ tailWord_7866266) baseStart_7866266 baseEnd_7866266 := by
    simpa [prefixWord, tailWord_7866266, baseEnd_7866266] using wordTrace_append hprefix tailTrace_7866266
  have hstable : (prefixWord ++ tailWord_7866266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866266).length < 2 ^ (prefixWord ++ tailWord_7866266).sum := by decide
  have hdescent : baseEnd_7866266 < baseStart_7866266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
