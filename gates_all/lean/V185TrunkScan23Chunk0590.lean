import V185TrunkScan23Chunk0589

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3488730 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2]
def baseStart_3488730 : Nat := 118140960795 + 3488730 * 2 ^ 59
def prefixEnd_3488730 : Nat := 4983230072969 + 3 ^ 40 * 3488730 * 2
def baseEnd_3488730 : Nat := 1791395363760240561530629

theorem tailTrace_3488730 : CollatzResearch.WordTrace tailWord_3488730 prefixEnd_3488730 1791395363760240561530629 := by
  unfold tailWord_3488730
  simp only [CollatzResearch.WordTrace]
  refine ⟨31811109162733628123211911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84829624433956341661898429 31811109162733628123211911)
  ·
    refine ⟨47716663744100442184817867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31811109162733628123211911 47716663744100442184817867)
    ·
      refine ⟨71574995616150663277226801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47716663744100442184817867 71574995616150663277226801)
      ·
        refine ⟨53681246712112997457920101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71574995616150663277226801 53681246712112997457920101)
        ·
          refine ⟨10065233758521187023360019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53681246712112997457920101 10065233758521187023360019)
          ·
            refine ⟨15097850637781780535040029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065233758521187023360019 15097850637781780535040029)
            ·
              refine ⟨5661693989168167700640011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15097850637781780535040029 5661693989168167700640011)
              ·
                refine ⟨8492540983752251550960017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661693989168167700640011 8492540983752251550960017)
                ·
                  refine ⟨6369405737814188663220013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8492540983752251550960017 6369405737814188663220013)
                  ·
                    refine ⟨2388527151680320748707505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6369405737814188663220013 2388527151680320748707505)
                    ·
                      refine ⟨1791395363760240561530629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388527151680320748707505 1791395363760240561530629)
                      ·
                        rfl

theorem cell23_3488730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_3488730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488730 prefixEnd_3488730 := by exact prefixLift 3488730
  have htrace : WordTrace (prefixWord ++ tailWord_3488730) baseStart_3488730 baseEnd_3488730 := by
    simpa [prefixWord, tailWord_3488730, baseEnd_3488730] using wordTrace_append hprefix tailTrace_3488730
  have hstable : (prefixWord ++ tailWord_3488730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488730).length < 2 ^ (prefixWord ++ tailWord_3488730).sum := by decide
  have hdescent : baseEnd_3488730 < baseStart_3488730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488753 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 4, 4]
def baseStart_3488753 : Nat := 118140960795 + 3488753 * 2 ^ 59
def prefixEnd_3488753 : Nat := 4983230072969 + 3 ^ 40 * 3488753 * 2
def baseEnd_3488753 : Nat := 597135724605097990514341

theorem tailTrace_3488753 : CollatzResearch.WordTrace tailWord_3488753 prefixEnd_3488753 597135724605097990514341 := by
  unfold tailWord_3488753
  simp only [CollatzResearch.WordTrace]
  refine ⟨127245275529851187420934913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84830183686567458280623275 127245275529851187420934913)
  ·
    refine ⟨95433956647388390565701185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127245275529851187420934913 95433956647388390565701185)
    ·
      refine ⟨71575467485541292924275889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95433956647388390565701185 71575467485541292924275889)
      ·
        refine ⟨53681600614155969693206917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71575467485541292924275889 53681600614155969693206917)
        ·
          refine ⟨10065300115154244317476297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53681600614155969693206917 10065300115154244317476297)
          ·
            refine ⟨7548975086365683238107223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10065300115154244317476297 7548975086365683238107223)
            ·
              refine ⟨11323462629548524857160835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7548975086365683238107223 11323462629548524857160835)
              ·
                refine ⟨16985193944322787285741253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11323462629548524857160835 16985193944322787285741253)
                ·
                  refine ⟨3184723864560522616076485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16985193944322787285741253 3184723864560522616076485)
                  ·
                    refine ⟨597135724605097990514341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184723864560522616076485 597135724605097990514341)
                    ·
                      rfl

theorem cell23_3488753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_3488753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488753 prefixEnd_3488753 := by exact prefixLift 3488753
  have htrace : WordTrace (prefixWord ++ tailWord_3488753) baseStart_3488753 baseEnd_3488753 := by
    simpa [prefixWord, tailWord_3488753, baseEnd_3488753] using wordTrace_append hprefix tailTrace_3488753
  have hstable : (prefixWord ++ tailWord_3488753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488753).length < 2 ^ (prefixWord ++ tailWord_3488753).sum := by decide
  have hdescent : baseEnd_3488753 < baseStart_3488753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488780 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3488780 : Nat := 118140960795 + 3488780 * 2 ^ 59
def prefixEnd_3488780 : Nat := 4983230072969 + 3 ^ 40 * 3488780 * 2
def baseEnd_3488780 : Nat := 1791421037792965365905399

theorem tailTrace_3488780 : CollatzResearch.WordTrace tailWord_3488780 prefixEnd_3488780 1791421037792965365905399 := by
  unfold tailWord_3488780
  simp only [CollatzResearch.WordTrace]
  refine ⟨63623130150376685516083897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84830840200502247354778529 63623130150376685516083897)
  ·
    refine ⟨47717347612782514137062923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63623130150376685516083897 47717347612782514137062923)
    ·
      refine ⟨71576021419173771205594385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47717347612782514137062923 71576021419173771205594385)
      ·
        refine ⟨53682016064380328404195789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71576021419173771205594385 53682016064380328404195789)
        ·
          refine ⟨20130756024142623151573421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53682016064380328404195789 20130756024142623151573421)
          ·
            refine ⟨7549033509053483681840033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20130756024142623151573421 7549033509053483681840033)
            ·
              refine ⟨5661775131790112761380025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7549033509053483681840033 5661775131790112761380025)
              ·
                refine ⟨4246331348842584571035019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5661775131790112761380025 4246331348842584571035019)
                ·
                  refine ⟨6369497023263876856552529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246331348842584571035019 6369497023263876856552529)
                  ·
                    refine ⟨4777122767447907642414397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6369497023263876856552529 4777122767447907642414397)
                    ·
                      refine ⟨1791421037792965365905399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4777122767447907642414397 1791421037792965365905399)
                      ·
                        rfl

theorem cell23_3488780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3488780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488780 prefixEnd_3488780 := by exact prefixLift 3488780
  have htrace : WordTrace (prefixWord ++ tailWord_3488780) baseStart_3488780 baseEnd_3488780 := by
    simpa [prefixWord, tailWord_3488780, baseEnd_3488780] using wordTrace_append hprefix tailTrace_3488780
  have hstable : (prefixWord ++ tailWord_3488780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488780).length < 2 ^ (prefixWord ++ tailWord_3488780).sum := by decide
  have hdescent : baseEnd_3488780 < baseStart_3488780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488793 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 3]
def baseStart_3488793 : Nat := 118140960795 + 3488793 * 2 ^ 59
def prefixEnd_3488793 : Nat := 4983230072969 + 3 ^ 40 * 3488793 * 2
def baseEnd_3488793 : Nat := 1791427713041473815042839

theorem tailTrace_3488793 : CollatzResearch.WordTrace tailWord_3488793 prefixEnd_3488793 1791427713041473815042839 := by
  unfold tailWord_3488793
  simp only [CollatzResearch.WordTrace]
  refine ⟨127246734449706274252391033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84831156299804182834927355 127246734449706274252391033)
  ·
    refine ⟨95435050837279705689293275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127246734449706274252391033 95435050837279705689293275)
    ·
      refine ⟨143152576255919558533939913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95435050837279705689293275 143152576255919558533939913)
      ·
        refine ⟨107364432191939668900454935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143152576255919558533939913 107364432191939668900454935)
        ·
          refine ⟨161046648287909503350682403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107364432191939668900454935 161046648287909503350682403)
          ·
            refine ⟨241569972431864255026023605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161046648287909503350682403 241569972431864255026023605)
            ·
              refine ⟨22647184915487273908689713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241569972431864255026023605 22647184915487273908689713)
              ·
                refine ⟨16985388686615455431517285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22647184915487273908689713 16985388686615455431517285)
                ·
                  refine ⟨3184760378740397893409491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16985388686615455431517285 3184760378740397893409491)
                  ·
                    refine ⟨4777140568110596840114237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3184760378740397893409491 4777140568110596840114237)
                    ·
                      refine ⟨1791427713041473815042839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4777140568110596840114237 1791427713041473815042839)
                      ·
                        rfl

theorem cell23_3488793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_3488793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488793 prefixEnd_3488793 := by exact prefixLift 3488793
  have htrace : WordTrace (prefixWord ++ tailWord_3488793) baseStart_3488793 baseEnd_3488793 := by
    simpa [prefixWord, tailWord_3488793, baseEnd_3488793] using wordTrace_append hprefix tailTrace_3488793
  have hstable : (prefixWord ++ tailWord_3488793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488793).length < 2 ^ (prefixWord ++ tailWord_3488793).sum := by decide
  have hdescent : baseEnd_3488793 < baseStart_3488793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488800 : List Nat := [2, 1, 1, 7, 2, 1, 9]
def baseStart_3488800 : Nat := 118140960795 + 3488800 * 2 ^ 59
def prefixEnd_3488800 : Nat := 4983230072969 + 3 ^ 40 * 3488800 * 2
def baseEnd_3488800 : Nat := 22116435893901917131547

theorem tailTrace_3488800 : CollatzResearch.WordTrace tailWord_3488800 prefixEnd_3488800 22116435893901917131547 := by
  unfold tailWord_3488800
  simp only [CollatzResearch.WordTrace]
  refine ⟨63623494880340457223947927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84831326507120609631930569 63623494880340457223947927)
  ·
    refine ⟨95435242320510685835921891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63623494880340457223947927 95435242320510685835921891)
    ·
      refine ⟨143152863480766028753882837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95435242320510685835921891 143152863480766028753882837)
      ·
        refine ⟨3355145237830453798919129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 143152863480766028753882837 3355145237830453798919129)
        ·
          refine ⟨2516358928372840349189347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3355145237830453798919129 2516358928372840349189347)
          ·
            refine ⟨3774538392559260523784021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516358928372840349189347 3774538392559260523784021)
            ·
              refine ⟨22116435893901917131547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3774538392559260523784021 22116435893901917131547)
              ·
                rfl

theorem cell23_3488800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 9].length) (baseStart_3488800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488800 prefixEnd_3488800 := by exact prefixLift 3488800
  have htrace : WordTrace (prefixWord ++ tailWord_3488800) baseStart_3488800 baseEnd_3488800 := by
    simpa [prefixWord, tailWord_3488800, baseEnd_3488800] using wordTrace_append hprefix tailTrace_3488800
  have hstable : (prefixWord ++ tailWord_3488800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488800).length < 2 ^ (prefixWord ++ tailWord_3488800).sum := by decide
  have hdescent : baseEnd_3488800 < baseStart_3488800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488816 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_3488816 : Nat := 118140960795 + 3488816 * 2 ^ 59
def prefixEnd_3488816 : Nat := 4983230072969 + 3 ^ 40 * 3488816 * 2
def baseEnd_3488816 : Nat := 1791439523096527225055233

theorem tailTrace_3488816 : CollatzResearch.WordTrace tailWord_3488816 prefixEnd_3488816 1791439523096527225055233 := by
  unfold tailWord_3488816
  simp only [CollatzResearch.WordTrace]
  refine ⟨63623786664311474590239151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84831715552415299453652201 63623786664311474590239151)
  ·
    refine ⟨95435679996467211885358727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63623786664311474590239151 95435679996467211885358727)
    ·
      refine ⟨143153519994700817828038091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95435679996467211885358727 143153519994700817828038091)
      ·
        refine ⟨214730279992051226742057137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143153519994700817828038091 214730279992051226742057137)
        ·
          refine ⟨161047709994038420056542853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214730279992051226742057137 161047709994038420056542853)
          ·
            refine ⟨30196445623882203760601785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161047709994038420056542853 30196445623882203760601785)
            ·
              refine ⟨22647334217911652820451339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30196445623882203760601785 22647334217911652820451339)
              ·
                refine ⟨33971001326867479230677009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22647334217911652820451339 33971001326867479230677009)
                ·
                  refine ⟨25478250995150609423007757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33971001326867479230677009 25478250995150609423007757)
                  ·
                    refine ⟨9554344123181478533627909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25478250995150609423007757 9554344123181478533627909)
                    ·
                      refine ⟨1791439523096527225055233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9554344123181478533627909 1791439523096527225055233)
                      ·
                        rfl

theorem cell23_3488816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_3488816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488816 prefixEnd_3488816 := by exact prefixLift 3488816
  have htrace : WordTrace (prefixWord ++ tailWord_3488816) baseStart_3488816 baseEnd_3488816 := by
    simpa [prefixWord, tailWord_3488816, baseEnd_3488816] using wordTrace_append hprefix tailTrace_3488816
  have hstable : (prefixWord ++ tailWord_3488816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488816).length < 2 ^ (prefixWord ++ tailWord_3488816).sum := by decide
  have hdescent : baseEnd_3488816 < baseStart_3488816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488826 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_3488826 : Nat := 118140960795 + 3488826 * 2 ^ 59
def prefixEnd_3488826 : Nat := 4983230072969 + 3 ^ 40 * 3488826 * 2
def baseEnd_3488826 : Nat := 597148219301024061976729

theorem tailTrace_3488826 : CollatzResearch.WordTrace tailWord_3488826 prefixEnd_3488826 597148219301024061976729 := by
  unfold tailWord_3488826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31811984514646680222085583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84831958705724480592228221 31811984514646680222085583)
  ·
    refine ⟨47717976771970020333128375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31811984514646680222085583 47717976771970020333128375)
    ·
      refine ⟨71576965157955030499692563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47717976771970020333128375 71576965157955030499692563)
      ·
        refine ⟨107365447736932545749538845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71576965157955030499692563 107365447736932545749538845)
        ·
          refine ⟨40262042901349704656077067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107365447736932545749538845 40262042901349704656077067)
          ·
            refine ⟨60393064352024556984115601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40262042901349704656077067 60393064352024556984115601)
            ·
              refine ⟨45294798264018417738086701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60393064352024556984115601 45294798264018417738086701)
              ·
                refine ⟨16985549349006906651782513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45294798264018417738086701 16985549349006906651782513)
                ·
                  refine ⟨12739162011755179988836885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16985549349006906651782513 12739162011755179988836885)
                  ·
                    refine ⟨597148219301024061976729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12739162011755179988836885 597148219301024061976729)
                    ·
                      rfl

theorem cell23_3488826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_3488826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488826 prefixEnd_3488826 := by exact prefixLift 3488826
  have htrace : WordTrace (prefixWord ++ tailWord_3488826) baseStart_3488826 baseEnd_3488826 := by
    simpa [prefixWord, tailWord_3488826, baseEnd_3488826] using wordTrace_append hprefix tailTrace_3488826
  have hstable : (prefixWord ++ tailWord_3488826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488826).length < 2 ^ (prefixWord ++ tailWord_3488826).sum := by decide
  have hdescent : baseEnd_3488826 < baseStart_3488826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488850 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_3488850 : Nat := 118140960795 + 3488850 * 2 ^ 59
def prefixEnd_3488850 : Nat := 4983230072969 + 3 ^ 40 * 3488850 * 2
def baseEnd_3488850 : Nat := 1791456981438780092030077

theorem tailTrace_3488850 : CollatzResearch.WordTrace tailWord_3488850 prefixEnd_3488850 1791456981438780092030077 := by
  unfold tailWord_3488850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31812203352624943246804001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84832542273666515324810669 31812203352624943246804001)
  ·
    refine ⟨23859152514468707435103001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31812203352624943246804001 23859152514468707435103001)
    ·
      refine ⟨17894364385851530576327251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23859152514468707435103001 17894364385851530576327251)
      ·
        refine ⟨26841546578777295864490877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17894364385851530576327251 26841546578777295864490877)
        ·
          refine ⟨10065579967041485949184079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26841546578777295864490877 10065579967041485949184079)
          ·
            refine ⟨15098369950562228923776119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065579967041485949184079 15098369950562228923776119)
            ·
              refine ⟨22647554925843343385664179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15098369950562228923776119 22647554925843343385664179)
              ·
                refine ⟨33971332388765015078496269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22647554925843343385664179 33971332388765015078496269)
                ·
                  refine ⟨12739249645786880654436101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33971332388765015078496269 12739249645786880654436101)
                  ·
                    refine ⟨2388609308585040122706769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12739249645786880654436101 2388609308585040122706769)
                    ·
                      refine ⟨1791456981438780092030077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388609308585040122706769 1791456981438780092030077)
                      ·
                        rfl

theorem cell23_3488850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_3488850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488850 prefixEnd_3488850 := by exact prefixLift 3488850
  have htrace : WordTrace (prefixWord ++ tailWord_3488850) baseStart_3488850 baseEnd_3488850 := by
    simpa [prefixWord, tailWord_3488850, baseEnd_3488850] using wordTrace_append hprefix tailTrace_3488850
  have hstable : (prefixWord ++ tailWord_3488850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488850).length < 2 ^ (prefixWord ++ tailWord_3488850).sum := by decide
  have hdescent : baseEnd_3488850 < baseStart_3488850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488896 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_3488896 : Nat := 118140960795 + 3488896 * 2 ^ 59
def prefixEnd_3488896 : Nat := 4983230072969 + 3 ^ 40 * 3488896 * 2
def baseEnd_3488896 : Nat := 1791480601548886912054865

theorem tailTrace_3488896 : CollatzResearch.WordTrace tailWord_3488896 prefixEnd_3488896 1791480601548886912054865 := by
  unfold tailWord_3488896
  simp only [CollatzResearch.WordTrace]
  refine ⟨63625245584166561421695271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84833660778888748562260361 63625245584166561421695271)
  ·
    refine ⟨95437868376249842132542907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63625245584166561421695271 95437868376249842132542907)
    ·
      refine ⟨143156802564374763198814361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95437868376249842132542907 143156802564374763198814361)
      ·
        refine ⟨107367601923281072399110771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143156802564374763198814361 107367601923281072399110771)
        ·
          refine ⟨161051402884921608598666157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107367601923281072399110771 161051402884921608598666157)
          ·
            refine ⟨60394276081845603224499809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161051402884921608598666157 60394276081845603224499809)
            ·
              refine ⟨45295707061384202418374857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60394276081845603224499809 45295707061384202418374857)
              ·
                refine ⟨33971780296038151813781143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45295707061384202418374857 33971780296038151813781143)
                ·
                  refine ⟨50957670444057227720671715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33971780296038151813781143 50957670444057227720671715)
                  ·
                    refine ⟨76436505666085841581007573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50957670444057227720671715 76436505666085841581007573)
                    ·
                      refine ⟨1791480601548886912054865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76436505666085841581007573 1791480601548886912054865)
                      ·
                        rfl

theorem cell23_3488896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_3488896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488896 prefixEnd_3488896 := by exact prefixLift 3488896
  have htrace : WordTrace (prefixWord ++ tailWord_3488896) baseStart_3488896 baseEnd_3488896 := by
    simpa [prefixWord, tailWord_3488896, baseEnd_3488896] using wordTrace_append hprefix tailTrace_3488896
  have hstable : (prefixWord ++ tailWord_3488896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488896).length < 2 ^ (prefixWord ++ tailWord_3488896).sum := by decide
  have hdescent : baseEnd_3488896 < baseStart_3488896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488943 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_3488943 : Nat := 118140960795 + 3488943 * 2 ^ 59
def prefixEnd_3488943 : Nat := 4983230072969 + 3 ^ 40 * 3488943 * 2
def baseEnd_3488943 : Nat := 1791504735139648228167149

theorem tailTrace_3488943 : CollatzResearch.WordTrace tailWord_3488943 prefixEnd_3488943 1791504735139648228167149 := by
  unfold tailWord_3488943
  simp only [CollatzResearch.WordTrace]
  refine ⟨127252205399162849870351483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84834803599441899913567655 127252205399162849870351483)
  ·
    refine ⟨190878308098744274805527225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127252205399162849870351483 190878308098744274805527225)
    ·
      refine ⟨143158731074058206104145419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190878308098744274805527225 143158731074058206104145419)
      ·
        refine ⟨214738096611087309156218129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143158731074058206104145419 214738096611087309156218129)
        ·
          refine ⟨161053572458315481867163597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214738096611087309156218129 161053572458315481867163597)
          ·
            refine ⟨60395089671868305700186349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161053572458315481867163597 60395089671868305700186349)
            ·
              refine ⟨22648158626950614637569881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60395089671868305700186349 22648158626950614637569881)
              ·
                refine ⟨16986118970212960978177411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22648158626950614637569881 16986118970212960978177411)
                ·
                  refine ⟨25479178455319441467266117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16986118970212960978177411 25479178455319441467266117)
                  ·
                    refine ⟨4777345960372395275112397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25479178455319441467266117 4777345960372395275112397)
                    ·
                      refine ⟨1791504735139648228167149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4777345960372395275112397 1791504735139648228167149)
                      ·
                        rfl

theorem cell23_3488943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_3488943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488943 prefixEnd_3488943 := by exact prefixLift 3488943
  have htrace : WordTrace (prefixWord ++ tailWord_3488943) baseStart_3488943 baseEnd_3488943 := by
    simpa [prefixWord, tailWord_3488943, baseEnd_3488943] using wordTrace_append hprefix tailTrace_3488943
  have hstable : (prefixWord ++ tailWord_3488943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488943).length < 2 ^ (prefixWord ++ tailWord_3488943).sum := by decide
  have hdescent : baseEnd_3488943 < baseStart_3488943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3488984 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 3, 4]
def baseStart_3488984 : Nat := 118140960795 + 3488984 * 2 ^ 59
def prefixEnd_3488984 : Nat := 4983230072969 + 3 ^ 40 * 3488984 * 2
def baseEnd_3488984 : Nat := 597175262615494189251487

theorem tailTrace_3488984 : CollatzResearch.WordTrace tailWord_3488984 prefixEnd_3488984 597175262615494189251487 := by
  unfold tailWord_3488984
  simp only [CollatzResearch.WordTrace]
  refine ⟨63626850396007156936297003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84835800528009542581729337 63626850396007156936297003)
  ·
    refine ⟨95440275594010735404445505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63626850396007156936297003 95440275594010735404445505)
    ·
      refine ⟨71580206695508051553334129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95440275594010735404445505 71580206695508051553334129)
      ·
        refine ⟨53685155021631038665000597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71580206695508051553334129 53685155021631038665000597)
        ·
          refine ⟨2516491641638954937421903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53685155021631038665000597 2516491641638954937421903)
          ·
            refine ⟨3774737462458432406132855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516491641638954937421903 3774737462458432406132855)
            ·
              refine ⟨5662106193687648609199283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774737462458432406132855 5662106193687648609199283)
              ·
                refine ⟨8493159290531472913798925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662106193687648609199283 8493159290531472913798925)
                ·
                  refine ⟨3184934733949302342674597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8493159290531472913798925 3184934733949302342674597)
                  ·
                    refine ⟨597175262615494189251487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184934733949302342674597 597175262615494189251487)
                    ·
                      rfl

theorem cell23_3488984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_3488984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3488984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3488984 prefixEnd_3488984 := by exact prefixLift 3488984
  have htrace : WordTrace (prefixWord ++ tailWord_3488984) baseStart_3488984 baseEnd_3488984 := by
    simpa [prefixWord, tailWord_3488984, baseEnd_3488984] using wordTrace_append hprefix tailTrace_3488984
  have hstable : (prefixWord ++ tailWord_3488984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3488984).length < 2 ^ (prefixWord ++ tailWord_3488984).sum := by decide
  have hdescent : baseEnd_3488984 < baseStart_3488984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3488984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489017 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 2, 3, 2]
def baseStart_3489017 : Nat := 118140960795 + 3489017 * 2 ^ 59
def prefixEnd_3489017 : Nat := 4983230072969 + 3 ^ 40 * 3489017 * 2
def baseEnd_3489017 : Nat := 1791542732708080938641809

theorem tailTrace_3489017 : CollatzResearch.WordTrace tailWord_3489017 prefixEnd_3489017 1791542732708080938641809 := by
  unfold tailWord_3489017
  simp only [CollatzResearch.WordTrace]
  refine ⟨127254904400894760508545305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84836602933929840339030203 127254904400894760508545305)
  ·
    refine ⟨95441178300671070381408979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127254904400894760508545305 95441178300671070381408979)
    ·
      refine ⟨143161767451006605572113469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95441178300671070381408979 143161767451006605572113469)
      ·
        refine ⟨53685662794127477089542551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143161767451006605572113469 53685662794127477089542551)
        ·
          refine ⟨80528494191191215634313827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53685662794127477089542551 80528494191191215634313827)
          ·
            refine ⟨120792741286786823451470741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80528494191191215634313827 120792741286786823451470741)
            ·
              refine ⟨5662159747818132349287691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120792741286786823451470741 5662159747818132349287691)
              ·
                refine ⟨8493239621727198523931537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662159747818132349287691 8493239621727198523931537)
                ·
                  refine ⟨6369929716295398892948653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8493239621727198523931537 6369929716295398892948653)
                  ·
                    refine ⟨2388723643610774584855745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6369929716295398892948653 2388723643610774584855745)
                    ·
                      refine ⟨1791542732708080938641809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388723643610774584855745 1791542732708080938641809)
                      ·
                        rfl

theorem cell23_3489017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_3489017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489017 prefixEnd_3489017 := by exact prefixLift 3489017
  have htrace : WordTrace (prefixWord ++ tailWord_3489017) baseStart_3489017 baseEnd_3489017 := by
    simpa [prefixWord, tailWord_3489017, baseEnd_3489017] using wordTrace_append hprefix tailTrace_3489017
  have hstable : (prefixWord ++ tailWord_3489017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489017).length < 2 ^ (prefixWord ++ tailWord_3489017).sum := by decide
  have hdescent : baseEnd_3489017 < baseStart_3489017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489023 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 3, 6]
def baseStart_3489023 : Nat := 118140960795 + 3489023 * 2 ^ 59
def prefixEnd_3489023 : Nat := 4983230072969 + 3 ^ 40 * 3489023 * 2
def baseEnd_3489023 : Nat := 597181937864002638388927

theorem tailTrace_3489023 : CollatzResearch.WordTrace tailWord_3489023 prefixEnd_3489023 597181937864002638388927 := by
  unfold tailWord_3489023
  simp only [CollatzResearch.WordTrace]
  refine ⟨127255123238873023533263723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84836748825915349022175815 127255123238873023533263723)
  ·
    refine ⟨190882684858309535299895585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127255123238873023533263723 190882684858309535299895585)
    ·
      refine ⟨143162013643732151474921689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190882684858309535299895585 143162013643732151474921689)
      ·
        refine ⟨107371510232799113606191267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143162013643732151474921689 107371510232799113606191267)
        ·
          refine ⟨161057265349198670409286901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107371510232799113606191267 161057265349198670409286901)
          ·
            refine ⟨15099118626487375350870647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161057265349198670409286901 15099118626487375350870647)
            ·
              refine ⟨22648677939731063026305971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15099118626487375350870647 22648677939731063026305971)
              ·
                refine ⟨33973016909596594539458957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22648677939731063026305971 33973016909596594539458957)
                ·
                  refine ⟨12739881341098722952297109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33973016909596594539458957 12739881341098722952297109)
                  ·
                    refine ⟨597181937864002638388927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12739881341098722952297109 597181937864002638388927)
                    ·
                      rfl

theorem cell23_3489023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_3489023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489023 prefixEnd_3489023 := by exact prefixLift 3489023
  have htrace : WordTrace (prefixWord ++ tailWord_3489023) baseStart_3489023 baseEnd_3489023 := by
    simpa [prefixWord, tailWord_3489023, baseEnd_3489023] using wordTrace_append hprefix tailTrace_3489023
  have hstable : (prefixWord ++ tailWord_3489023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489023).length < 2 ^ (prefixWord ++ tailWord_3489023).sum := by decide
  have hdescent : baseEnd_3489023 < baseStart_3489023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489027 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 1, 5]
def baseStart_3489027 : Nat := 118140960795 + 3489027 * 2 ^ 59
def prefixEnd_3489027 : Nat := 4983230072969 + 3 ^ 40 * 3489027 * 2
def baseEnd_3489027 : Nat := 597182622504875299838921

theorem tailTrace_3489027 : CollatzResearch.WordTrace tailWord_3489027 prefixEnd_3489027 597182622504875299838921 := by
  unfold tailWord_3489027
  simp only [CollatzResearch.WordTrace]
  refine ⟨127255269130858532216409335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84836846087239021477606223 127255269130858532216409335)
  ·
    refine ⟨190882903696287798324614003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127255269130858532216409335 190882903696287798324614003)
    ·
      refine ⟨286324355544431697486921005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190882903696287798324614003 286324355544431697486921005)
      ·
        refine ⟨107371633329161886557595377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286324355544431697486921005 107371633329161886557595377)
        ·
          refine ⟨80528724996871414918196533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107371633329161886557595377 80528724996871414918196533)
          ·
            refine ⟨7549567968456695148580925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80528724996871414918196533 7549567968456695148580925)
            ·
              refine ⟨2831087988171260680717847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7549567968456695148580925 2831087988171260680717847)
              ·
                refine ⟨4246631982256891021076771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831087988171260680717847 4246631982256891021076771)
                ·
                  refine ⟨6369947973385336531615157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246631982256891021076771 6369947973385336531615157)
                  ·
                    refine ⟨597182622504875299838921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6369947973385336531615157 597182622504875299838921)
                    ·
                      rfl

theorem cell23_3489027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 5].length) (baseStart_3489027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489027 prefixEnd_3489027 := by exact prefixLift 3489027
  have htrace : WordTrace (prefixWord ++ tailWord_3489027) baseStart_3489027 baseEnd_3489027 := by
    simpa [prefixWord, tailWord_3489027, baseEnd_3489027] using wordTrace_append hprefix tailTrace_3489027
  have hstable : (prefixWord ++ tailWord_3489027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489027).length < 2 ^ (prefixWord ++ tailWord_3489027).sum := by decide
  have hdescent : baseEnd_3489027 < baseStart_3489027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489064 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_3489064 : Nat := 118140960795 + 3489064 * 2 ^ 59
def prefixEnd_3489064 : Nat := 4983230072969 + 3 ^ 40 * 3489064 * 2
def baseEnd_3489064 : Nat := 1791566866298842254754093

theorem tailTrace_3489064 : CollatzResearch.WordTrace tailWord_3489064 prefixEnd_3489064 1791566866298842254754093 := by
  unfold tailWord_3489064
  simp only [CollatzResearch.WordTrace]
  refine ⟨63628309315862243767753123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84837745754482991690337497 63628309315862243767753123)
  ·
    refine ⟨95442463973793365651629685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63628309315862243767753123 95442463973793365651629685)
    ·
      refine ⟨8947730997543128029840283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95442463973793365651629685 8947730997543128029840283)
      ·
        refine ⟨13421596496314692044760425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8947730997543128029840283 13421596496314692044760425)
        ·
          refine ⟨10066197372236019033570319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13421596496314692044760425 10066197372236019033570319)
          ·
            refine ⟨15099296058354028550355479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066197372236019033570319 15099296058354028550355479)
            ·
              refine ⟨22648944087531042825533219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15099296058354028550355479 22648944087531042825533219)
              ·
                refine ⟨33973416131296564238299829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22648944087531042825533219 33973416131296564238299829)
                ·
                  refine ⟨3185007762309052897340609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33973416131296564238299829 3185007762309052897340609)
                  ·
                    refine ⟨2388755821731789673005457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3185007762309052897340609 2388755821731789673005457)
                    ·
                      refine ⟨1791566866298842254754093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388755821731789673005457 1791566866298842254754093)
                      ·
                        rfl

theorem cell23_3489064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_3489064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489064 prefixEnd_3489064 := by exact prefixLift 3489064
  have htrace : WordTrace (prefixWord ++ tailWord_3489064) baseStart_3489064 baseEnd_3489064 := by
    simpa [prefixWord, tailWord_3489064, baseEnd_3489064] using wordTrace_append hprefix tailTrace_3489064
  have hstable : (prefixWord ++ tailWord_3489064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489064).length < 2 ^ (prefixWord ++ tailWord_3489064).sum := by decide
  have hdescent : baseEnd_3489064 < baseStart_3489064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489078 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3489078 : Nat := 118140960795 + 3489078 * 2 ^ 59
def prefixEnd_3489078 : Nat := 4983230072969 + 3 ^ 40 * 3489078 * 2
def baseEnd_3489078 : Nat := 597191351676001733326343

theorem tailTrace_3489078 : CollatzResearch.WordTrace tailWord_3489078 prefixEnd_3489078 597191351676001733326343 := by
  unfold tailWord_3489078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953570578354610495407243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84838086169115845284343925 7953570578354610495407243)
  ·
    refine ⟨11930355867531915743110865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7953570578354610495407243 11930355867531915743110865)
    ·
      refine ⟨8947766900648936807333149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11930355867531915743110865 8947766900648936807333149)
      ·
        refine ⟨3355412587743351302749931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8947766900648936807333149 3355412587743351302749931)
        ·
          refine ⟨5033118881615026954124897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3355412587743351302749931 5033118881615026954124897)
          ·
            refine ⟨3774839161211270215593673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5033118881615026954124897 3774839161211270215593673)
            ·
              refine ⟨2831129370908452661695255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774839161211270215593673 2831129370908452661695255)
              ·
                refine ⟨4246694056362678992542883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831129370908452661695255 4246694056362678992542883)
                ·
                  refine ⟨6370041084544018488814325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246694056362678992542883 6370041084544018488814325)
                  ·
                    refine ⟨597191351676001733326343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6370041084544018488814325 597191351676001733326343)
                    ·
                      rfl

theorem cell23_3489078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3489078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489078 prefixEnd_3489078 := by exact prefixLift 3489078
  have htrace : WordTrace (prefixWord ++ tailWord_3489078) baseStart_3489078 baseEnd_3489078 := by
    simpa [prefixWord, tailWord_3489078, baseEnd_3489078] using wordTrace_append hprefix tailTrace_3489078
  have hstable : (prefixWord ++ tailWord_3489078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489078).length < 2 ^ (prefixWord ++ tailWord_3489078).sum := by decide
  have hdescent : baseEnd_3489078 < baseStart_3489078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489081 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3489081 : Nat := 118140960795 + 3489081 * 2 ^ 59
def prefixEnd_3489081 : Nat := 4983230072969 + 3 ^ 40 * 3489081 * 2
def baseEnd_3489081 : Nat := 1791575595469968688241515

theorem tailTrace_3489081 : CollatzResearch.WordTrace tailWord_3489081 prefixEnd_3489081 1791575595469968688241515 := by
  unfold tailWord_3489081
  simp only [CollatzResearch.WordTrace]
  refine ⟨127257238672662899438875097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84838159115108599625916731 127257238672662899438875097)
  ·
    refine ⟨95442929004497174579156323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127257238672662899438875097 95442929004497174579156323)
    ·
      refine ⟨143164393506745761868734485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95442929004497174579156323 143164393506745761868734485)
      ·
        refine ⟨6710830945628707587596929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143164393506745761868734485 6710830945628707587596929)
        ·
          refine ⟨5033123209221530690697697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6710830945628707587596929 5033123209221530690697697)
          ·
            refine ⟨3774842406916148018023273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5033123209221530690697697 3774842406916148018023273)
            ·
              refine ⟨2831131805187111013517455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774842406916148018023273 2831131805187111013517455)
              ·
                refine ⟨4246697707780666520276183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831131805187111013517455 4246697707780666520276183)
                ·
                  refine ⟨6370046561670999780414275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246697707780666520276183 6370046561670999780414275)
                  ·
                    refine ⟨9555069842506499670621413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370046561670999780414275 9555069842506499670621413)
                    ·
                      refine ⟨1791575595469968688241515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9555069842506499670621413 1791575595469968688241515)
                      ·
                        rfl

theorem cell23_3489081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3489081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489081 prefixEnd_3489081 := by exact prefixLift 3489081
  have htrace : WordTrace (prefixWord ++ tailWord_3489081) baseStart_3489081 baseEnd_3489081 := by
    simpa [prefixWord, tailWord_3489081, baseEnd_3489081] using wordTrace_append hprefix tailTrace_3489081
  have hstable : (prefixWord ++ tailWord_3489081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489081).length < 2 ^ (prefixWord ++ tailWord_3489081).sum := by decide
  have hdescent : baseEnd_3489081 < baseStart_3489081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489084 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_3489084 : Nat := 118140960795 + 3489084 * 2 ^ 59
def prefixEnd_3489084 : Nat := 4983230072969 + 3 ^ 40 * 3489084 * 2
def baseEnd_3489084 : Nat := 1791577135911932176504001

theorem tailTrace_3489084 : CollatzResearch.WordTrace tailWord_3489084 prefixEnd_3489084 1791577135911932176504001 := by
  unfold tailWord_3489084
  simp only [CollatzResearch.WordTrace]
  refine ⟨63628674045826015475617153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84838232061101353967489537 63628674045826015475617153)
  ·
    refine ⟨47721505534369511606712865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63628674045826015475617153 47721505534369511606712865)
    ·
      refine ⟨35791129150777133705034649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47721505534369511606712865 35791129150777133705034649)
      ·
        refine ⟨26843346863082850278775987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35791129150777133705034649 26843346863082850278775987)
        ·
          refine ⟨40265020294624275418163981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26843346863082850278775987 40265020294624275418163981)
          ·
            refine ⟨15099382610484103281811493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40265020294624275418163981 15099382610484103281811493)
            ·
              refine ⟨2831134239465769365339655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15099382610484103281811493 2831134239465769365339655)
              ·
                refine ⟨4246701359198654048009483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831134239465769365339655 4246701359198654048009483)
                ·
                  refine ⟨6370052038797981072014225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246701359198654048009483 6370052038797981072014225)
                  ·
                    refine ⟨4777539029098485804010669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6370052038797981072014225 4777539029098485804010669)
                    ·
                      refine ⟨1791577135911932176504001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4777539029098485804010669 1791577135911932176504001)
                      ·
                        rfl

theorem cell23_3489084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_3489084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489084 prefixEnd_3489084 := by exact prefixLift 3489084
  have htrace : WordTrace (prefixWord ++ tailWord_3489084) baseStart_3489084 baseEnd_3489084 := by
    simpa [prefixWord, tailWord_3489084, baseEnd_3489084] using wordTrace_append hprefix tailTrace_3489084
  have hstable : (prefixWord ++ tailWord_3489084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489084).length < 2 ^ (prefixWord ++ tailWord_3489084).sum := by decide
  have hdescent : baseEnd_3489084 < baseStart_3489084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489124 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_3489124 : Nat := 118140960795 + 3489124 * 2 ^ 59
def prefixEnd_3489124 : Nat := 4983230072969 + 3 ^ 40 * 3489124 * 2
def baseEnd_3489124 : Nat := 1791597675138112020003817

theorem tailTrace_3489124 : CollatzResearch.WordTrace tailWord_3489124 prefixEnd_3489124 1791597675138112020003817 := by
  unfold tailWord_3489124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63629403505753558891345213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84839204674338078521793617 63629403505753558891345213)
  ·
    refine ⟨23861026314657584584254455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63629403505753558891345213 23861026314657584584254455)
    ·
      refine ⟨35791539471986376876381683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23861026314657584584254455 35791539471986376876381683)
      ·
        refine ⟨53687309207979565314572525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35791539471986376876381683 53687309207979565314572525)
        ·
          refine ⟨20132740952992336992964697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53687309207979565314572525 20132740952992336992964697)
          ·
            refine ⟨15099555714744252744723523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20132740952992336992964697 15099555714744252744723523)
            ·
              refine ⟨22649333572116379117085285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15099555714744252744723523 22649333572116379117085285)
              ·
                refine ⟨4246750044771821084453491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22649333572116379117085285 4246750044771821084453491)
                ·
                  refine ⟨6370125067157731626680237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246750044771821084453491 6370125067157731626680237)
                  ·
                    refine ⟨2388796900184149360005089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6370125067157731626680237 2388796900184149360005089)
                    ·
                      refine ⟨1791597675138112020003817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388796900184149360005089 1791597675138112020003817)
                      ·
                        rfl

theorem cell23_3489124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_3489124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489124 prefixEnd_3489124 := by exact prefixLift 3489124
  have htrace : WordTrace (prefixWord ++ tailWord_3489124) baseStart_3489124 baseEnd_3489124 := by
    simpa [prefixWord, tailWord_3489124, baseEnd_3489124] using wordTrace_append hprefix tailTrace_3489124
  have hstable : (prefixWord ++ tailWord_3489124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489124).length < 2 ^ (prefixWord ++ tailWord_3489124).sum := by decide
  have hdescent : baseEnd_3489124 < baseStart_3489124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489137 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 1, 4, 2]
def baseStart_3489137 : Nat := 118140960795 + 3489137 * 2 ^ 59
def prefixEnd_3489137 : Nat := 4983230072969 + 3 ^ 40 * 3489137 * 2
def baseEnd_3489137 : Nat := 1791604350386620469141257

theorem tailTrace_3489137 : CollatzResearch.WordTrace tailWord_3489137 prefixEnd_3489137 1791604350386620469141257 := by
  unfold tailWord_3489137
  simp only [CollatzResearch.WordTrace]
  refine ⟨127259281160460021002913665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84839520773640014001942443 127259281160460021002913665)
  ·
    refine ⟨95444460870345015752185249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127259281160460021002913665 95444460870345015752185249)
    ·
      refine ⟨71583345652758761814138937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95444460870345015752185249 71583345652758761814138937)
      ·
        refine ⟨53687509239569071360604203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71583345652758761814138937 53687509239569071360604203)
        ·
          refine ⟨80531263859353607040906305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53687509239569071360604203 80531263859353607040906305)
          ·
            refine ⟨60398447894515205280679729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80531263859353607040906305 60398447894515205280679729)
            ·
              refine ⟨45298835920886403960509797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60398447894515205280679729 45298835920886403960509797)
              ·
                refine ⟨8493531735166200742595587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45298835920886403960509797 8493531735166200742595587)
                ·
                  refine ⟨12740297602749301113893381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8493531735166200742595587 12740297602749301113893381)
                  ·
                    refine ⟨2388805800515493958855009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12740297602749301113893381 2388805800515493958855009)
                    ·
                      refine ⟨1791604350386620469141257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388805800515493958855009 1791604350386620469141257)
                      ·
                        rfl

theorem cell23_3489137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_3489137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489137 prefixEnd_3489137 := by exact prefixLift 3489137
  have htrace : WordTrace (prefixWord ++ tailWord_3489137) baseStart_3489137 baseEnd_3489137 := by
    simpa [prefixWord, tailWord_3489137, baseEnd_3489137] using wordTrace_append hprefix tailTrace_3489137
  have hstable : (prefixWord ++ tailWord_3489137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489137).length < 2 ^ (prefixWord ++ tailWord_3489137).sum := by decide
  have hdescent : baseEnd_3489137 < baseStart_3489137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489210 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_3489210 : Nat := 118140960795 + 3489210 * 2 ^ 59
def prefixEnd_3489210 : Nat := 4983230072969 + 3 ^ 40 * 3489210 * 2
def baseEnd_3489210 : Nat := 1791641834474398683528421

theorem tailTrace_3489210 : CollatzResearch.WordTrace tailWord_3489210 prefixEnd_3489210 1791641834474398683528421 := by
  unfold tailWord_3489210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31815485922298888617580271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84841295792797036313547389 31815485922298888617580271)
  ·
    refine ⟨47723228883448332926370407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31815485922298888617580271 47723228883448332926370407)
    ·
      refine ⟨71584843325172499389555611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47723228883448332926370407 71584843325172499389555611)
      ·
        refine ⟨107377264987758749084333417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71584843325172499389555611 107377264987758749084333417)
        ·
          refine ⟨80532948740819061813250063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107377264987758749084333417 80532948740819061813250063)
          ·
            refine ⟨120799423111228592719875095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80532948740819061813250063 120799423111228592719875095)
            ·
              refine ⟨181199134666842889079812643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120799423111228592719875095 181199134666842889079812643)
              ·
                refine ⟨271798702000264333619718965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181199134666842889079812643 271798702000264333619718965)
                ·
                  refine ⟨25481128312524781276848653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271798702000264333619718965 25481128312524781276848653)
                  ·
                    refine ⟨9555423117196792978818245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25481128312524781276848653 9555423117196792978818245)
                    ·
                      refine ⟨1791641834474398683528421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9555423117196792978818245 1791641834474398683528421)
                      ·
                        rfl

theorem cell23_3489210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_3489210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489210 prefixEnd_3489210 := by exact prefixLift 3489210
  have htrace : WordTrace (prefixWord ++ tailWord_3489210) baseStart_3489210 baseEnd_3489210 := by
    simpa [prefixWord, tailWord_3489210, baseEnd_3489210] using wordTrace_append hprefix tailTrace_3489210
  have hstable : (prefixWord ++ tailWord_3489210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489210).length < 2 ^ (prefixWord ++ tailWord_3489210).sum := by decide
  have hdescent : baseEnd_3489210 < baseStart_3489210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489227 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 6, 2]
def baseStart_3489227 : Nat := 118140960795 + 3489227 * 2 ^ 59
def prefixEnd_3489227 : Nat := 4983230072969 + 3 ^ 40 * 3489227 * 2
def baseEnd_3489227 : Nat := 1791650563645525117015843

theorem tailTrace_3489227 : CollatzResearch.WordTrace tailWord_3489227 prefixEnd_3489227 1791650563645525117015843 := by
  unfold tailWord_3489227
  simp only [CollatzResearch.WordTrace]
  refine ⟨127262563730133966373689935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84841709153422644249126623 127262563730133966373689935)
  ·
    refine ⟨190893845595200949560534903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127262563730133966373689935 190893845595200949560534903)
    ·
      refine ⟨286340768392801424340802355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190893845595200949560534903 286340768392801424340802355)
      ·
        refine ⟨429511152589202136511203533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286340768392801424340802355 429511152589202136511203533)
        ·
          refine ⟨161066682220950801191701325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429511152589202136511203533 161066682220950801191701325)
          ·
            refine ⟨60400005832856550446887997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161066682220950801191701325 60400005832856550446887997)
            ·
              refine ⟨22650002187321206417582999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60400005832856550446887997 22650002187321206417582999)
              ·
                refine ⟨33975003280981809626374499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22650002187321206417582999 33975003280981809626374499)
                ·
                  refine ⟨50962504921472714439561749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33975003280981809626374499 50962504921472714439561749)
                  ·
                    refine ⟨2388867418194033489354457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50962504921472714439561749 2388867418194033489354457)
                    ·
                      refine ⟨1791650563645525117015843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388867418194033489354457 1791650563645525117015843)
                      ·
                        rfl

theorem cell23_3489227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 6, 2].length) (baseStart_3489227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489227 prefixEnd_3489227 := by exact prefixLift 3489227
  have htrace : WordTrace (prefixWord ++ tailWord_3489227) baseStart_3489227 baseEnd_3489227 := by
    simpa [prefixWord, tailWord_3489227, baseEnd_3489227] using wordTrace_append hprefix tailTrace_3489227
  have hstable : (prefixWord ++ tailWord_3489227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489227).length < 2 ^ (prefixWord ++ tailWord_3489227).sum := by decide
  have hdescent : baseEnd_3489227 < baseStart_3489227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489247 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_3489247 : Nat := 118140960795 + 3489247 * 2 ^ 59
def prefixEnd_3489247 : Nat := 4983230072969 + 3 ^ 40 * 3489247 * 2
def baseEnd_3489247 : Nat := 1791660833258615038765751

theorem tailTrace_3489247 : CollatzResearch.WordTrace tailWord_3489247 prefixEnd_3489247 1791660833258615038765751 := by
  unfold tailWord_3489247
  simp only [CollatzResearch.WordTrace]
  refine ⟨127263293190061509789417995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84842195460041006526278663 127263293190061509789417995)
  ·
    refine ⟨190894939785092264684126993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127263293190061509789417995 190894939785092264684126993)
    ·
      refine ⟨143171204838819198513095245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190894939785092264684126993 143171204838819198513095245)
      ·
        refine ⟨53689201814557199442410717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143171204838819198513095245 53689201814557199442410717)
        ·
          refine ⟨20133450680458949790904019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53689201814557199442410717 20133450680458949790904019)
          ·
            refine ⟨30200176020688424686356029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20133450680458949790904019 30200176020688424686356029)
            ·
              refine ⟨11325066007758159257383511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30200176020688424686356029 11325066007758159257383511)
              ·
                refine ⟨16987599011637238886075267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11325066007758159257383511 16987599011637238886075267)
                ·
                  refine ⟨25481398517455858329112901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16987599011637238886075267 25481398517455858329112901)
                  ·
                    refine ⟨4777762222022973436708669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25481398517455858329112901 4777762222022973436708669)
                    ·
                      refine ⟨1791660833258615038765751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4777762222022973436708669 1791660833258615038765751)
                      ·
                        rfl

theorem cell23_3489247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_3489247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489247 prefixEnd_3489247 := by exact prefixLift 3489247
  have htrace : WordTrace (prefixWord ++ tailWord_3489247) baseStart_3489247 baseEnd_3489247 := by
    simpa [prefixWord, tailWord_3489247, baseEnd_3489247] using wordTrace_append hprefix tailTrace_3489247
  have hstable : (prefixWord ++ tailWord_3489247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489247).length < 2 ^ (prefixWord ++ tailWord_3489247).sum := by decide
  have hdescent : baseEnd_3489247 < baseStart_3489247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489314 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3489314 : Nat := 118140960795 + 3489314 * 2 ^ 59
def prefixEnd_3489314 : Nat := 4983230072969 + 3 ^ 40 * 3489314 * 2
def baseEnd_3489314 : Nat := 597231745487488758875981

theorem tailTrace_3489314 : CollatzResearch.WordTrace tailWord_3489314 prefixEnd_3489314 597231745487488758875981 := by
  unfold tailWord_3489314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31816434220204695058026749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84843824587212520154737997 31816434220204695058026749)
  ·
    refine ⟨11931162832576760646760031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31816434220204695058026749 11931162832576760646760031)
    ·
      refine ⟨17896744248865140970140047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11931162832576760646760031 17896744248865140970140047)
      ·
        refine ⟨26845116373297711455210071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17896744248865140970140047 26845116373297711455210071)
        ·
          refine ⟨40267674559946567182815107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26845116373297711455210071 40267674559946567182815107)
          ·
            refine ⟨60401511839919850774222661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40267674559946567182815107 60401511839919850774222661)
            ·
              refine ⟨11325283469984972020166749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60401511839919850774222661 11325283469984972020166749)
              ·
                refine ⟨4246981301244364507562531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11325283469984972020166749 4246981301244364507562531)
                ·
                  refine ⟨6370471951866546761343797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246981301244364507562531 6370471951866546761343797)
                  ·
                    refine ⟨597231745487488758875981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6370471951866546761343797 597231745487488758875981)
                    ·
                      rfl

theorem cell23_3489314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3489314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489314 prefixEnd_3489314 := by exact prefixLift 3489314
  have htrace : WordTrace (prefixWord ++ tailWord_3489314) baseStart_3489314 baseEnd_3489314 := by
    simpa [prefixWord, tailWord_3489314, baseEnd_3489314] using wordTrace_append hprefix tailTrace_3489314
  have hstable : (prefixWord ++ tailWord_3489314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489314).length < 2 ^ (prefixWord ++ tailWord_3489314).sum := by decide
  have hdescent : baseEnd_3489314 < baseStart_3489314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489317 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3489317 : Nat := 118140960795 + 3489317 * 2 ^ 59
def prefixEnd_3489317 : Nat := 4983230072969 + 3 ^ 40 * 3489317 * 2
def baseEnd_3489317 : Nat := 1791696776904429764890429

theorem tailTrace_3489317 : CollatzResearch.WordTrace tailWord_3489317 prefixEnd_3489317 1791696776904429764890429 := by
  unfold tailWord_3489317
  simp only [CollatzResearch.WordTrace]
  refine ⟨127265846299807911744466205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84843897533205274496310803 127265846299807911744466205)
  ·
    refine ⟨47724692362427966904174827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127265846299807911744466205 47724692362427966904174827)
    ·
      refine ⟨71587038543641950356262241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47724692362427966904174827 71587038543641950356262241)
      ·
        refine ⟨53690278907731462767196681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71587038543641950356262241 53690278907731462767196681)
        ·
          refine ⟨40267709180798597075397511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53690278907731462767196681 40267709180798597075397511)
          ·
            refine ⟨60401563771197895613096267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40267709180798597075397511 60401563771197895613096267)
            ·
              refine ⟨90602345656796843419644401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60401563771197895613096267 90602345656796843419644401)
              ·
                refine ⟨67951759242597632564733301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90602345656796843419644401 67951759242597632564733301)
                ·
                  refine ⟨6370477428993528052943747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67951759242597632564733301 6370477428993528052943747)
                  ·
                    refine ⟨9555716143490292079415621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370477428993528052943747 9555716143490292079415621)
                    ·
                      refine ⟨1791696776904429764890429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9555716143490292079415621 1791696776904429764890429)
                      ·
                        rfl

theorem cell23_3489317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3489317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489317 prefixEnd_3489317 := by exact prefixLift 3489317
  have htrace : WordTrace (prefixWord ++ tailWord_3489317) baseStart_3489317 baseEnd_3489317 := by
    simpa [prefixWord, tailWord_3489317, baseEnd_3489317] using wordTrace_append hprefix tailTrace_3489317
  have hstable : (prefixWord ++ tailWord_3489317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489317).length < 2 ^ (prefixWord ++ tailWord_3489317).sum := by decide
  have hdescent : baseEnd_3489317 < baseStart_3489317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489354 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_3489354 : Nat := 118140960795 + 3489354 * 2 ^ 59
def prefixEnd_3489354 : Nat := 4983230072969 + 3 ^ 40 * 3489354 * 2
def baseEnd_3489354 : Nat := 1791715775688646120127759

theorem tailTrace_3489354 : CollatzResearch.WordTrace tailWord_3489354 prefixEnd_3489354 1791715775688646120127759 := by
  unfold tailWord_3489354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31816798950168466765890779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84844797200449244709042077 31816798950168466765890779)
  ·
    refine ⟨47725198425252700148836169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31816798950168466765890779 47725198425252700148836169)
    ·
      refine ⟨35793898818939525111627127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47725198425252700148836169 35793898818939525111627127)
      ·
        refine ⟨53690848228409287667440691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35793898818939525111627127 53690848228409287667440691)
        ·
          refine ⟨80536272342613931501161037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53690848228409287667440691 80536272342613931501161037)
          ·
            refine ⟨30201102128480224312935389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80536272342613931501161037 30201102128480224312935389)
            ·
              refine ⟨11325413298180084117350771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30201102128480224312935389 11325413298180084117350771)
              ·
                refine ⟨16988119947270126176026157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11325413298180084117350771 16988119947270126176026157)
                ·
                  refine ⟨6370544980226297316009809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16988119947270126176026157 6370544980226297316009809)
                  ·
                    refine ⟨4777908735169722987007357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6370544980226297316009809 4777908735169722987007357)
                    ·
                      refine ⟨1791715775688646120127759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4777908735169722987007357 1791715775688646120127759)
                      ·
                        rfl

theorem cell23_3489354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_3489354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489354 prefixEnd_3489354 := by exact prefixLift 3489354
  have htrace : WordTrace (prefixWord ++ tailWord_3489354) baseStart_3489354 baseEnd_3489354 := by
    simpa [prefixWord, tailWord_3489354, baseEnd_3489354] using wordTrace_append hprefix tailTrace_3489354
  have hstable : (prefixWord ++ tailWord_3489354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489354).length < 2 ^ (prefixWord ++ tailWord_3489354).sum := by decide
  have hdescent : baseEnd_3489354 < baseStart_3489354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489364 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3489364 : Nat := 118140960795 + 3489364 * 2 ^ 59
def prefixEnd_3489364 : Nat := 4983230072969 + 3 ^ 40 * 3489364 * 2
def baseEnd_3489364 : Nat := 1791720910495191081002713

theorem tailTrace_3489364 : CollatzResearch.WordTrace tailWord_3489364 prefixEnd_3489364 1791720910495191081002713 := by
  unfold tailWord_3489364
  simp only [CollatzResearch.WordTrace]
  refine ⟨63633780265318819385713573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84845040353758425847618097 63633780265318819385713573)
  ·
    refine ⟨11931333799747278634821295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63633780265318819385713573 11931333799747278634821295)
    ·
      refine ⟨17897000699620917952231943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11931333799747278634821295 17897000699620917952231943)
      ·
        refine ⟨26845501049431376928347915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17897000699620917952231943 26845501049431376928347915)
        ·
          refine ⟨40268251574147065392521873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26845501049431376928347915 40268251574147065392521873)
          ·
            refine ⟨30201188680610299044391405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40268251574147065392521873 30201188680610299044391405)
            ·
              refine ⟨11325445755228862141646777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30201188680610299044391405 11325445755228862141646777)
              ·
                refine ⟨8494084316421646606235083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11325445755228862141646777 8494084316421646606235083)
                ·
                  refine ⟨12741126474632469909352625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494084316421646606235083 12741126474632469909352625)
                  ·
                    refine ⟨9555844855974352432014469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12741126474632469909352625 9555844855974352432014469)
                    ·
                      refine ⟨1791720910495191081002713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9555844855974352432014469 1791720910495191081002713)
                      ·
                        rfl

theorem cell23_3489364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3489364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489364 prefixEnd_3489364 := by exact prefixLift 3489364
  have htrace : WordTrace (prefixWord ++ tailWord_3489364) baseStart_3489364 baseEnd_3489364 := by
    simpa [prefixWord, tailWord_3489364, baseEnd_3489364] using wordTrace_append hprefix tailTrace_3489364
  have hstable : (prefixWord ++ tailWord_3489364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489364).length < 2 ^ (prefixWord ++ tailWord_3489364).sum := by decide
  have hdescent : baseEnd_3489364 < baseStart_3489364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489368 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 1, 2, 2]
def baseStart_3489368 : Nat := 118140960795 + 3489368 * 2 ^ 59
def prefixEnd_3489368 : Nat := 4983230072969 + 3 ^ 40 * 3489368 * 2
def baseEnd_3489368 : Nat := 1791722964417809065352695

theorem tailTrace_3489368 : CollatzResearch.WordTrace tailWord_3489368 prefixEnd_3489368 1791722964417809065352695 := by
  unfold tailWord_3489368
  simp only [CollatzResearch.WordTrace]
  refine ⟨63633853211311573727286379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84845137615082098303048505 63633853211311573727286379)
  ·
    refine ⟨95450779816967360590929569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63633853211311573727286379 95450779816967360590929569)
    ·
      refine ⟨71588084862725520443197177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95450779816967360590929569 71588084862725520443197177)
      ·
        refine ⟨53691063647044140332397883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71588084862725520443197177 53691063647044140332397883)
        ·
          refine ⟨80536595470566210498596825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53691063647044140332397883 80536595470566210498596825)
          ·
            refine ⟨60402446602924657873947619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80536595470566210498596825 60402446602924657873947619)
            ·
              refine ⟨90603669904386986810921429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60402446602924657873947619 90603669904386986810921429)
              ·
                refine ⟨2123523513384070003380971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90603669904386986810921429 2123523513384070003380971)
                ·
                  refine ⟨3185285270076105005071457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123523513384070003380971 3185285270076105005071457)
                  ·
                    refine ⟨2388963952557078753803593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3185285270076105005071457 2388963952557078753803593)
                    ·
                      refine ⟨1791722964417809065352695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388963952557078753803593 1791722964417809065352695)
                      ·
                        rfl

theorem cell23_3489368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_3489368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489368 prefixEnd_3489368 := by exact prefixLift 3489368
  have htrace : WordTrace (prefixWord ++ tailWord_3489368) baseStart_3489368 baseEnd_3489368 := by
    simpa [prefixWord, tailWord_3489368, baseEnd_3489368] using wordTrace_append hprefix tailTrace_3489368
  have hstable : (prefixWord ++ tailWord_3489368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489368).length < 2 ^ (prefixWord ++ tailWord_3489368).sum := by decide
  have hdescent : baseEnd_3489368 < baseStart_3489368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489374 : List Nat := [4, 4, 1, 14]
def baseStart_3489374 : Nat := 118140960795 + 3489374 * 2 ^ 59
def prefixEnd_3489374 : Nat := 4983230072969 + 3 ^ 40 * 3489374 * 2
def baseEnd_3489374 : Nat := 819262023457583924041

theorem tailTrace_3489374 : CollatzResearch.WordTrace tailWord_3489374 prefixEnd_3489374 819262023457583924041 := by
  unfold tailWord_3489374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908490657575176309911397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84845283507067606986194117 15908490657575176309911397)
  ·
    refine ⟨2982841998295345558108387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15908490657575176309911397 2982841998295345558108387)
    ·
      refine ⟨4474262997443018337162581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2982841998295345558108387 4474262997443018337162581)
      ·
        refine ⟨819262023457583924041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 4474262997443018337162581 819262023457583924041)
        ·
          rfl

theorem cell23_3489374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 14].length) (baseStart_3489374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489374 prefixEnd_3489374 := by exact prefixLift 3489374
  have htrace : WordTrace (prefixWord ++ tailWord_3489374) baseStart_3489374 baseEnd_3489374 := by
    simpa [prefixWord, tailWord_3489374, baseEnd_3489374] using wordTrace_append hprefix tailTrace_3489374
  have hstable : (prefixWord ++ tailWord_3489374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489374).length < 2 ^ (prefixWord ++ tailWord_3489374).sum := by decide
  have hdescent : baseEnd_3489374 < baseStart_3489374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489385 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 1, 2, 2]
def baseStart_3489385 : Nat := 118140960795 + 3489385 * 2 ^ 59
def prefixEnd_3489385 : Nat := 4983230072969 + 3 ^ 40 * 3489385 * 2
def baseEnd_3489385 : Nat := 1791731693588935498840117

theorem tailTrace_3489385 : CollatzResearch.WordTrace tailWord_3489385 prefixEnd_3489385 1791731693588935498840117 := by
  unfold tailWord_3489385
  simp only [CollatzResearch.WordTrace]
  refine ⟨127268326463561559357941609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84845550975707706238627739 127268326463561559357941609)
  ·
    refine ⟨95451244847671169518456207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127268326463561559357941609 95451244847671169518456207)
    ·
      refine ⟨143176867271506754277684311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95451244847671169518456207 143176867271506754277684311)
      ·
        refine ⟨214765300907260131416526467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143176867271506754277684311 214765300907260131416526467)
        ·
          refine ⟨322147951360890197124789701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214765300907260131416526467 322147951360890197124789701)
          ·
            refine ⟨60402740880166911960898069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322147951360890197124789701 60402740880166911960898069)
            ·
              refine ⟨2831378478757823998167097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60402740880166911960898069 2831378478757823998167097)
              ·
                refine ⟨2123533859068367998625323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831378478757823998167097 2123533859068367998625323)
                ·
                  refine ⟨3185300788602551997937985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123533859068367998625323 3185300788602551997937985)
                  ·
                    refine ⟨2388975591451913998453489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3185300788602551997937985 2388975591451913998453489)
                    ·
                      refine ⟨1791731693588935498840117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388975591451913998453489 1791731693588935498840117)
                      ·
                        rfl

theorem cell23_3489385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 2, 2].length) (baseStart_3489385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489385 prefixEnd_3489385 := by exact prefixLift 3489385
  have htrace : WordTrace (prefixWord ++ tailWord_3489385) baseStart_3489385 baseEnd_3489385 := by
    simpa [prefixWord, tailWord_3489385, baseEnd_3489385] using wordTrace_append hprefix tailTrace_3489385
  have hstable : (prefixWord ++ tailWord_3489385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489385).length < 2 ^ (prefixWord ++ tailWord_3489385).sum := by decide
  have hdescent : baseEnd_3489385 < baseStart_3489385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489401 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3489401 : Nat := 118140960795 + 3489401 * 2 ^ 59
def prefixEnd_3489401 : Nat := 4983230072969 + 3 ^ 40 * 3489401 * 2
def baseEnd_3489401 : Nat := 1791739909279407436240043

theorem tailTrace_3489401 : CollatzResearch.WordTrace tailWord_3489401 prefixEnd_3489401 1791739909279407436240043 := by
  unfold tailWord_3489401
  simp only [CollatzResearch.WordTrace]
  refine ⟨127268910031503594090524057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84845940021002396060349371 127268910031503594090524057)
  ·
    refine ⟨95451682523627695567893043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127268910031503594090524057 95451682523627695567893043)
    ·
      refine ⟨143177523785441543351839565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95451682523627695567893043 143177523785441543351839565)
      ·
        refine ⟨53691571419540578756939837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143177523785441543351839565 53691571419540578756939837)
        ·
          refine ⟨20134339282327717033852439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53691571419540578756939837 20134339282327717033852439)
          ·
            refine ⟨30201508923491575550778659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20134339282327717033852439 30201508923491575550778659)
            ·
              refine ⟨45302263385237363326167989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30201508923491575550778659 45302263385237363326167989)
              ·
                refine ⟨4247087192366002811828249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45302263385237363326167989 4247087192366002811828249)
                ·
                  refine ⟨3185315394274502108871187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4247087192366002811828249 3185315394274502108871187)
                  ·
                    refine ⟨4777973091411753163306781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3185315394274502108871187 4777973091411753163306781)
                    ·
                      refine ⟨1791739909279407436240043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4777973091411753163306781 1791739909279407436240043)
                      ·
                        rfl

theorem cell23_3489401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3489401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489401 prefixEnd_3489401 := by exact prefixLift 3489401
  have htrace : WordTrace (prefixWord ++ tailWord_3489401) baseStart_3489401 baseEnd_3489401 := by
    simpa [prefixWord, tailWord_3489401, baseEnd_3489401] using wordTrace_append hprefix tailTrace_3489401
  have hstable : (prefixWord ++ tailWord_3489401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489401).length < 2 ^ (prefixWord ++ tailWord_3489401).sum := by decide
  have hdescent : baseEnd_3489401 < baseStart_3489401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489411 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 1, 3, 2]
def baseStart_3489411 : Nat := 118140960795 + 3489411 * 2 ^ 59
def prefixEnd_3489411 : Nat := 4983230072969 + 3 ^ 40 * 3489411 * 2
def baseEnd_3489411 : Nat := 1791745044085952397114997

theorem tailTrace_3489411 : CollatzResearch.WordTrace tailWord_3489411 prefixEnd_3489411 1791745044085952397114997 := by
  unfold tailWord_3489411
  simp only [CollatzResearch.WordTrace]
  refine ⟨127269274761467365798388087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84846183174311577198925391 127269274761467365798388087)
  ·
    refine ⟨190903912142201048697582131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127269274761467365798388087 190903912142201048697582131)
    ·
      refine ⟨286355868213301573046373197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190903912142201048697582131 286355868213301573046373197)
      ·
        refine ⟨107383450579988089892389949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286355868213301573046373197 107383450579988089892389949)
        ·
          refine ⟨40268793967495533709646231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107383450579988089892389949 40268793967495533709646231)
          ·
            refine ⟨60403190951243300564469347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40268793967495533709646231 60403190951243300564469347)
            ·
              refine ⟨90604786426864950846704021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60403190951243300564469347 90604786426864950846704021)
              ·
                refine ⟨4247099363759294570939251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90604786426864950846704021 4247099363759294570939251)
                ·
                  refine ⟨6370649045638941856408877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247099363759294570939251 6370649045638941856408877)
                  ·
                    refine ⟨2388993392114603196153329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6370649045638941856408877 2388993392114603196153329)
                    ·
                      refine ⟨1791745044085952397114997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2388993392114603196153329 1791745044085952397114997)
                      ·
                        rfl

theorem cell23_3489411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_3489411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489411 prefixEnd_3489411 := by exact prefixLift 3489411
  have htrace : WordTrace (prefixWord ++ tailWord_3489411) baseStart_3489411 baseEnd_3489411 := by
    simpa [prefixWord, tailWord_3489411, baseEnd_3489411] using wordTrace_append hprefix tailTrace_3489411
  have hstable : (prefixWord ++ tailWord_3489411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489411).length < 2 ^ (prefixWord ++ tailWord_3489411).sum := by decide
  have hdescent : baseEnd_3489411 < baseStart_3489411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489458 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_3489458 : Nat := 118140960795 + 3489458 * 2 ^ 59
def prefixEnd_3489458 : Nat := 4983230072969 + 3 ^ 40 * 3489458 * 2
def baseEnd_3489458 : Nat := 1791769177676713713227281

theorem tailTrace_3489458 : CollatzResearch.WordTrace tailWord_3489458 prefixEnd_3489458 1791769177676713713227281 := by
  unfold tailWord_3489458
  simp only [CollatzResearch.WordTrace]
  refine ⟨31817747248074273206337257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84847325994864728550232685 31817747248074273206337257)
  ·
    refine ⟨23863310436055704904752943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31817747248074273206337257 23863310436055704904752943)
    ·
      refine ⟨35794965654083557357129415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23863310436055704904752943 35794965654083557357129415)
      ·
        refine ⟨53692448481125336035694123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35794965654083557357129415 53692448481125336035694123)
        ·
          refine ⟨80538672721688004053541185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53692448481125336035694123 80538672721688004053541185)
          ·
            refine ⟨60404004541266003040155889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80538672721688004053541185 60404004541266003040155889)
            ·
              refine ⟨45303003405949502280116917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60404004541266003040155889 45303003405949502280116917)
              ·
                refine ⟨4247156569307765838760961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45303003405949502280116917 4247156569307765838760961)
                ·
                  refine ⟨3185367426980824379070721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4247156569307765838760961 3185367426980824379070721)
                  ·
                    refine ⟨2389025570235618284303041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3185367426980824379070721 2389025570235618284303041)
                    ·
                      refine ⟨1791769177676713713227281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389025570235618284303041 1791769177676713713227281)
                      ·
                        rfl

theorem cell23_3489458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_3489458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489458 prefixEnd_3489458 := by exact prefixLift 3489458
  have htrace : WordTrace (prefixWord ++ tailWord_3489458) baseStart_3489458 baseEnd_3489458 := by
    simpa [prefixWord, tailWord_3489458, baseEnd_3489458] using wordTrace_append hprefix tailTrace_3489458
  have hstable : (prefixWord ++ tailWord_3489458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489458).length < 2 ^ (prefixWord ++ tailWord_3489458).sum := by decide
  have hdescent : baseEnd_3489458 < baseStart_3489458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489462 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3489462 : Nat := 118140960795 + 3489462 * 2 ^ 59
def prefixEnd_3489462 : Nat := 4983230072969 + 3 ^ 40 * 3489462 * 2
def baseEnd_3489462 : Nat := 1791771231599331697577263

theorem tailTrace_3489462 : CollatzResearch.WordTrace tailWord_3489462 prefixEnd_3489462 1791771231599331697577263 := by
  unfold tailWord_3489462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954445930267662594280915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84847423256188401005663093 7954445930267662594280915)
  ·
    refine ⟨11931668895401493891421373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7954445930267662594280915 11931668895401493891421373)
    ·
      refine ⟨4474375835775560209283015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11931668895401493891421373 4474375835775560209283015)
      ·
        refine ⟨6711563753663340313924523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474375835775560209283015 6711563753663340313924523)
        ·
          refine ⟨10067345630495010470886785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711563753663340313924523 10067345630495010470886785)
          ·
            refine ⟨7550509222871257853165089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10067345630495010470886785 7550509222871257853165089)
            ·
              refine ⟨5662881917153443389873817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7550509222871257853165089 5662881917153443389873817)
              ·
                refine ⟨4247161437865082542405363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662881917153443389873817 4247161437865082542405363)
                ·
                  refine ⟨6370742156797623813608045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247161437865082542405363 6370742156797623813608045)
                  ·
                    refine ⟨2389028308799108930103017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6370742156797623813608045 2389028308799108930103017)
                    ·
                      refine ⟨1791771231599331697577263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389028308799108930103017 1791771231599331697577263)
                      ·
                        rfl

theorem cell23_3489462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3489462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489462 prefixEnd_3489462 := by exact prefixLift 3489462
  have htrace : WordTrace (prefixWord ++ tailWord_3489462) baseStart_3489462 baseEnd_3489462 := by
    simpa [prefixWord, tailWord_3489462, baseEnd_3489462] using wordTrace_append hprefix tailTrace_3489462
  have hstable : (prefixWord ++ tailWord_3489462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489462).length < 2 ^ (prefixWord ++ tailWord_3489462).sum := by decide
  have hdescent : baseEnd_3489462 < baseStart_3489462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489478 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3489478 : Nat := 118140960795 + 3489478 * 2 ^ 59
def prefixEnd_3489478 : Nat := 4983230072969 + 3 ^ 40 * 3489478 * 2
def baseEnd_3489478 : Nat := 1791779447289803634977189

theorem tailTrace_3489478 : CollatzResearch.WordTrace tailWord_3489478 prefixEnd_3489478 1791779447289803634977189 := by
  unfold tailWord_3489478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977241201632019882533659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84847812301483090827384725 3977241201632019882533659)
  ·
    refine ⟨5965861802448029823800489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977241201632019882533659 5965861802448029823800489)
    ·
      refine ⟨4474396351836022367850367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5965861802448029823800489 4474396351836022367850367)
      ·
        refine ⟨6711594527754033551775551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474396351836022367850367 6711594527754033551775551)
        ·
          refine ⟨10067391791631050327663327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711594527754033551775551 10067391791631050327663327)
          ·
            refine ⟨15101087687446575491494991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067391791631050327663327 15101087687446575491494991)
            ·
              refine ⟨22651631531169863237242487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15101087687446575491494991 22651631531169863237242487)
              ·
                refine ⟨33977447296754794855863731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22651631531169863237242487 33977447296754794855863731)
                ·
                  refine ⟨50966170945132192283795597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33977447296754794855863731 50966170945132192283795597)
                  ·
                    refine ⟨19112314104424572106423349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50966170945132192283795597 19112314104424572106423349)
                    ·
                      refine ⟨1791779447289803634977189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19112314104424572106423349 1791779447289803634977189)
                      ·
                        rfl

theorem cell23_3489478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3489478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489478 prefixEnd_3489478 := by exact prefixLift 3489478
  have htrace : WordTrace (prefixWord ++ tailWord_3489478) baseStart_3489478 baseEnd_3489478 := by
    simpa [prefixWord, tailWord_3489478, baseEnd_3489478] using wordTrace_append hprefix tailTrace_3489478
  have hstable : (prefixWord ++ tailWord_3489478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489478).length < 2 ^ (prefixWord ++ tailWord_3489478).sum := by decide
  have hdescent : baseEnd_3489478 < baseStart_3489478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489487 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_3489487 : Nat := 118140960795 + 3489487 * 2 ^ 59
def prefixEnd_3489487 : Nat := 4983230072969 + 3 ^ 40 * 3489487 * 2
def baseEnd_3489487 : Nat := 1791784068615694099764647

theorem tailTrace_3489487 : CollatzResearch.WordTrace tailWord_3489487 prefixEnd_3489487 1791784068615694099764647 := by
  unfold tailWord_3489487
  simp only [CollatzResearch.WordTrace]
  refine ⟨127272046709192030778154715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84848031139461353852103143 127272046709192030778154715)
  ·
    refine ⟨190908070063788046167232073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127272046709192030778154715 190908070063788046167232073)
    ·
      refine ⟨143181052547841034625424055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190908070063788046167232073 143181052547841034625424055)
      ·
        refine ⟨214771578821761551938136083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143181052547841034625424055 214771578821761551938136083)
        ·
          refine ⟨322157368232642327907204125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214771578821761551938136083 322157368232642327907204125)
          ·
            refine ⟨120809013087240872965201547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322157368232642327907204125 120809013087240872965201547)
            ·
              refine ⟨181213519630861309447802321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120809013087240872965201547 181213519630861309447802321)
              ·
                refine ⟨135910139723145982085851741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181213519630861309447802321 135910139723145982085851741)
                ·
                  refine ⟨50966302396179743282194403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135910139723145982085851741 50966302396179743282194403)
                  ·
                    refine ⟨76449453594269614923291605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50966302396179743282194403 76449453594269614923291605)
                    ·
                      refine ⟨1791784068615694099764647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76449453594269614923291605 1791784068615694099764647)
                      ·
                        rfl

theorem cell23_3489487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_3489487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489487 prefixEnd_3489487 := by exact prefixLift 3489487
  have htrace : WordTrace (prefixWord ++ tailWord_3489487) baseStart_3489487 baseEnd_3489487 := by
    simpa [prefixWord, tailWord_3489487, baseEnd_3489487] using wordTrace_append hprefix tailTrace_3489487
  have hstable : (prefixWord ++ tailWord_3489487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489487).length < 2 ^ (prefixWord ++ tailWord_3489487).sum := by decide
  have hdescent : baseEnd_3489487 < baseStart_3489487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489498 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_3489498 : Nat := 118140960795 + 3489498 * 2 ^ 59
def prefixEnd_3489498 : Nat := 4983230072969 + 3 ^ 40 * 3489498 * 2
def baseEnd_3489498 : Nat := 199087746322543728525233

theorem tailTrace_3489498 : CollatzResearch.WordTrace tailWord_3489498 prefixEnd_3489498 199087746322543728525233 := by
  unfold tailWord_3489498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31818111978038044914201287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84848298608101453104536765 31818111978038044914201287)
  ·
    refine ⟨47727167967057067371301931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31818111978038044914201287 47727167967057067371301931)
    ·
      refine ⟨71590751950585601056952897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47727167967057067371301931 71590751950585601056952897)
      ·
        refine ⟨53693063962939200792714673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71590751950585601056952897 53693063962939200792714673)
        ·
          refine ⟨40269797972204400594536005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53693063962939200792714673 40269797972204400594536005)
          ·
            refine ⟨7550587119788325111475501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40269797972204400594536005 7550587119788325111475501)
            ·
              refine ⟨2831470169920621916803313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7550587119788325111475501 2831470169920621916803313)
              ·
                refine ⟨2123602627440466437602485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831470169920621916803313 2123602627440466437602485)
                ·
                  refine ⟨199087746322543728525233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2123602627440466437602485 199087746322543728525233)
                  ·
                    rfl

theorem cell23_3489498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_3489498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489498 prefixEnd_3489498 := by exact prefixLift 3489498
  have htrace : WordTrace (prefixWord ++ tailWord_3489498) baseStart_3489498 baseEnd_3489498 := by
    simpa [prefixWord, tailWord_3489498, baseEnd_3489498] using wordTrace_append hprefix tailTrace_3489498
  have hstable : (prefixWord ++ tailWord_3489498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489498).length < 2 ^ (prefixWord ++ tailWord_3489498).sum := by decide
  have hdescent : baseEnd_3489498 < baseStart_3489498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489514 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_3489514 : Nat := 118140960795 + 3489514 * 2 ^ 59
def prefixEnd_3489514 : Nat := 4983230072969 + 3 ^ 40 * 3489514 * 2
def baseEnd_3489514 : Nat := 1791797932593365494127023

theorem tailTrace_3489514 : CollatzResearch.WordTrace tailWord_3489514 prefixEnd_3489514 1791797932593365494127023 := by
  unfold tailWord_3489514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31818257870023553597346899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84848687653396142926258397 31818257870023553597346899)
  ·
    refine ⟨47727386805035330396020349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31818257870023553597346899 47727386805035330396020349)
    ·
      refine ⟨17897770051888248898507631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47727386805035330396020349 17897770051888248898507631)
      ·
        refine ⟨26846655077832373347761447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17897770051888248898507631 26846655077832373347761447)
        ·
          refine ⟨40269982616748560021642171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26846655077832373347761447 40269982616748560021642171)
          ·
            refine ⟨60404973925122840032463257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40269982616748560021642171 60404973925122840032463257)
            ·
              refine ⟨45303730443842130024347443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60404973925122840032463257 45303730443842130024347443)
              ·
                refine ⟨67955595665763195036521165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45303730443842130024347443 67955595665763195036521165)
                ·
                  refine ⟨25483348374661198138695437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67955595665763195036521165 25483348374661198138695437)
                  ·
                    refine ⟨9556255640497949302010789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25483348374661198138695437 9556255640497949302010789)
                    ·
                      refine ⟨1791797932593365494127023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9556255640497949302010789 1791797932593365494127023)
                      ·
                        rfl

theorem cell23_3489514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_3489514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489514 prefixEnd_3489514 := by exact prefixLift 3489514
  have htrace : WordTrace (prefixWord ++ tailWord_3489514) baseStart_3489514 baseEnd_3489514 := by
    simpa [prefixWord, tailWord_3489514, baseEnd_3489514] using wordTrace_append hprefix tailTrace_3489514
  have hstable : (prefixWord ++ tailWord_3489514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489514).length < 2 ^ (prefixWord ++ tailWord_3489514).sum := by decide
  have hdescent : baseEnd_3489514 < baseStart_3489514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489544 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3489544 : Nat := 118140960795 + 3489544 * 2 ^ 59
def prefixEnd_3489544 : Nat := 4983230072969 + 3 ^ 40 * 3489544 * 2
def baseEnd_3489544 : Nat := 1791813337013000376751885

theorem tailTrace_3489544 : CollatzResearch.WordTrace tailWord_3489544 prefixEnd_3489544 1791813337013000376751885 := by
  unfold tailWord_3489544
  simp only [CollatzResearch.WordTrace]
  refine ⟨63637062834992764756489843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84849417113323686341986457 63637062834992764756489843)
  ·
    refine ⟨95455594252489147134734765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63637062834992764756489843 95455594252489147134734765)
    ·
      refine ⟨35795847844683430175525537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95455594252489147134734765 35795847844683430175525537)
      ·
        refine ⟨26846885883512572631644153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35795847844683430175525537 26846885883512572631644153)
        ·
          refine ⟨20135164412634429473733115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26846885883512572631644153 20135164412634429473733115)
          ·
            refine ⟨30202746618951644210599673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20135164412634429473733115 30202746618951644210599673)
            ·
              refine ⟨22652059964213733157949755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30202746618951644210599673 22652059964213733157949755)
              ·
                refine ⟨33978089946320599736924633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22652059964213733157949755 33978089946320599736924633)
                ·
                  refine ⟨25483567459740449802693475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33978089946320599736924633 25483567459740449802693475)
                  ·
                    refine ⟨38225351189610674704040213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25483567459740449802693475 38225351189610674704040213)
                    ·
                      refine ⟨1791813337013000376751885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38225351189610674704040213 1791813337013000376751885)
                      ·
                        rfl

theorem cell23_3489544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3489544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489544 prefixEnd_3489544 := by exact prefixLift 3489544
  have htrace : WordTrace (prefixWord ++ tailWord_3489544) baseStart_3489544 baseEnd_3489544 := by
    simpa [prefixWord, tailWord_3489544, baseEnd_3489544] using wordTrace_append hprefix tailTrace_3489544
  have hstable : (prefixWord ++ tailWord_3489544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489544).length < 2 ^ (prefixWord ++ tailWord_3489544).sum := by decide
  have hdescent : baseEnd_3489544 < baseStart_3489544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489549 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3489549 : Nat := 118140960795 + 3489549 * 2 ^ 59
def prefixEnd_3489549 : Nat := 4983230072969 + 3 ^ 40 * 3489549 * 2
def baseEnd_3489549 : Nat := 199090656046252539687707

theorem tailTrace_3489549 : CollatzResearch.WordTrace tailWord_3489549 prefixEnd_3489549 199090656046252539687707 := by
  unfold tailWord_3489549
  simp only [CollatzResearch.WordTrace]
  refine ⟨127274308034967415366911701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84849538689978276911274467 127274308034967415366911701)
  ·
    refine ⟨2982991594569548797661993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127274308034967415366911701 2982991594569548797661993)
    ·
      refine ⟨2237243695927161598246495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2982991594569548797661993 2237243695927161598246495)
      ·
        refine ⟨3355865543890742397369743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237243695927161598246495 3355865543890742397369743)
        ·
          refine ⟨5033798315836113596054615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3355865543890742397369743 5033798315836113596054615)
          ·
            refine ⟨7550697473754170394081923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5033798315836113596054615 7550697473754170394081923)
            ·
              refine ⟨11326046210631255591122885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550697473754170394081923 11326046210631255591122885)
              ·
                refine ⟨2123633664493360423335541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11326046210631255591122885 2123633664493360423335541)
                ·
                  refine ⟨199090656046252539687707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2123633664493360423335541 199090656046252539687707)
                  ·
                    rfl

theorem cell23_3489549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3489549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489549 prefixEnd_3489549 := by exact prefixLift 3489549
  have htrace : WordTrace (prefixWord ++ tailWord_3489549) baseStart_3489549 baseEnd_3489549 := by
    simpa [prefixWord, tailWord_3489549, baseEnd_3489549] using wordTrace_append hprefix tailTrace_3489549
  have hstable : (prefixWord ++ tailWord_3489549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489549).length < 2 ^ (prefixWord ++ tailWord_3489549).sum := by decide
  have hdescent : baseEnd_3489549 < baseStart_3489549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489582 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3489582 : Nat := 118140960795 + 3489582 * 2 ^ 59
def prefixEnd_3489582 : Nat := 4983230072969 + 3 ^ 40 * 3489582 * 2
def baseEnd_3489582 : Nat := 1791832849277871228076711

theorem tailTrace_3489582 : CollatzResearch.WordTrace tailWord_3489582 prefixEnd_3489582 1791832849277871228076711 := by
  unfold tailWord_3489582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909438955480982750357875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84850341095898574668575333 15909438955480982750357875)
  ·
    refine ⟨23864158433221474125536813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15909438955480982750357875 23864158433221474125536813)
    ·
      refine ⟨8949059412458052797076305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23864158433221474125536813 8949059412458052797076305)
      ·
        refine ⟨6711794559343539597807229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8949059412458052797076305 6711794559343539597807229)
        ·
          refine ⟨2516922959753827349177711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6711794559343539597807229 2516922959753827349177711)
          ·
            refine ⟨3775384439630741023766567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516922959753827349177711 3775384439630741023766567)
            ·
              refine ⟨5663076659446111535649851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775384439630741023766567 5663076659446111535649851)
              ·
                refine ⟨8494614989169167303474777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663076659446111535649851 8494614989169167303474777)
                ·
                  refine ⟨6370961241876875477606083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8494614989169167303474777 6370961241876875477606083)
                  ·
                    refine ⟨9556441862815313216409125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370961241876875477606083 9556441862815313216409125)
                    ·
                      refine ⟨1791832849277871228076711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9556441862815313216409125 1791832849277871228076711)
                      ·
                        rfl

theorem cell23_3489582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3489582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489582 prefixEnd_3489582 := by exact prefixLift 3489582
  have htrace : WordTrace (prefixWord ++ tailWord_3489582) baseStart_3489582 baseEnd_3489582 := by
    simpa [prefixWord, tailWord_3489582, baseEnd_3489582] using wordTrace_append hprefix tailTrace_3489582
  have hstable : (prefixWord ++ tailWord_3489582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489582).length < 2 ^ (prefixWord ++ tailWord_3489582).sum := by decide
  have hdescent : baseEnd_3489582 < baseStart_3489582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489614 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_3489614 : Nat := 118140960795 + 3489614 * 2 ^ 59
def prefixEnd_3489614 : Nat := 4983230072969 + 3 ^ 40 * 3489614 * 2
def baseEnd_3489614 : Nat := 597283093552938367625521

theorem tailTrace_3489614 : CollatzResearch.WordTrace tailWord_3489614 prefixEnd_3489614 597283093552938367625521 := by
  unfold tailWord_3489614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909584847466491433503487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84851119186487954312018597 15909584847466491433503487)
  ·
    refine ⟨23864377271199737150255231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15909584847466491433503487 23864377271199737150255231)
    ·
      refine ⟨35796565906799605725382847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23864377271199737150255231 35796565906799605725382847)
      ·
        refine ⟨53694848860199408588074271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35796565906799605725382847 53694848860199408588074271)
        ·
          refine ⟨80542273290299112882111407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53694848860199408588074271 80542273290299112882111407)
          ·
            refine ⟨120813409935448669323167111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80542273290299112882111407 120813409935448669323167111)
            ·
              refine ⟨181220114903173003984750667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120813409935448669323167111 181220114903173003984750667)
              ·
                refine ⟨271830172354759505977126001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181220114903173003984750667 271830172354759505977126001)
                ·
                  refine ⟨203872629266069629482844501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271830172354759505977126001 203872629266069629482844501)
                  ·
                    refine ⟨597283093552938367625521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 203872629266069629482844501 597283093552938367625521)
                    ·
                      rfl

theorem cell23_3489614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_3489614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489614 prefixEnd_3489614 := by exact prefixLift 3489614
  have htrace : WordTrace (prefixWord ++ tailWord_3489614) baseStart_3489614 baseEnd_3489614 := by
    simpa [prefixWord, tailWord_3489614, baseEnd_3489614] using wordTrace_append hprefix tailTrace_3489614
  have hstable : (prefixWord ++ tailWord_3489614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489614).length < 2 ^ (prefixWord ++ tailWord_3489614).sum := by decide
  have hdescent : baseEnd_3489614 < baseStart_3489614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489631 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 1, 6]
def baseStart_3489631 : Nat := 118140960795 + 3489631 * 2 ^ 59
def prefixEnd_3489631 : Nat := 4983230072969 + 3 ^ 40 * 3489631 * 2
def baseEnd_3489631 : Nat := 597286003276647178787995

theorem tailTrace_3489631 : CollatzResearch.WordTrace tailWord_3489631 prefixEnd_3489631 597286003276647178787995 := by
  unfold tailWord_3489631
  simp only [CollatzResearch.WordTrace]
  refine ⟨127277298820670343371396747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84851532547113562247597831 127277298820670343371396747)
  ·
    refine ⟨190915948231005515057095121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127277298820670343371396747 190915948231005515057095121)
    ·
      refine ⟨143186961173254136292821341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190915948231005515057095121 143186961173254136292821341)
      ·
        refine ⟨53695110439970301109808003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143186961173254136292821341 53695110439970301109808003)
        ·
          refine ⟨80542665659955451664712005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53695110439970301109808003 80542665659955451664712005)
          ·
            refine ⟨15101749811241647187133501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80542665659955451664712005 15101749811241647187133501)
            ·
              refine ⟨5663156179215617695175063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15101749811241647187133501 5663156179215617695175063)
              ·
                refine ⟨8494734268823426542762595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663156179215617695175063 8494734268823426542762595)
                ·
                  refine ⟨12742101403235139814143893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494734268823426542762595 12742101403235139814143893)
                  ·
                    refine ⟨597286003276647178787995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12742101403235139814143893 597286003276647178787995)
                    ·
                      rfl

theorem cell23_3489631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_3489631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489631 prefixEnd_3489631 := by exact prefixLift 3489631
  have htrace : WordTrace (prefixWord ++ tailWord_3489631) baseStart_3489631 baseEnd_3489631 := by
    simpa [prefixWord, tailWord_3489631, baseEnd_3489631] using wordTrace_append hprefix tailTrace_3489631
  have hstable : (prefixWord ++ tailWord_3489631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489631).length < 2 ^ (prefixWord ++ tailWord_3489631).sum := by decide
  have hdescent : baseEnd_3489631 < baseStart_3489631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489641 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_3489641 : Nat := 118140960795 + 3489641 * 2 ^ 59
def prefixEnd_3489641 : Nat := 4983230072969 + 3 ^ 40 * 3489641 * 2
def baseEnd_3489641 : Nat := 1791863144636486497238939

theorem tailTrace_3489641 : CollatzResearch.WordTrace tailWord_3489641 prefixEnd_3489641 1791863144636486497238939 := by
  unfold tailWord_3489641
  simp only [CollatzResearch.WordTrace]
  refine ⟨127277663550634115079260777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84851775700422743386173851 127277663550634115079260777)
  ·
    refine ⟨95458247662975586309445583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127277663550634115079260777 95458247662975586309445583)
    ·
      refine ⟨143187371494463379464168375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95458247662975586309445583 143187371494463379464168375)
      ·
        refine ⟨214781057241695069196252563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143187371494463379464168375 214781057241695069196252563)
        ·
          refine ⟨322171585862542603794378845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214781057241695069196252563 322171585862542603794378845)
          ·
            refine ⟨120814344698453476422892067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322171585862542603794378845 120814344698453476422892067)
            ·
              refine ⟨181221517047680214634338101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120814344698453476422892067 181221517047680214634338101)
              ·
                refine ⟨16989517223220020121969197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181221517047680214634338101 16989517223220020121969197)
                ·
                  refine ⟨6371068958707507545738449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16989517223220020121969197 6371068958707507545738449)
                  ·
                    refine ⟨4778301719030630659303837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6371068958707507545738449 4778301719030630659303837)
                    ·
                      refine ⟨1791863144636486497238939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4778301719030630659303837 1791863144636486497238939)
                      ·
                        rfl

theorem cell23_3489641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_3489641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489641 prefixEnd_3489641 := by exact prefixLift 3489641
  have htrace : WordTrace (prefixWord ++ tailWord_3489641) baseStart_3489641 baseEnd_3489641 := by
    simpa [prefixWord, tailWord_3489641, baseEnd_3489641] using wordTrace_append hprefix tailTrace_3489641
  have hstable : (prefixWord ++ tailWord_3489641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489641).length < 2 ^ (prefixWord ++ tailWord_3489641).sum := by decide
  have hdescent : baseEnd_3489641 < baseStart_3489641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489658 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_3489658 : Nat := 118140960795 + 3489658 * 2 ^ 59
def prefixEnd_3489658 : Nat := 4983230072969 + 3 ^ 40 * 3489658 * 2
def baseEnd_3489658 : Nat := 1791871873807612930726361

theorem tailTrace_3489658 : CollatzResearch.WordTrace tailWord_3489658 prefixEnd_3489658 1791871873807612930726361 := by
  unfold tailWord_3489658
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819570897893131745657407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84852189061048351321753085 31819570897893131745657407)
  ·
    refine ⟨47729356346839697618486111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31819570897893131745657407 47729356346839697618486111)
    ·
      refine ⟨71594034520259546427729167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47729356346839697618486111 71594034520259546427729167)
      ·
        refine ⟨107391051780389319641593751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71594034520259546427729167 107391051780389319641593751)
        ·
          refine ⟨161086577670583979462390627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107391051780389319641593751 161086577670583979462390627)
          ·
            refine ⟨241629866505875969193585941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161086577670583979462390627 241629866505875969193585941)
            ·
              refine ⟨11326399992462936055949341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241629866505875969193585941 11326399992462936055949341)
              ·
                refine ⟨4247399997173601020981003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11326399992462936055949341 4247399997173601020981003)
                ·
                  refine ⟨6371099995760401531471505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247399997173601020981003 6371099995760401531471505)
                  ·
                    refine ⟨4778324996820301148603629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6371099995760401531471505 4778324996820301148603629)
                    ·
                      refine ⟨1791871873807612930726361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4778324996820301148603629 1791871873807612930726361)
                      ·
                        rfl

theorem cell23_3489658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_3489658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489658 prefixEnd_3489658 := by exact prefixLift 3489658
  have htrace : WordTrace (prefixWord ++ tailWord_3489658) baseStart_3489658 baseEnd_3489658 := by
    simpa [prefixWord, tailWord_3489658, baseEnd_3489658] using wordTrace_append hprefix tailTrace_3489658
  have hstable : (prefixWord ++ tailWord_3489658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489658).length < 2 ^ (prefixWord ++ tailWord_3489658).sum := by decide
  have hdescent : baseEnd_3489658 < baseStart_3489658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489682 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3489682 : Nat := 118140960795 + 3489682 * 2 ^ 59
def prefixEnd_3489682 : Nat := 4983230072969 + 3 ^ 40 * 3489682 * 2
def baseEnd_3489682 : Nat := 597294732447773612275417

theorem tailTrace_3489682 : CollatzResearch.WordTrace tailWord_3489682 prefixEnd_3489682 597294732447773612275417 := by
  unfold tailWord_3489682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819789735871394770375825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84852772628990386054335533 31819789735871394770375825)
  ·
    refine ⟨23864842301903546077781869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31819789735871394770375825 23864842301903546077781869)
    ·
      refine ⟨8949315863213829779168201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23864842301903546077781869 8949315863213829779168201)
      ·
        refine ⟨6711986897410372334376151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8949315863213829779168201 6711986897410372334376151)
        ·
          refine ⟨10067980346115558501564227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711986897410372334376151 10067980346115558501564227)
          ·
            refine ⟨15101970519173337752346341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067980346115558501564227 15101970519173337752346341)
            ·
              refine ⟨2831619472345000828564939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15101970519173337752346341 2831619472345000828564939)
              ·
                refine ⟨4247429208517501242847409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831619472345000828564939 4247429208517501242847409)
                ·
                  refine ⟨3185571906388125932135557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4247429208517501242847409 3185571906388125932135557)
                  ·
                    refine ⟨597294732447773612275417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3185571906388125932135557 597294732447773612275417)
                    ·
                      rfl

theorem cell23_3489682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3489682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489682 prefixEnd_3489682 := by exact prefixLift 3489682
  have htrace : WordTrace (prefixWord ++ tailWord_3489682) baseStart_3489682 baseEnd_3489682 := by
    simpa [prefixWord, tailWord_3489682, baseEnd_3489682] using wordTrace_append hprefix tailTrace_3489682
  have hstable : (prefixWord ++ tailWord_3489682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489682).length < 2 ^ (prefixWord ++ tailWord_3489682).sum := by decide
  have hdescent : baseEnd_3489682 < baseStart_3489682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489686 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3489686 : Nat := 118140960795 + 3489686 * 2 ^ 59
def prefixEnd_3489686 : Nat := 4983230072969 + 3 ^ 40 * 3489686 * 2
def baseEnd_3489686 : Nat := 597295417088646273725411

theorem tailTrace_3489686 : CollatzResearch.WordTrace tailWord_3489686 prefixEnd_3489686 597295417088646273725411 := by
  unfold tailWord_3489686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954956552216942985290557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84852869890314058509765941 7954956552216942985290557)
  ·
    refine ⟨2983108707081353619483959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7954956552216942985290557 2983108707081353619483959)
    ·
      refine ⟨4474663060622030429225939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983108707081353619483959 4474663060622030429225939)
      ·
        refine ⟨6711994590933045643838909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474663060622030429225939 6711994590933045643838909)
        ·
          refine ⟨2516997971599892116439591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6711994590933045643838909 2516997971599892116439591)
          ·
            refine ⟨3775496957399838174659387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516997971599892116439591 3775496957399838174659387)
            ·
              refine ⟨5663245436099757261989081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775496957399838174659387 5663245436099757261989081)
              ·
                refine ⟨4247434077074817946491811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663245436099757261989081 4247434077074817946491811)
                ·
                  refine ⟨6371151115612226919737717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247434077074817946491811 6371151115612226919737717)
                  ·
                    refine ⟨597295417088646273725411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6371151115612226919737717 597295417088646273725411)
                    ·
                      rfl

theorem cell23_3489686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3489686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489686 prefixEnd_3489686 := by exact prefixLift 3489686
  have htrace : WordTrace (prefixWord ++ tailWord_3489686) baseStart_3489686 baseEnd_3489686 := by
    simpa [prefixWord, tailWord_3489686, baseEnd_3489686] using wordTrace_append hprefix tailTrace_3489686
  have hstable : (prefixWord ++ tailWord_3489686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489686).length < 2 ^ (prefixWord ++ tailWord_3489686).sum := by decide
  have hdescent : baseEnd_3489686 < baseStart_3489686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489692 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3489692 : Nat := 118140960795 + 3489692 * 2 ^ 59
def prefixEnd_3489692 : Nat := 4983230072969 + 3 ^ 40 * 3489692 * 2
def baseEnd_3489692 : Nat := 1791889332149865797701205

theorem tailTrace_3489692 : CollatzResearch.WordTrace tailWord_3489692 prefixEnd_3489692 1791889332149865797701205 := by
  unfold tailWord_3489692
  simp only [CollatzResearch.WordTrace]
  refine ⟨63639761836724675394683665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84853015782299567192911553 63639761836724675394683665)
  ·
    refine ⟨47729821377543506546012749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63639761836724675394683665 47729821377543506546012749)
    ·
      refine ⟨17898683016578814954754781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47729821377543506546012749 17898683016578814954754781)
      ·
        refine ⟨6712006131217055608033043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17898683016578814954754781 6712006131217055608033043)
        ·
          refine ⟨10068009196825583412049565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712006131217055608033043 10068009196825583412049565)
          ·
            refine ⟨3775503448809593779518587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10068009196825583412049565 3775503448809593779518587)
            ·
              refine ⟨5663255173214390669277881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775503448809593779518587 5663255173214390669277881)
              ·
                refine ⟨4247441379910793001958411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663255173214390669277881 4247441379910793001958411)
                ·
                  refine ⟨6371162069866189502937617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247441379910793001958411 6371162069866189502937617)
                  ·
                    refine ⟨4778371552399642127203213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6371162069866189502937617 4778371552399642127203213)
                    ·
                      refine ⟨1791889332149865797701205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4778371552399642127203213 1791889332149865797701205)
                      ·
                        rfl

theorem cell23_3489692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3489692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489692 prefixEnd_3489692 := by exact prefixLift 3489692
  have htrace : WordTrace (prefixWord ++ tailWord_3489692) baseStart_3489692 baseEnd_3489692 := by
    simpa [prefixWord, tailWord_3489692, baseEnd_3489692] using wordTrace_append hprefix tailTrace_3489692
  have hstable : (prefixWord ++ tailWord_3489692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489692).length < 2 ^ (prefixWord ++ tailWord_3489692).sum := by decide
  have hdescent : baseEnd_3489692 < baseStart_3489692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489721 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_3489721 : Nat := 118140960795 + 3489721 * 2 ^ 59
def prefixEnd_3489721 : Nat := 4983230072969 + 3 ^ 40 * 3489721 * 2
def baseEnd_3489721 : Nat := 597301407696282061412857

theorem tailTrace_3489721 : CollatzResearch.WordTrace tailWord_3489721 prefixEnd_3489721 597301407696282061412857 := by
  unfold tailWord_3489721
  simp only [CollatzResearch.WordTrace]
  refine ⟨127280581390344288742173017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84853720926896192494782011 127280581390344288742173017)
  ·
    refine ⟨95460436042758216556629763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127280581390344288742173017 95460436042758216556629763)
    ·
      refine ⟨143190654064137324834944645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95460436042758216556629763 143190654064137324834944645)
      ·
        refine ⟨26848247637025748406552121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143190654064137324834944645 26848247637025748406552121)
        ·
          refine ⟨20136185727769311304914091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26848247637025748406552121 20136185727769311304914091)
          ·
            refine ⟨30204278591653966957371137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20136185727769311304914091 30204278591653966957371137)
            ·
              refine ⟨22653208943740475218028353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30204278591653966957371137 22653208943740475218028353)
              ·
                refine ⟨16989906707805356413521265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22653208943740475218028353 16989906707805356413521265)
                ·
                  refine ⟨12742430030854017310140949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16989906707805356413521265 12742430030854017310140949)
                  ·
                    refine ⟨597301407696282061412857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12742430030854017310140949 597301407696282061412857)
                    ·
                      rfl

theorem cell23_3489721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_3489721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489721 prefixEnd_3489721 := by exact prefixLift 3489721
  have htrace : WordTrace (prefixWord ++ tailWord_3489721) baseStart_3489721 baseEnd_3489721 := by
    simpa [prefixWord, tailWord_3489721, baseEnd_3489721] using wordTrace_append hprefix tailTrace_3489721
  have hstable : (prefixWord ++ tailWord_3489721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489721).length < 2 ^ (prefixWord ++ tailWord_3489721).sum := by decide
  have hdescent : baseEnd_3489721 < baseStart_3489721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489728 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 3, 4, 2]
def baseStart_3489728 : Nat := 118140960795 + 3489728 * 2 ^ 59
def prefixEnd_3489728 : Nat := 4983230072969 + 3 ^ 40 * 3489728 * 2
def baseEnd_3489728 : Nat := 1791907817453427656851039

theorem tailTrace_3489728 : CollatzResearch.WordTrace tailWord_3489728 prefixEnd_3489728 1791907817453427656851039 := by
  unfold tailWord_3489728
  simp only [CollatzResearch.WordTrace]
  refine ⟨63640418350659464468838919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84853891134212619291785225 63640418350659464468838919)
  ·
    refine ⟨95460627525989196703258379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63640418350659464468838919 95460627525989196703258379)
    ·
      refine ⟨143190941288983795054887569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95460627525989196703258379 143190941288983795054887569)
      ·
        refine ⟨107393205966737846291165677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143190941288983795054887569 107393205966737846291165677)
        ·
          refine ⟨40272452237526692359187129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107393205966737846291165677 40272452237526692359187129)
          ·
            refine ⟨30204339178145019269390347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40272452237526692359187129 30204339178145019269390347)
            ·
              refine ⟨45306508767217528904085521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30204339178145019269390347 45306508767217528904085521)
              ·
                refine ⟨33979881575413146678064141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45306508767217528904085521 33979881575413146678064141)
                ·
                  refine ⟨12742455590779930004274053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33979881575413146678064141 12742455590779930004274053)
                  ·
                    refine ⟨2389210423271236875801385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12742455590779930004274053 2389210423271236875801385)
                    ·
                      refine ⟨1791907817453427656851039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389210423271236875801385 1791907817453427656851039)
                      ·
                        rfl

theorem cell23_3489728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_3489728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489728 prefixEnd_3489728 := by exact prefixLift 3489728
  have htrace : WordTrace (prefixWord ++ tailWord_3489728) baseStart_3489728 baseEnd_3489728 := by
    simpa [prefixWord, tailWord_3489728, baseEnd_3489728] using wordTrace_append hprefix tailTrace_3489728
  have hstable : (prefixWord ++ tailWord_3489728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489728).length < 2 ^ (prefixWord ++ tailWord_3489728).sum := by decide
  have hdescent : baseEnd_3489728 < baseStart_3489728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489748 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3489748 : Nat := 118140960795 + 3489748 * 2 ^ 59
def prefixEnd_3489748 : Nat := 4983230072969 + 3 ^ 40 * 3489748 * 2
def baseEnd_3489748 : Nat := 1791918087066517578600947

theorem tailTrace_3489748 : CollatzResearch.WordTrace tailWord_3489748 prefixEnd_3489748 1791918087066517578600947 := by
  unfold tailWord_3489748
  simp only [CollatzResearch.WordTrace]
  refine ⟨63640783080623236176702949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84854377440830981568937265 63640783080623236176702949)
  ·
    refine ⟨11932646827616856783131803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63640783080623236176702949 11932646827616856783131803)
    ·
      refine ⟨17898970241425285174697705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11932646827616856783131803 17898970241425285174697705)
      ·
        refine ⟨13424227681068963881023279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17898970241425285174697705 13424227681068963881023279)
        ·
          refine ⟨20136341521603445821534919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13424227681068963881023279 20136341521603445821534919)
          ·
            refine ⟨30204512282405168732302379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20136341521603445821534919 30204512282405168732302379)
            ·
              refine ⟨45306768423607753098453569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30204512282405168732302379 45306768423607753098453569)
              ·
                refine ⟨33980076317705814823840177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45306768423607753098453569 33980076317705814823840177)
                ·
                  refine ⟨25485057238279361117880133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33980076317705814823840177 25485057238279361117880133)
                  ·
                    refine ⟨4778448232177380209602525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25485057238279361117880133 4778448232177380209602525)
                    ·
                      refine ⟨1791918087066517578600947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4778448232177380209602525 1791918087066517578600947)
                      ·
                        rfl

theorem cell23_3489748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3489748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489748 prefixEnd_3489748 := by exact prefixLift 3489748
  have htrace : WordTrace (prefixWord ++ tailWord_3489748) baseStart_3489748 baseEnd_3489748 := by
    simpa [prefixWord, tailWord_3489748, baseEnd_3489748] using wordTrace_append hprefix tailTrace_3489748
  have hstable : (prefixWord ++ tailWord_3489748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489748).length < 2 ^ (prefixWord ++ tailWord_3489748).sum := by decide
  have hdescent : baseEnd_3489748 < baseStart_3489748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489751 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 7]
def baseStart_3489751 : Nat := 118140960795 + 3489751 * 2 ^ 59
def prefixEnd_3489751 : Nat := 4983230072969 + 3 ^ 40 * 3489751 * 2
def baseEnd_3489751 : Nat := 199102180834275674095937

theorem tailTrace_3489751 : CollatzResearch.WordTrace tailWord_3489751 prefixEnd_3489751 199102180834275674095937 := by
  unfold tailWord_3489751
  simp only [CollatzResearch.WordTrace]
  refine ⟨127281675580235603865765107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84854450386823735910510071 127281675580235603865765107)
  ·
    refine ⟨190922513370353405798647661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127281675580235603865765107 190922513370353405798647661)
    ·
      refine ⟨71595942513882527174492873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190922513370353405798647661 71595942513882527174492873)
      ·
        refine ⟨53696956885411895380869655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71595942513882527174492873 53696956885411895380869655)
        ·
          refine ⟨80545435328117843071304483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53696956885411895380869655 80545435328117843071304483)
          ·
            refine ⟨120818152992176764606956725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80545435328117843071304483 120818152992176764606956725)
            ·
              refine ⟨11326701843016571681902193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120818152992176764606956725 11326701843016571681902193)
              ·
                refine ⟨8495026382262428761426645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11326701843016571681902193 8495026382262428761426645)
                ·
                  refine ⟨199102180834275674095937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8495026382262428761426645 199102180834275674095937)
                  ·
                    rfl

theorem cell23_3489751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 7].length) (baseStart_3489751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489751 prefixEnd_3489751 := by exact prefixLift 3489751
  have htrace : WordTrace (prefixWord ++ tailWord_3489751) baseStart_3489751 baseEnd_3489751 := by
    simpa [prefixWord, tailWord_3489751, baseEnd_3489751] using wordTrace_append hprefix tailTrace_3489751
  have hstable : (prefixWord ++ tailWord_3489751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489751).length < 2 ^ (prefixWord ++ tailWord_3489751).sum := by decide
  have hdescent : baseEnd_3489751 < baseStart_3489751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489791 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_3489791 : Nat := 118140960795 + 3489791 * 2 ^ 59
def prefixEnd_3489791 : Nat := 4983230072969 + 3 ^ 40 * 3489791 * 2
def baseEnd_3489791 : Nat := 1791940166734660910363249

theorem tailTrace_3489791 : CollatzResearch.WordTrace tailWord_3489791 prefixEnd_3489791 1791940166734660910363249 := by
  unfold tailWord_3489791
  simp only [CollatzResearch.WordTrace]
  refine ⟨127283134500090690697221227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84855423000060460464814151 127283134500090690697221227)
  ·
    refine ⟨190924701750136036045831841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127283134500090690697221227 190924701750136036045831841)
    ·
      refine ⟨143193526312602027034373881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190924701750136036045831841 143193526312602027034373881)
      ·
        refine ⟨107395144734451520275780411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143193526312602027034373881 107395144734451520275780411)
        ·
          refine ⟨161092717101677280413670617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107395144734451520275780411 161092717101677280413670617)
          ·
            refine ⟨120819537826257960310252963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161092717101677280413670617 120819537826257960310252963)
            ·
              refine ⟨181229306739386940465379445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120819537826257960310252963 181229306739386940465379445)
              ·
                refine ⟨16990247506817525668629323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181229306739386940465379445 16990247506817525668629323)
                ·
                  refine ⟨25485371260226288502943985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16990247506817525668629323 25485371260226288502943985)
                  ·
                    refine ⟨19114028445169716377207989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25485371260226288502943985 19114028445169716377207989)
                    ·
                      refine ⟨1791940166734660910363249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19114028445169716377207989 1791940166734660910363249)
                      ·
                        rfl

theorem cell23_3489791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_3489791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489791 prefixEnd_3489791 := by exact prefixLift 3489791
  have htrace : WordTrace (prefixWord ++ tailWord_3489791) baseStart_3489791 baseEnd_3489791 := by
    simpa [prefixWord, tailWord_3489791, baseEnd_3489791] using wordTrace_append hprefix tailTrace_3489791
  have hstable : (prefixWord ++ tailWord_3489791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489791).length < 2 ^ (prefixWord ++ tailWord_3489791).sum := by decide
  have hdescent : baseEnd_3489791 < baseStart_3489791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489796 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3489796 : Nat := 118140960795 + 3489796 * 2 ^ 59
def prefixEnd_3489796 : Nat := 4983230072969 + 3 ^ 40 * 3489796 * 2
def baseEnd_3489796 : Nat := 1791942734137933390800727

theorem tailTrace_3489796 : CollatzResearch.WordTrace tailWord_3489796 prefixEnd_3489796 1791942734137933390800727 := by
  unfold tailWord_3489796
  simp only [CollatzResearch.WordTrace]
  refine ⟨63641658432536288275576621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84855544576715051034102161 63641658432536288275576621)
  ·
    refine ⟨23865621912201108103341233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63641658432536288275576621 23865621912201108103341233)
    ·
      refine ⟨17899216434150831077505925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23865621912201108103341233 17899216434150831077505925)
      ·
        refine ⟨3356103081403280827032361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17899216434150831077505925 3356103081403280827032361)
        ·
          refine ⟨2517077311052460620274271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356103081403280827032361 2517077311052460620274271)
          ·
            refine ⟨3775615966578690930411407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517077311052460620274271 3775615966578690930411407)
            ·
              refine ⟨5663423949868036395617111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775615966578690930411407 5663423949868036395617111)
              ·
                refine ⟨8495135924802054593425667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663423949868036395617111 8495135924802054593425667)
                ·
                  refine ⟨12742703887203081890138501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8495135924802054593425667 12742703887203081890138501)
                  ·
                    refine ⟨2389256978850577854400969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12742703887203081890138501 2389256978850577854400969)
                    ·
                      refine ⟨1791942734137933390800727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389256978850577854400969 1791942734137933390800727)
                      ·
                        rfl

theorem cell23_3489796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3489796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489796 prefixEnd_3489796 := by exact prefixLift 3489796
  have htrace : WordTrace (prefixWord ++ tailWord_3489796) baseStart_3489796 baseEnd_3489796 := by
    simpa [prefixWord, tailWord_3489796, baseEnd_3489796] using wordTrace_append hprefix tailTrace_3489796
  have hstable : (prefixWord ++ tailWord_3489796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489796).length < 2 ^ (prefixWord ++ tailWord_3489796).sum := by decide
  have hdescent : baseEnd_3489796 < baseStart_3489796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489818 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3489818 : Nat := 118140960795 + 3489818 * 2 ^ 59
def prefixEnd_3489818 : Nat := 4983230072969 + 3 ^ 40 * 3489818 * 2
def baseEnd_3489818 : Nat := 1791954030712332304725625

theorem tailTrace_3489818 : CollatzResearch.WordTrace tailWord_3489818 prefixEnd_3489818 1791954030712332304725625 := by
  unfold tailWord_3489818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31821029817748218577113527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84856079513995249538969405 31821029817748218577113527)
  ·
    refine ⟨47731544726622327865670291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31821029817748218577113527 47731544726622327865670291)
    ·
      refine ⟨71597317089933491798505437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47731544726622327865670291 71597317089933491798505437)
      ·
        refine ⟨26848993908725059424439539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71597317089933491798505437 26848993908725059424439539)
        ·
          refine ⟨40273490863087589136659309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26848993908725059424439539 40273490863087589136659309)
          ·
            refine ⟨15102559073657845926247241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40273490863087589136659309 15102559073657845926247241)
            ·
              refine ⟨11326919305243384444685431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15102559073657845926247241 11326919305243384444685431)
              ·
                refine ⟨16990378957865076667028147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11326919305243384444685431 16990378957865076667028147)
                ·
                  refine ⟨25485568436797615000542221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16990378957865076667028147 25485568436797615000542221)
                  ·
                    refine ⟨9557088163799105625203333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25485568436797615000542221 9557088163799105625203333)
                    ·
                      refine ⟨1791954030712332304725625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9557088163799105625203333 1791954030712332304725625)
                      ·
                        rfl

theorem cell23_3489818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3489818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489818 prefixEnd_3489818 := by exact prefixLift 3489818
  have htrace : WordTrace (prefixWord ++ tailWord_3489818) baseStart_3489818 baseEnd_3489818 := by
    simpa [prefixWord, tailWord_3489818, baseEnd_3489818] using wordTrace_append hprefix tailTrace_3489818
  have hstable : (prefixWord ++ tailWord_3489818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489818).length < 2 ^ (prefixWord ++ tailWord_3489818).sum := by decide
  have hdescent : baseEnd_3489818 < baseStart_3489818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489832 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3489832 : Nat := 118140960795 + 3489832 * 2 ^ 59
def prefixEnd_3489832 : Nat := 4983230072969 + 3 ^ 40 * 3489832 * 2
def baseEnd_3489832 : Nat := 597320406480498416650187

theorem tailTrace_3489832 : CollatzResearch.WordTrace tailWord_3489832 prefixEnd_3489832 597320406480498416650187 := by
  unfold tailWord_3489832
  simp only [CollatzResearch.WordTrace]
  refine ⟨63642314946471077349731875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84856419928628103132975833 63642314946471077349731875)
  ·
    refine ⟨95463472419706616024597813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63642314946471077349731875 95463472419706616024597813)
    ·
      refine ⟨8949700539347495252306045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95463472419706616024597813 8949700539347495252306045)
      ·
        refine ⟨3356137702255310719614767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8949700539347495252306045 3356137702255310719614767)
        ·
          refine ⟨5034206553382966079422151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356137702255310719614767 5034206553382966079422151)
          ·
            refine ⟨7551309830074449119133227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034206553382966079422151 7551309830074449119133227)
            ·
              refine ⟨11326964745111673678699841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551309830074449119133227 11326964745111673678699841)
              ·
                refine ⟨8495223558833755259024881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11326964745111673678699841 8495223558833755259024881)
                ·
                  refine ⟨6371417669125316444268661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8495223558833755259024881 6371417669125316444268661)
                  ·
                    refine ⟨597320406480498416650187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6371417669125316444268661 597320406480498416650187)
                    ·
                      rfl

theorem cell23_3489832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3489832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489832 prefixEnd_3489832 := by exact prefixLift 3489832
  have htrace : WordTrace (prefixWord ++ tailWord_3489832) baseStart_3489832 baseEnd_3489832 := by
    simpa [prefixWord, tailWord_3489832, baseEnd_3489832] using wordTrace_append hprefix tailTrace_3489832
  have hstable : (prefixWord ++ tailWord_3489832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489832).length < 2 ^ (prefixWord ++ tailWord_3489832).sum := by decide
  have hdescent : baseEnd_3489832 < baseStart_3489832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489845 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3489845 : Nat := 118140960795 + 3489845 * 2 ^ 59
def prefixEnd_3489845 : Nat := 4983230072969 + 3 ^ 40 * 3489845 * 2
def baseEnd_3489845 : Nat := 597322631563334566362667

theorem tailTrace_3489845 : CollatzResearch.WordTrace tailWord_3489845 prefixEnd_3489845 597322631563334566362667 := by
  unfold tailWord_3489845
  simp only [CollatzResearch.WordTrace]
  refine ⟨127285104041895057919686989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84856736027930038613124659 127285104041895057919686989)
  ·
    refine ⟨47731914015710646719882621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127285104041895057919686989 47731914015710646719882621)
    ·
      refine ⟨17899467755891492519955983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47731914015710646719882621 17899467755891492519955983)
      ·
        refine ⟨26849201633837238779933975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17899467755891492519955983 26849201633837238779933975)
        ·
          refine ⟨40273802450755858169900963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26849201633837238779933975 40273802450755858169900963)
          ·
            refine ⟨60410703676133787254851445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40273802450755858169900963 60410703676133787254851445)
            ·
              refine ⟨5663503469637542555142323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60410703676133787254851445 5663503469637542555142323)
              ·
                refine ⟨8495255204456313832713485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663503469637542555142323 8495255204456313832713485)
                ·
                  refine ⟨3185720701671117687267557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8495255204456313832713485 3185720701671117687267557)
                  ·
                    refine ⟨597322631563334566362667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3185720701671117687267557 597322631563334566362667)
                    ·
                      rfl

theorem cell23_3489845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3489845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489845 prefixEnd_3489845 := by exact prefixLift 3489845
  have htrace : WordTrace (prefixWord ++ tailWord_3489845) baseStart_3489845 baseEnd_3489845 := by
    simpa [prefixWord, tailWord_3489845, baseEnd_3489845] using wordTrace_append hprefix tailTrace_3489845
  have hstable : (prefixWord ++ tailWord_3489845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489845).length < 2 ^ (prefixWord ++ tailWord_3489845).sum := by decide
  have hdescent : baseEnd_3489845 < baseStart_3489845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489862 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3489862 : Nat := 118140960795 + 3489862 * 2 ^ 59
def prefixEnd_3489862 : Nat := 4983230072969 + 3 ^ 40 * 3489862 * 2
def baseEnd_3489862 : Nat := 597325541287043377525141

theorem tailTrace_3489862 : CollatzResearch.WordTrace tailWord_3489862 prefixEnd_3489862 597325541287043377525141 := by
  unfold tailWord_3489862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977678877588545931970495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84857149388555646548703893 3977678877588545931970495)
  ·
    refine ⟨5966518316382818897955743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977678877588545931970495 5966518316382818897955743)
    ·
      refine ⟨8949777474574228346933615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5966518316382818897955743 8949777474574228346933615)
      ·
        refine ⟨13424666211861342520400423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949777474574228346933615 13424666211861342520400423)
        ·
          refine ⟨20136999317792013780600635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13424666211861342520400423 20136999317792013780600635)
          ·
            refine ⟨30205498976688020670900953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20136999317792013780600635 30205498976688020670900953)
            ·
              refine ⟨22654124232516015503175715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30205498976688020670900953 22654124232516015503175715)
              ·
                refine ⟨33981186348774023254763573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22654124232516015503175715 33981186348774023254763573)
                ·
                  refine ⟨3185736220197564680134085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33981186348774023254763573 3185736220197564680134085)
                  ·
                    refine ⟨597325541287043377525141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3185736220197564680134085 597325541287043377525141)
                    ·
                      rfl

theorem cell23_3489862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3489862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489862 prefixEnd_3489862 := by exact prefixLift 3489862
  have htrace : WordTrace (prefixWord ++ tailWord_3489862) baseStart_3489862 baseEnd_3489862 := by
    simpa [prefixWord, tailWord_3489862, baseEnd_3489862] using wordTrace_append hprefix tailTrace_3489862
  have hstable : (prefixWord ++ tailWord_3489862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489862).length < 2 ^ (prefixWord ++ tailWord_3489862).sum := by decide
  have hdescent : baseEnd_3489862 < baseStart_3489862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489868 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3489868 : Nat := 118140960795 + 3489868 * 2 ^ 59
def prefixEnd_3489868 : Nat := 4983230072969 + 3 ^ 40 * 3489868 * 2
def baseEnd_3489868 : Nat := 1791979704745057109100395

theorem tailTrace_3489868 : CollatzResearch.WordTrace tailWord_3489868 prefixEnd_3489868 1791979704745057109100395 := by
  unfold tailWord_3489868
  simp only [CollatzResearch.WordTrace]
  refine ⟨63642971460405866423887129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84857295280541155231849505 63642971460405866423887129)
  ·
    refine ⟨47732228595304399817915347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63642971460405866423887129 47732228595304399817915347)
    ·
      refine ⟨71598342892956599726873021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47732228595304399817915347 71598342892956599726873021)
      ·
        refine ⟨26849378584858724897577383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71598342892956599726873021 26849378584858724897577383)
        ·
          refine ⟨40274067877288087346366075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26849378584858724897577383 40274067877288087346366075)
          ·
            refine ⟨60411101815932131019549113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40274067877288087346366075 60411101815932131019549113)
            ·
              refine ⟨45308326361949098264661835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60411101815932131019549113 45308326361949098264661835)
              ·
                refine ⟨67962489542923647396992753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45308326361949098264661835 67962489542923647396992753)
                ·
                  refine ⟨50971867157192735547744565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67962489542923647396992753 50971867157192735547744565)
                  ·
                    refine ⟨4778612545986818957601053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50971867157192735547744565 4778612545986818957601053)
                    ·
                      refine ⟨1791979704745057109100395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4778612545986818957601053 1791979704745057109100395)
                      ·
                        rfl

theorem cell23_3489868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3489868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489868 prefixEnd_3489868 := by exact prefixLift 3489868
  have htrace : WordTrace (prefixWord ++ tailWord_3489868) baseStart_3489868 baseEnd_3489868 := by
    simpa [prefixWord, tailWord_3489868, baseEnd_3489868] using wordTrace_append hprefix tailTrace_3489868
  have hstable : (prefixWord ++ tailWord_3489868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489868).length < 2 ^ (prefixWord ++ tailWord_3489868).sum := by decide
  have hdescent : baseEnd_3489868 < baseStart_3489868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489871 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 9]
def baseStart_3489871 : Nat := 118140960795 + 3489871 * 2 ^ 59
def prefixEnd_3489871 : Nat := 4983230072969 + 3 ^ 40 * 3489871 * 2
def baseEnd_3489871 : Nat := 597327081729006865787627

theorem tailTrace_3489871 : CollatzResearch.WordTrace tailWord_3489871 prefixEnd_3489871 597327081729006865787627 := by
  unfold tailWord_3489871
  simp only [CollatzResearch.WordTrace]
  refine ⟨127286052339800864360133467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84857368226533909573422311 127286052339800864360133467)
  ·
    refine ⟨190929078509701296540200201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127286052339800864360133467 190929078509701296540200201)
    ·
      refine ⟨143196808882275972405150151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190929078509701296540200201 143196808882275972405150151)
      ·
        refine ⟨214795213323413958607725227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143196808882275972405150151 214795213323413958607725227)
        ·
          refine ⟨322192819985120937911587841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214795213323413958607725227 322192819985120937911587841)
          ·
            refine ⟨241644614988840703433690881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322192819985120937911587841 241644614988840703433690881)
            ·
              refine ⟨181233461241630527575268161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241644614988840703433690881 181233461241630527575268161)
              ·
                refine ⟨135925095931222895681451121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181233461241630527575268161 135925095931222895681451121)
                ·
                  refine ⟨101943821948417171761088341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135925095931222895681451121 101943821948417171761088341)
                  ·
                    refine ⟨597327081729006865787627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 101943821948417171761088341 597327081729006865787627)
                    ·
                      rfl

theorem cell23_3489871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_3489871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489871 prefixEnd_3489871 := by exact prefixLift 3489871
  have htrace : WordTrace (prefixWord ++ tailWord_3489871) baseStart_3489871 baseEnd_3489871 := by
    simpa [prefixWord, tailWord_3489871, baseEnd_3489871] using wordTrace_append hprefix tailTrace_3489871
  have hstable : (prefixWord ++ tailWord_3489871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489871).length < 2 ^ (prefixWord ++ tailWord_3489871).sum := by decide
  have hdescent : baseEnd_3489871 < baseStart_3489871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489902 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3489902 : Nat := 118140960795 + 3489902 * 2 ^ 59
def prefixEnd_3489902 : Nat := 4983230072969 + 3 ^ 40 * 3489902 * 2
def baseEnd_3489902 : Nat := 1791997163087309976075239

theorem tailTrace_3489902 : CollatzResearch.WordTrace tailWord_3489902 prefixEnd_3489902 1791997163087309976075239 := by
  unfold tailWord_3489902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15910897875336069581813995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84858122001792371103007973 15910897875336069581813995)
  ·
    refine ⟨23866346813004104372720993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15910897875336069581813995 23866346813004104372720993)
    ·
      refine ⟨17899760109753078279540745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23866346813004104372720993 17899760109753078279540745)
      ·
        refine ⟨13424820082314808709655559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17899760109753078279540745 13424820082314808709655559)
        ·
          refine ⟨20137230123472213064483339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13424820082314808709655559 20137230123472213064483339)
          ·
            refine ⟨30205845185208319596725009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20137230123472213064483339 30205845185208319596725009)
            ·
              refine ⟨22654383888906239697543757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30205845185208319596725009 22654383888906239697543757)
              ·
                refine ⟨8495393958339839886578909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22654383888906239697543757 8495393958339839886578909)
                ·
                  refine ⟨3185772734377439957467091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8495393958339839886578909 3185772734377439957467091)
                  ·
                    refine ⟨4778659101566159936200637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3185772734377439957467091 4778659101566159936200637)
                    ·
                      refine ⟨1791997163087309976075239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4778659101566159936200637 1791997163087309976075239)
                      ·
                        rfl

theorem cell23_3489902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3489902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489902 prefixEnd_3489902 := by exact prefixLift 3489902
  have htrace : WordTrace (prefixWord ++ tailWord_3489902) baseStart_3489902 baseEnd_3489902 := by
    simpa [prefixWord, tailWord_3489902, baseEnd_3489902] using wordTrace_append hprefix tailTrace_3489902
  have hstable : (prefixWord ++ tailWord_3489902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489902).length < 2 ^ (prefixWord ++ tailWord_3489902).sum := by decide
  have hdescent : baseEnd_3489902 < baseStart_3489902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489925 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_3489925 : Nat := 118140960795 + 3489925 * 2 ^ 59
def prefixEnd_3489925 : Nat := 4983230072969 + 3 ^ 40 * 3489925 * 2
def baseEnd_3489925 : Nat := 1792008973142363386087633

theorem tailTrace_3489925 : CollatzResearch.WordTrace tailWord_3489925 prefixEnd_3489925 1792008973142363386087633 := by
  unfold tailWord_3489925
  simp only [CollatzResearch.WordTrace]
  refine ⟨127288021881605231582599229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84858681254403487721732819 127288021881605231582599229)
  ·
    refine ⟨47733008205601961843474711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127288021881605231582599229 47733008205601961843474711)
    ·
      refine ⟨71599512308402942765212067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47733008205601961843474711 71599512308402942765212067)
      ·
        refine ⟨107399268462604414147818101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71599512308402942765212067 107399268462604414147818101)
        ·
          refine ⟨10068681418369163826357947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107399268462604414147818101 10068681418369163826357947)
          ·
            refine ⟨15103022127553745739536921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068681418369163826357947 15103022127553745739536921)
            ·
              refine ⟨11327266595665309304652691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15103022127553745739536921 11327266595665309304652691)
              ·
                refine ⟨16990899893497963956979037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11327266595665309304652691 16990899893497963956979037)
                ·
                  refine ⟨6371587460061736483867139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16990899893497963956979037 6371587460061736483867139)
                  ·
                    refine ⟨9557381190092604725800709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6371587460061736483867139 9557381190092604725800709)
                    ·
                      refine ⟨1792008973142363386087633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9557381190092604725800709 1792008973142363386087633)
                      ·
                        rfl

theorem cell23_3489925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_3489925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489925 prefixEnd_3489925 := by exact prefixLift 3489925
  have htrace : WordTrace (prefixWord ++ tailWord_3489925) baseStart_3489925 baseEnd_3489925 := by
    simpa [prefixWord, tailWord_3489925, baseEnd_3489925] using wordTrace_append hprefix tailTrace_3489925
  have hstable : (prefixWord ++ tailWord_3489925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489925).length < 2 ^ (prefixWord ++ tailWord_3489925).sum := by decide
  have hdescent : baseEnd_3489925 < baseStart_3489925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489948 : List Nat := [2, 2, 3, 2, 1, 1, 12]
def baseStart_3489948 : Nat := 118140960795 + 3489948 * 2 ^ 59
def prefixEnd_3489948 : Nat := 4983230072969 + 3 ^ 40 * 3489948 * 2
def baseEnd_3489948 : Nat := 22123713372807614766667

theorem tailTrace_3489948 : CollatzResearch.WordTrace tailWord_3489948 prefixEnd_3489948 22123713372807614766667 := by
  unfold tailWord_3489948
  simp only [CollatzResearch.WordTrace]
  refine ⟨63644430380260953255343249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84859240507014604340457665 63644430380260953255343249)
  ·
    refine ⟨47733322785195714941507437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63644430380260953255343249 47733322785195714941507437)
    ·
      refine ⟨17899996044448393103065289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47733322785195714941507437 17899996044448393103065289)
      ·
        refine ⟨13424997033336294827298967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17899996044448393103065289 13424997033336294827298967)
        ·
          refine ⟨20137495550004442240948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13424997033336294827298967 20137495550004442240948451)
          ·
            refine ⟨30206243325006663361422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20137495550004442240948451 30206243325006663361422677)
            ·
              refine ⟨22123713372807614766667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30206243325006663361422677 22123713372807614766667)
              ·
                rfl

theorem cell23_3489948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 12].length) (baseStart_3489948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489948 prefixEnd_3489948 := by exact prefixLift 3489948
  have htrace : WordTrace (prefixWord ++ tailWord_3489948) baseStart_3489948 baseEnd_3489948 := by
    simpa [prefixWord, tailWord_3489948, baseEnd_3489948] using wordTrace_append hprefix tailTrace_3489948
  have hstable : (prefixWord ++ tailWord_3489948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489948).length < 2 ^ (prefixWord ++ tailWord_3489948).sum := by decide
  have hdescent : baseEnd_3489948 < baseStart_3489948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489952 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 2, 4]
def baseStart_3489952 : Nat := 118140960795 + 3489952 * 2 ^ 59
def prefixEnd_3489952 : Nat := 4983230072969 + 3 ^ 40 * 3489952 * 2
def baseEnd_3489952 : Nat := 597340945706678260150003

theorem tailTrace_3489952 : CollatzResearch.WordTrace tailWord_3489952 prefixEnd_3489952 597340945706678260150003 := by
  unfold tailWord_3489952
  simp only [CollatzResearch.WordTrace]
  refine ⟨63644503326253707596916055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84859337768338276795888073 63644503326253707596916055)
  ·
    refine ⟨95466754989380561395374083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63644503326253707596916055 95466754989380561395374083)
    ·
      refine ⟨143200132484070842093061125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95466754989380561395374083 143200132484070842093061125)
      ·
        refine ⟨26850024840763282892448961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143200132484070842093061125 26850024840763282892448961)
        ·
          refine ⟨20137518630572462169336721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26850024840763282892448961 20137518630572462169336721)
          ·
            refine ⟨15103138972929346627002541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20137518630572462169336721 15103138972929346627002541)
            ·
              refine ⟨5663677114848504985125953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15103138972929346627002541 5663677114848504985125953)
              ·
                refine ⟨4247757836136378738844465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663677114848504985125953 4247757836136378738844465)
                ·
                  refine ⟨3185818377102284054133349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4247757836136378738844465 3185818377102284054133349)
                  ·
                    refine ⟨597340945706678260150003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3185818377102284054133349 597340945706678260150003)
                    ·
                      rfl

theorem cell23_3489952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_3489952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489952 prefixEnd_3489952 := by exact prefixLift 3489952
  have htrace : WordTrace (prefixWord ++ tailWord_3489952) baseStart_3489952 baseEnd_3489952 := by
    simpa [prefixWord, tailWord_3489952, baseEnd_3489952] using wordTrace_append hprefix tailTrace_3489952
  have hstable : (prefixWord ++ tailWord_3489952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489952).length < 2 ^ (prefixWord ++ tailWord_3489952).sum := by decide
  have hdescent : baseEnd_3489952 < baseStart_3489952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489969 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 1, 6]
def baseStart_3489969 : Nat := 118140960795 + 3489969 * 2 ^ 59
def prefixEnd_3489969 : Nat := 4983230072969 + 3 ^ 40 * 3489969 * 2
def baseEnd_3489969 : Nat := 597343855430387071312477

theorem tailTrace_3489969 : CollatzResearch.WordTrace tailWord_3489969 prefixEnd_3489969 597343855430387071312477 := by
  unfold tailWord_3489969
  simp only [CollatzResearch.WordTrace]
  refine ⟨127289626693445827097200961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84859751128963884731467307 127289626693445827097200961)
  ·
    refine ⟨95467220020084370322900721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127289626693445827097200961 95467220020084370322900721)
    ·
      refine ⟨71600415015063277742175541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95467220020084370322900721 71600415015063277742175541)
      ·
        refine ⟨6712538907662182288328957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71600415015063277742175541 6712538907662182288328957)
        ·
          refine ⟨2517202090373318358123359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6712538907662182288328957 2517202090373318358123359)
          ·
            refine ⟨3775803135559977537185039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517202090373318358123359 3775803135559977537185039)
            ·
              refine ⟨5663704703339966305777559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775803135559977537185039 5663704703339966305777559)
              ·
                refine ⟨8495557055009949458666339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663704703339966305777559 8495557055009949458666339)
                ·
                  refine ⟨12743335582514924187999509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8495557055009949458666339 12743335582514924187999509)
                  ·
                    refine ⟨597343855430387071312477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12743335582514924187999509 597343855430387071312477)
                    ·
                      rfl

theorem cell23_3489969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_3489969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489969 prefixEnd_3489969 := by exact prefixLift 3489969
  have htrace : WordTrace (prefixWord ++ tailWord_3489969) baseStart_3489969 baseEnd_3489969 := by
    simpa [prefixWord, tailWord_3489969, baseEnd_3489969] using wordTrace_append hprefix tailTrace_3489969
  have hstable : (prefixWord ++ tailWord_3489969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489969).length < 2 ^ (prefixWord ++ tailWord_3489969).sum := by decide
  have hdescent : baseEnd_3489969 < baseStart_3489969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3489978 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_3489978 : Nat := 118140960795 + 3489978 * 2 ^ 59
def prefixEnd_3489978 : Nat := 4983230072969 + 3 ^ 40 * 3489978 * 2
def baseEnd_3489978 : Nat := 597345395872350559574963

theorem tailTrace_3489978 : CollatzResearch.WordTrace tailWord_3489978 prefixEnd_3489978 597345395872350559574963 := by
  unfold tailWord_3489978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31822488737603305408569647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84859969966942147756185725 31822488737603305408569647)
  ·
    refine ⟨47733733106404958112854471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31822488737603305408569647 47733733106404958112854471)
    ·
      refine ⟨71600599659607437169281707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47733733106404958112854471 71600599659607437169281707)
      ·
        refine ⟨107400899489411155753922561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71600599659607437169281707 107400899489411155753922561)
        ·
          refine ⟨80550674617058366815441921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107400899489411155753922561 80550674617058366815441921)
          ·
            refine ⟨60413005962793775111581441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80550674617058366815441921 60413005962793775111581441)
            ·
              refine ⟨45309754472095331333686081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60413005962793775111581441 45309754472095331333686081)
              ·
                refine ⟨33982315854071498500264561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45309754472095331333686081 33982315854071498500264561)
                ·
                  refine ⟨25486736890553623875198421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33982315854071498500264561 25486736890553623875198421)
                  ·
                    refine ⟨597345395872350559574963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25486736890553623875198421 597345395872350559574963)
                    ·
                      rfl

theorem cell23_3489978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_3489978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3489978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3489978 prefixEnd_3489978 := by exact prefixLift 3489978
  have htrace : WordTrace (prefixWord ++ tailWord_3489978) baseStart_3489978 baseEnd_3489978 := by
    simpa [prefixWord, tailWord_3489978, baseEnd_3489978] using wordTrace_append hprefix tailTrace_3489978
  have hstable : (prefixWord ++ tailWord_3489978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3489978).length < 2 ^ (prefixWord ++ tailWord_3489978).sum := by decide
  have hdescent : baseEnd_3489978 < baseStart_3489978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3489978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490072 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 5]
def baseStart_3490072 : Nat := 118140960795 + 3490072 * 2 ^ 59
def prefixEnd_3490072 : Nat := 4983230072969 + 3 ^ 40 * 3490072 * 2
def baseEnd_3490072 : Nat := 199120494977619367883273

theorem tailTrace_3490072 : CollatzResearch.WordTrace tailWord_3490072 prefixEnd_3490072 199120494977619367883273 := by
  unfold tailWord_3490072
  simp only [CollatzResearch.WordTrace]
  refine ⟨63646691706036337844100235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84862255608048450458800313 63646691706036337844100235)
  ·
    refine ⟨95470037559054506766150353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63646691706036337844100235 95470037559054506766150353)
    ·
      refine ⟨71602528169290880074612765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95470037559054506766150353 71602528169290880074612765)
      ·
        refine ⟨26850948063484080027979787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71602528169290880074612765 26850948063484080027979787)
        ·
          refine ⟨40276422095226120041969681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26850948063484080027979787 40276422095226120041969681)
          ·
            refine ⟨30207316571419590031477261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40276422095226120041969681 30207316571419590031477261)
            ·
              refine ⟨11327743714282346261803973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30207316571419590031477261 11327743714282346261803973)
              ·
                refine ⟨2123951946427939924088245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11327743714282346261803973 2123951946427939924088245)
                ·
                  refine ⟨199120494977619367883273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2123951946427939924088245 199120494977619367883273)
                  ·
                    rfl

theorem cell23_3490072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 5].length) (baseStart_3490072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490072 prefixEnd_3490072 := by exact prefixLift 3490072
  have htrace : WordTrace (prefixWord ++ tailWord_3490072) baseStart_3490072 baseEnd_3490072 := by
    simpa [prefixWord, tailWord_3490072, baseEnd_3490072] using wordTrace_append hprefix tailTrace_3490072
  have hstable : (prefixWord ++ tailWord_3490072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490072).length < 2 ^ (prefixWord ++ tailWord_3490072).sum := by decide
  have hdescent : baseEnd_3490072 < baseStart_3490072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490082 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_3490082 : Nat := 118140960795 + 3490082 * 2 ^ 59
def prefixEnd_3490082 : Nat := 4983230072969 + 3 ^ 40 * 3490082 * 2
def baseEnd_3490082 : Nat := 1792089589605119271824411

theorem tailTrace_3490082 : CollatzResearch.WordTrace tailWord_3490082 prefixEnd_3490082 1792089589605119271824411 := by
  unfold tailWord_3490082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31823437035509111849016125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84862498761357631597376333 31823437035509111849016125)
  ·
    refine ⟨11933788888315916943381047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31823437035509111849016125 11933788888315916943381047)
    ·
      refine ⟨17900683332473875415071571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11933788888315916943381047 17900683332473875415071571)
      ·
        refine ⟨26851024998710813122607357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17900683332473875415071571 26851024998710813122607357)
        ·
          refine ⟨10069134374516554920977759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26851024998710813122607357 10069134374516554920977759)
          ·
            refine ⟨15103701561774832381466639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069134374516554920977759 15103701561774832381466639)
            ·
              refine ⟨22655552342662248572199959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15103701561774832381466639 22655552342662248572199959)
              ·
                refine ⟨33983328513993372858299939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22655552342662248572199959 33983328513993372858299939)
                ·
                  refine ⟨50974992770990059287449909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33983328513993372858299939 50974992770990059287449909)
                  ·
                    refine ⟨4778905572280318058198429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50974992770990059287449909 4778905572280318058198429)
                    ·
                      refine ⟨1792089589605119271824411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4778905572280318058198429 1792089589605119271824411)
                      ·
                        rfl

theorem cell23_3490082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_3490082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490082 prefixEnd_3490082 := by exact prefixLift 3490082
  have htrace : WordTrace (prefixWord ++ tailWord_3490082) baseStart_3490082 baseEnd_3490082 := by
    simpa [prefixWord, tailWord_3490082, baseEnd_3490082] using wordTrace_append hprefix tailTrace_3490082
  have hstable : (prefixWord ++ tailWord_3490082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490082).length < 2 ^ (prefixWord ++ tailWord_3490082).sum := by decide
  have hdescent : baseEnd_3490082 < baseStart_3490082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490135 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_3490135 : Nat := 118140960795 + 3490135 * 2 ^ 59
def prefixEnd_3490135 : Nat := 4983230072969 + 3 ^ 40 * 3490135 * 2
def baseEnd_3490135 : Nat := 1792116804079807564461667

theorem tailTrace_3490135 : CollatzResearch.WordTrace tailWord_3490135 prefixEnd_3490135 1792116804079807564461667 := by
  unfold tailWord_3490135
  simp only [CollatzResearch.WordTrace]
  refine ⟨127295681210844437447743859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84863787473896291631829239 127295681210844437447743859)
  ·
    refine ⟨190943521816266656171615789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127295681210844437447743859 190943521816266656171615789)
    ·
      refine ⟨71603820681099996064355921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190943521816266656171615789 71603820681099996064355921)
      ·
        refine ⟨53702865510824997048266941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71603820681099996064355921 53702865510824997048266941)
        ·
          refine ⟨20138574566559373893100103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53702865510824997048266941 20138574566559373893100103)
          ·
            refine ⟨30207861849839060839650155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20138574566559373893100103 30207861849839060839650155)
            ·
              refine ⟨45311792774758591259475233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30207861849839060839650155 45311792774758591259475233)
              ·
                refine ⟨33983844581068943444606425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45311792774758591259475233 33983844581068943444606425)
                ·
                  refine ⟨25487883435801707583454819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33983844581068943444606425 25487883435801707583454819)
                  ·
                    refine ⟨38231825153702561375182229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25487883435801707583454819 38231825153702561375182229)
                    ·
                      refine ⟨1792116804079807564461667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38231825153702561375182229 1792116804079807564461667)
                      ·
                        rfl

theorem cell23_3490135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_3490135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490135 prefixEnd_3490135 := by exact prefixLift 3490135
  have htrace : WordTrace (prefixWord ++ tailWord_3490135) baseStart_3490135 baseEnd_3490135 := by
    simpa [prefixWord, tailWord_3490135, baseEnd_3490135] using wordTrace_append hprefix tailTrace_3490135
  have hstable : (prefixWord ++ tailWord_3490135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490135).length < 2 ^ (prefixWord ++ tailWord_3490135).sum := by decide
  have hdescent : baseEnd_3490135 < baseStart_3490135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490269 : List Nat := [1, 4, 3, 1, 1, 1, 5, 7]
def baseStart_3490269 : Nat := 118140960795 + 3490269 * 2 ^ 59
def prefixEnd_3490269 : Nat := 4983230072969 + 3 ^ 40 * 3490269 * 2
def baseEnd_3490269 : Nat := 66377244832870742229113

theorem tailTrace_3490269 : CollatzResearch.WordTrace tailWord_3490269 prefixEnd_3490269 66377244832870742229113 := by
  unfold tailWord_3490269
  simp only [CollatzResearch.WordTrace]
  refine ⟨127300568592358978333121861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84867045728239318888747907 127300568592358978333121861)
  ·
    refine ⟨23868856611067308437460349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127300568592358978333121861 23868856611067308437460349)
    ·
      refine ⟨8950821229150240664047631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23868856611067308437460349 8950821229150240664047631)
      ·
        refine ⟨13426231843725360996071447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950821229150240664047631 13426231843725360996071447)
        ·
          refine ⟨20139347765588041494107171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426231843725360996071447 20139347765588041494107171)
          ·
            refine ⟨30209021648382062241160757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20139347765588041494107171 30209021648382062241160757)
            ·
              refine ⟨2832095779535818335108821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30209021648382062241160757 2832095779535818335108821)
              ·
                refine ⟨66377244832870742229113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2832095779535818335108821 66377244832870742229113)
                ·
                  rfl

theorem cell23_3490269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 7].length) (baseStart_3490269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490269 prefixEnd_3490269 := by exact prefixLift 3490269
  have htrace : WordTrace (prefixWord ++ tailWord_3490269) baseStart_3490269 baseEnd_3490269 := by
    simpa [prefixWord, tailWord_3490269, baseEnd_3490269] using wordTrace_append hprefix tailTrace_3490269
  have hstable : (prefixWord ++ tailWord_3490269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490269).length < 2 ^ (prefixWord ++ tailWord_3490269).sum := by decide
  have hdescent : baseEnd_3490269 < baseStart_3490269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490279 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3490279 : Nat := 118140960795 + 3490279 * 2 ^ 59
def prefixEnd_3490279 : Nat := 4983230072969 + 3 ^ 40 * 3490279 * 2
def baseEnd_3490279 : Nat := 1792190745294055001061005

theorem tailTrace_3490279 : CollatzResearch.WordTrace tailWord_3490279 prefixEnd_3490279 1792190745294055001061005 := by
  unfold tailWord_3490279
  simp only [CollatzResearch.WordTrace]
  refine ⟨127300933322322750040985891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84867288881548500027323927 127300933322322750040985891)
  ·
    refine ⟨190951399983484125061478837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127300933322322750040985891 190951399983484125061478837)
    ·
      refine ⟨17901693748451636724513641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190951399983484125061478837 17901693748451636724513641)
      ·
        refine ⟨13426270311338727543385231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17901693748451636724513641 13426270311338727543385231)
        ·
          refine ⟨20139405467008091315077847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426270311338727543385231 20139405467008091315077847)
          ·
            refine ⟨30209108200512136972616771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20139405467008091315077847 30209108200512136972616771)
            ·
              refine ⟨45313662300768205458925157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30209108200512136972616771 45313662300768205458925157)
              ·
                refine ⟨8496311681394038523548467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45313662300768205458925157 8496311681394038523548467)
                ·
                  refine ⟨12744467522091057785322701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496311681394038523548467 12744467522091057785322701)
                  ·
                    refine ⟨4779175320784146669496013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12744467522091057785322701 4779175320784146669496013)
                    ·
                      refine ⟨1792190745294055001061005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779175320784146669496013 1792190745294055001061005)
                      ·
                        rfl

theorem cell23_3490279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3490279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490279 prefixEnd_3490279 := by exact prefixLift 3490279
  have htrace : WordTrace (prefixWord ++ tailWord_3490279) baseStart_3490279 baseEnd_3490279 := by
    simpa [prefixWord, tailWord_3490279, baseEnd_3490279] using wordTrace_append hprefix tailTrace_3490279
  have hstable : (prefixWord ++ tailWord_3490279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490279).length < 2 ^ (prefixWord ++ tailWord_3490279).sum := by decide
  have hdescent : baseEnd_3490279 < baseStart_3490279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490280 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_3490280 : Nat := 118140960795 + 3490280 * 2 ^ 59
def prefixEnd_3490280 : Nat := 4983230072969 + 3 ^ 40 * 3490280 * 2
def baseEnd_3490280 : Nat := 1792191258774709497148501

theorem tailTrace_3490280 : CollatzResearch.WordTrace tailWord_3490280 prefixEnd_3490280 1792191258774709497148501 := by
  unfold tailWord_3490280
  simp only [CollatzResearch.WordTrace]
  refine ⟨63650484897659563605886147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84867313196879418141181529 63650484897659563605886147)
  ·
    refine ⟨95475727346489345408829221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63650484897659563605886147 95475727346489345408829221)
    ·
      refine ⟨17901698877466752264155479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95475727346489345408829221 17901698877466752264155479)
      ·
        refine ⟨26852548316200128396233219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17901698877466752264155479 26852548316200128396233219)
        ·
          refine ⟨40278822474300192594349829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26852548316200128396233219 40278822474300192594349829)
          ·
            refine ⟨7552279213931286111440593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40278822474300192594349829 7552279213931286111440593)
            ·
              refine ⟨5664209410448464583580445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7552279213931286111440593 5664209410448464583580445)
              ·
                refine ⟨2124078528918174218842667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664209410448464583580445 2124078528918174218842667)
                ·
                  refine ⟨3186117793377261328264001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124078528918174218842667 3186117793377261328264001)
                  ·
                    refine ⟨2389588345032945996198001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3186117793377261328264001 2389588345032945996198001)
                    ·
                      refine ⟨1792191258774709497148501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389588345032945996198001 1792191258774709497148501)
                      ·
                        rfl

theorem cell23_3490280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_3490280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490280 prefixEnd_3490280 := by exact prefixLift 3490280
  have htrace : WordTrace (prefixWord ++ tailWord_3490280) baseStart_3490280 baseEnd_3490280 := by
    simpa [prefixWord, tailWord_3490280, baseEnd_3490280] using wordTrace_append hprefix tailTrace_3490280
  have hstable : (prefixWord ++ tailWord_3490280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490280).length < 2 ^ (prefixWord ++ tailWord_3490280).sum := by decide
  have hdescent : baseEnd_3490280 < baseStart_3490280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490290 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3490290 : Nat := 118140960795 + 3490290 * 2 ^ 59
def prefixEnd_3490290 : Nat := 4983230072969 + 3 ^ 40 * 3490290 * 2
def baseEnd_3490290 : Nat := 597398797860418152674485

theorem tailTrace_3490290 : CollatzResearch.WordTrace tailWord_3490290 prefixEnd_3490290 597398797860418152674485 := by
  unfold tailWord_3490290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31825333631320724729909081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84867556350188599279757549 31825333631320724729909081)
  ·
    refine ⟨23869000223490543547431811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31825333631320724729909081 23869000223490543547431811)
    ·
      refine ⟨35803500335235815321147717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23869000223490543547431811 35803500335235815321147717)
      ·
        refine ⟨6713156312856715372715197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35803500335235815321147717 6713156312856715372715197)
        ·
          refine ⟨2517433617321268264768199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6713156312856715372715197 2517433617321268264768199)
          ·
            refine ⟨3776150425981902397152299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517433617321268264768199 3776150425981902397152299)
            ·
              refine ⟨5664225638972853595728449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776150425981902397152299 5664225638972853595728449)
              ·
                refine ⟨4248169229229640196796337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5664225638972853595728449 4248169229229640196796337)
                ·
                  refine ⟨3186126921922230147597253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248169229229640196796337 3186126921922230147597253)
                  ·
                    refine ⟨597398797860418152674485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186126921922230147597253 597398797860418152674485)
                    ·
                      rfl

theorem cell23_3490290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3490290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490290 prefixEnd_3490290 := by exact prefixLift 3490290
  have htrace : WordTrace (prefixWord ++ tailWord_3490290) baseStart_3490290 baseEnd_3490290 := by
    simpa [prefixWord, tailWord_3490290, baseEnd_3490290] using wordTrace_append hprefix tailTrace_3490290
  have hstable : (prefixWord ++ tailWord_3490290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490290).length < 2 ^ (prefixWord ++ tailWord_3490290).sum := by decide
  have hdescent : baseEnd_3490290 < baseStart_3490290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490310 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3490310 : Nat := 118140960795 + 3490310 * 2 ^ 59
def prefixEnd_3490310 : Nat := 4983230072969 + 3 ^ 40 * 3490310 * 2
def baseEnd_3490310 : Nat := 1792206663194344379773363

theorem tailTrace_3490310 : CollatzResearch.WordTrace tailWord_3490310 prefixEnd_3490310 1792206663194344379773363 := by
  unfold tailWord_3490310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978189499537826322980137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84868042656806961556909589 3978189499537826322980137)
  ·
    refine ⟨2983642124653369742235103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3978189499537826322980137 2983642124653369742235103)
    ·
      refine ⟨4475463186980054613352655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983642124653369742235103 4475463186980054613352655)
      ·
        refine ⟨6713194780470081920028983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475463186980054613352655 6713194780470081920028983)
        ·
          refine ⟨10069792170705122880043475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713194780470081920028983 10069792170705122880043475)
          ·
            refine ⟨15104688256057684320065213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069792170705122880043475 15104688256057684320065213)
            ·
              refine ⟨5664258096021631620024455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15104688256057684320065213 5664258096021631620024455)
              ·
                refine ⟨8496387144032447430036683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664258096021631620024455 8496387144032447430036683)
                ·
                  refine ⟨12744580716048671145055025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496387144032447430036683 12744580716048671145055025)
                  ·
                    refine ⟨9558435537036503358791269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12744580716048671145055025 9558435537036503358791269)
                    ·
                      refine ⟨1792206663194344379773363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9558435537036503358791269 1792206663194344379773363)
                      ·
                        rfl

theorem cell23_3490310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3490310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490310 prefixEnd_3490310 := by exact prefixLift 3490310
  have htrace : WordTrace (prefixWord ++ tailWord_3490310) baseStart_3490310 baseEnd_3490310 := by
    simpa [prefixWord, tailWord_3490310, baseEnd_3490310] using wordTrace_append hprefix tailTrace_3490310
  have hstable : (prefixWord ++ tailWord_3490310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490310).length < 2 ^ (prefixWord ++ tailWord_3490310).sum := by decide
  have hdescent : baseEnd_3490310 < baseStart_3490310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490339 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5]
def baseStart_3490339 : Nat := 118140960795 + 3490339 * 2 ^ 59
def prefixEnd_3490339 : Nat := 4983230072969 + 3 ^ 40 * 3490339 * 2
def baseEnd_3490339 : Nat := 1792221554133324766310729

theorem tailTrace_3490339 : CollatzResearch.WordTrace tailWord_3490339 prefixEnd_3490339 1792221554133324766310729 := by
  unfold tailWord_3490339
  simp only [CollatzResearch.WordTrace]
  refine ⟨127303121702105380288170071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84868747801403586858780047 127303121702105380288170071)
  ·
    refine ⟨190954682553158070432255107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127303121702105380288170071 190954682553158070432255107)
    ·
      refine ⟨286432023829737105648382661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190954682553158070432255107 286432023829737105648382661)
      ·
        refine ⟨53706004468075707309071749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286432023829737105648382661 53706004468075707309071749)
        ·
          refine ⟨10069875837764195120450953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53706004468075707309071749 10069875837764195120450953)
          ·
            refine ⟨7552406878323146340338215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10069875837764195120450953 7552406878323146340338215)
            ·
              refine ⟨11328610317484719510507323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552406878323146340338215 11328610317484719510507323)
              ·
                refine ⟨16992915476227079265760985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328610317484719510507323 16992915476227079265760985)
                ·
                  refine ⟨12744686607170309449320739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16992915476227079265760985 12744686607170309449320739)
                  ·
                    refine ⟨19117029910755464173981109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12744686607170309449320739 19117029910755464173981109)
                    ·
                      refine ⟨1792221554133324766310729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19117029910755464173981109 1792221554133324766310729)
                      ·
                        rfl

theorem cell23_3490339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_3490339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490339 prefixEnd_3490339 := by exact prefixLift 3490339
  have htrace : WordTrace (prefixWord ++ tailWord_3490339) baseStart_3490339 baseEnd_3490339 := by
    simpa [prefixWord, tailWord_3490339, baseEnd_3490339] using wordTrace_append hprefix tailTrace_3490339
  have hstable : (prefixWord ++ tailWord_3490339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490339).length < 2 ^ (prefixWord ++ tailWord_3490339).sum := by decide
  have hdescent : baseEnd_3490339 < baseStart_3490339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490389 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3490389 : Nat := 118140960795 + 3490389 * 2 ^ 59
def prefixEnd_3490389 : Nat := 4983230072969 + 3 ^ 40 * 3490389 * 2
def baseEnd_3490389 : Nat := 597415742722016523561833

theorem tailTrace_3490389 : CollatzResearch.WordTrace tailWord_3490389 prefixEnd_3490389 597415742722016523561833 := by
  unfold tailWord_3490389
  simp only [CollatzResearch.WordTrace]
  refine ⟨127304945351924238827490221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84869963567949492551660147 127304945351924238827490221)
  ·
    refine ⟨47739354506971589560308833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127304945351924238827490221 47739354506971589560308833)
    ·
      refine ⟨35804515880228692170231625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47739354506971589560308833 35804515880228692170231625)
      ·
        refine ⟨26853386910171519127673719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35804515880228692170231625 26853386910171519127673719)
        ·
          refine ⟨40280080365257278691510579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26853386910171519127673719 40280080365257278691510579)
          ·
            refine ⟨60420120547885918037265869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40280080365257278691510579 60420120547885918037265869)
            ·
              refine ⟨22657545205457219263974701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60420120547885918037265869 22657545205457219263974701)
              ·
                refine ⟨8496579452046457223990513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22657545205457219263974701 8496579452046457223990513)
                ·
                  refine ⟨6372434589034842917992885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8496579452046457223990513 6372434589034842917992885)
                  ·
                    refine ⟨597415742722016523561833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6372434589034842917992885 597415742722016523561833)
                    ·
                      rfl

theorem cell23_3490389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3490389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490389 prefixEnd_3490389 := by exact prefixLift 3490389
  have htrace : WordTrace (prefixWord ++ tailWord_3490389) baseStart_3490389 baseEnd_3490389 := by
    simpa [prefixWord, tailWord_3490389, baseEnd_3490389] using wordTrace_append hprefix tailTrace_3490389
  have hstable : (prefixWord ++ tailWord_3490389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490389).length < 2 ^ (prefixWord ++ tailWord_3490389).sum := by decide
  have hdescent : baseEnd_3490389 < baseStart_3490389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490436 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_3490436 : Nat := 118140960795 + 3490436 * 2 ^ 59
def prefixEnd_3490436 : Nat := 4983230072969 + 3 ^ 40 * 3490436 * 2
def baseEnd_3490436 : Nat := 597423787252270295599261

theorem tailTrace_3490436 : CollatzResearch.WordTrace tailWord_3490436 prefixEnd_3490436 597423787252270295599261 := by
  unfold tailWord_3490436
  simp only [CollatzResearch.WordTrace]
  refine ⟨63653329791376982927225581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84871106388502643902967441 63653329791376982927225581)
  ·
    refine ⟨23869998671766368597709593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63653329791376982927225581 23869998671766368597709593)
    ·
      refine ⟨17902499003824776448282195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23869998671766368597709593 17902499003824776448282195)
      ·
        refine ⟨26853748505737164672423293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17902499003824776448282195 26853748505737164672423293)
        ·
          refine ⟨10070155689651436752158735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26853748505737164672423293 10070155689651436752158735)
          ·
            refine ⟨15105233534477155128238103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10070155689651436752158735 15105233534477155128238103)
            ·
              refine ⟨22657850301715732692357155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15105233534477155128238103 22657850301715732692357155)
              ·
                refine ⟨33986775452573599038535733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22657850301715732692357155 33986775452573599038535733)
                ·
                  refine ⟨3186260198678774909862725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33986775452573599038535733 3186260198678774909862725)
                  ·
                    refine ⟨597423787252270295599261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186260198678774909862725 597423787252270295599261)
                    ·
                      rfl

theorem cell23_3490436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_3490436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490436 prefixEnd_3490436 := by exact prefixLift 3490436
  have htrace : WordTrace (prefixWord ++ tailWord_3490436) baseStart_3490436 baseEnd_3490436 := by
    simpa [prefixWord, tailWord_3490436, baseEnd_3490436] using wordTrace_append hprefix tailTrace_3490436
  have hstable : (prefixWord ++ tailWord_3490436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490436).length < 2 ^ (prefixWord ++ tailWord_3490436).sum := by decide
  have hdescent : baseEnd_3490436 < baseStart_3490436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490446 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3490446 : Nat := 118140960795 + 3490446 * 2 ^ 59
def prefixEnd_3490446 : Nat := 4983230072969 + 3 ^ 40 * 3490446 * 2
def baseEnd_3490446 : Nat := 1792276496563355847672737

theorem tailTrace_3490446 : CollatzResearch.WordTrace tailWord_3490446 prefixEnd_3490446 1792276496563355847672737 := by
  unfold tailWord_3490446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15913378039089717195289399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84871349541811825041543461 15913378039089717195289399)
  ·
    refine ⟨23870067058634575792934099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15913378039089717195289399 23870067058634575792934099)
    ·
      refine ⟨35805100587951863689401149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23870067058634575792934099 35805100587951863689401149)
      ·
        refine ⟨13426912720481948883525431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35805100587951863689401149 13426912720481948883525431)
        ·
          refine ⟨20140369080722923325288147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426912720481948883525431 20140369080722923325288147)
          ·
            refine ⟨30210553621084384987932221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20140369080722923325288147 30210553621084384987932221)
            ·
              refine ⟨11328957607906644370474583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30210553621084384987932221 11328957607906644370474583)
              ·
                refine ⟨16993436411859966555711875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328957607906644370474583 16993436411859966555711875)
                ·
                  refine ⟨25490154617789949833567813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16993436411859966555711875 25490154617789949833567813)
                  ·
                    refine ⟨4779403990835615593793965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25490154617789949833567813 4779403990835615593793965)
                    ·
                      refine ⟨1792276496563355847672737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779403990835615593793965 1792276496563355847672737)
                      ·
                        rfl

theorem cell23_3490446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3490446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490446 prefixEnd_3490446 := by exact prefixLift 3490446
  have htrace : WordTrace (prefixWord ++ tailWord_3490446) baseStart_3490446 baseEnd_3490446 := by
    simpa [prefixWord, tailWord_3490446, baseEnd_3490446] using wordTrace_append hprefix tailTrace_3490446
  have hstable : (prefixWord ++ tailWord_3490446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490446).length < 2 ^ (prefixWord ++ tailWord_3490446).sum := by decide
  have hdescent : baseEnd_3490446 < baseStart_3490446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490493 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3490493 : Nat := 118140960795 + 3490493 * 2 ^ 59
def prefixEnd_3490493 : Nat := 4983230072969 + 3 ^ 40 * 3490493 * 2
def baseEnd_3490493 : Nat := 1792300630154117163785021

theorem tailTrace_3490493 : CollatzResearch.WordTrace tailWord_3490493 prefixEnd_3490493 1792300630154117163785021 := by
  unfold tailWord_3490493
  simp only [CollatzResearch.WordTrace]
  refine ⟨127308738543547464589276133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84872492362364976392850755 127308738543547464589276133)
  ·
    refine ⟨23870388476915149610489275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127308738543547464589276133 23870388476915149610489275)
    ·
      refine ⟨35805582715372724415733913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23870388476915149610489275 35805582715372724415733913)
      ·
        refine ⟨26854187036529543311800435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35805582715372724415733913 26854187036529543311800435)
        ·
          refine ⟨40281280554794314967700653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26854187036529543311800435 40281280554794314967700653)
          ·
            refine ⟨15105480208047868112887745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40281280554794314967700653 15105480208047868112887745)
            ·
              refine ⟨11329110156035901084665809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15105480208047868112887745 11329110156035901084665809)
              ·
                refine ⟨8496832617026925813499357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11329110156035901084665809 8496832617026925813499357)
                ·
                  refine ⟨3186312231385097180062259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8496832617026925813499357 3186312231385097180062259)
                  ·
                    refine ⟨4779468347077645770093389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3186312231385097180062259 4779468347077645770093389)
                    ·
                      refine ⟨1792300630154117163785021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779468347077645770093389 1792300630154117163785021)
                      ·
                        rfl

theorem cell23_3490493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3490493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490493 prefixEnd_3490493 := by exact prefixLift 3490493
  have htrace : WordTrace (prefixWord ++ tailWord_3490493) baseStart_3490493 baseEnd_3490493 := by
    simpa [prefixWord, tailWord_3490493, baseEnd_3490493] using wordTrace_append hprefix tailTrace_3490493
  have hstable : (prefixWord ++ tailWord_3490493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490493).length < 2 ^ (prefixWord ++ tailWord_3490493).sum := by decide
  have hdescent : baseEnd_3490493 < baseStart_3490493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490496 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 1, 5]
def baseStart_3490496 : Nat := 118140960795 + 3490496 * 2 ^ 59
def prefixEnd_3490496 : Nat := 4983230072969 + 3 ^ 40 * 3490496 * 2
def baseEnd_3490496 : Nat := 597434056865360217349169

theorem tailTrace_3490496 : CollatzResearch.WordTrace tailWord_3490496 prefixEnd_3490496 597434056865360217349169 := by
  unfold tailWord_3490496
  simp only [CollatzResearch.WordTrace]
  refine ⟨63654423981268298050817671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84872565308357730734423561 63654423981268298050817671)
  ·
    refine ⟨95481635971902447076226507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63654423981268298050817671 95481635971902447076226507)
    ·
      refine ⟨143222453957853670614339761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95481635971902447076226507 143222453957853670614339761)
      ·
        refine ⟨107416840468390252960754821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143222453957853670614339761 107416840468390252960754821)
        ·
          refine ⟨20140657587823172430141529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107416840468390252960754821 20140657587823172430141529)
          ·
            refine ⟨15105493190867379322606147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20140657587823172430141529 15105493190867379322606147)
            ·
              refine ⟨22658239786301068983909221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15105493190867379322606147 22658239786301068983909221)
              ·
                refine ⟨4248419959931450434482979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22658239786301068983909221 4248419959931450434482979)
                ·
                  refine ⟨6372629939897175651724469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248419959931450434482979 6372629939897175651724469)
                  ·
                    refine ⟨597434056865360217349169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6372629939897175651724469 597434056865360217349169)
                    ·
                      rfl

theorem cell23_3490496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_3490496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490496 prefixEnd_3490496 := by exact prefixLift 3490496
  have htrace : WordTrace (prefixWord ++ tailWord_3490496) baseStart_3490496 baseEnd_3490496 := by
    simpa [prefixWord, tailWord_3490496, baseEnd_3490496] using wordTrace_append hprefix tailTrace_3490496
  have hstable : (prefixWord ++ tailWord_3490496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490496).length < 2 ^ (prefixWord ++ tailWord_3490496).sum := by decide
  have hdescent : baseEnd_3490496 < baseStart_3490496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490527 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 1, 1, 3]
def baseStart_3490527 : Nat := 118140960795 + 3490527 * 2 ^ 59
def prefixEnd_3490527 : Nat := 4983230072969 + 3 ^ 40 * 3490527 * 2
def baseEnd_3490527 : Nat := 1792318088496370030759865

theorem tailTrace_3490527 : CollatzResearch.WordTrace tailWord_3490527 prefixEnd_3490527 1792318088496370030759865 := by
  unfold tailWord_3490527
  simp only [CollatzResearch.WordTrace]
  refine ⟨127309978625424288396013835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84873319083616192264009223 127309978625424288396013835)
  ·
    refine ⟨190964967938136432594020753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127309978625424288396013835 190964967938136432594020753)
    ·
      refine ⟨143223725953602324445515565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190964967938136432594020753 143223725953602324445515565)
      ·
        refine ⟨53708897232600871667068337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143223725953602324445515565 53708897232600871667068337)
        ·
          refine ⟨40281672924450653750301253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53708897232600871667068337 40281672924450653750301253)
          ·
            refine ⟨7552813673334497578181485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40281672924450653750301253 7552813673334497578181485)
            ·
              refine ⟨2832305127500436591818057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7552813673334497578181485 2832305127500436591818057)
              ·
                refine ⟨2124228845625327443863543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832305127500436591818057 2124228845625327443863543)
                ·
                  refine ⟨3186343268437991165795315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124228845625327443863543 3186343268437991165795315)
                  ·
                    refine ⟨4779514902656986748692973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3186343268437991165795315 4779514902656986748692973)
                    ·
                      refine ⟨1792318088496370030759865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779514902656986748692973 1792318088496370030759865)
                      ·
                        rfl

theorem cell23_3490527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_3490527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490527 prefixEnd_3490527 := by exact prefixLift 3490527
  have htrace : WordTrace (prefixWord ++ tailWord_3490527) baseStart_3490527 baseEnd_3490527 := by
    simpa [prefixWord, tailWord_3490527, baseEnd_3490527] using wordTrace_append hprefix tailTrace_3490527
  have hstable : (prefixWord ++ tailWord_3490527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490527).length < 2 ^ (prefixWord ++ tailWord_3490527).sum := by decide
  have hdescent : baseEnd_3490527 < baseStart_3490527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490543 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 2, 4]
def baseStart_3490543 : Nat := 118140960795 + 3490543 * 2 ^ 59
def prefixEnd_3490543 : Nat := 4983230072969 + 3 ^ 40 * 3490543 * 2
def baseEnd_3490543 : Nat := 597442101395613989386597

theorem tailTrace_3490543 : CollatzResearch.WordTrace tailWord_3490543 prefixEnd_3490543 597442101395613989386597 := by
  unfold tailWord_3490543
  simp only [CollatzResearch.WordTrace]
  refine ⟨127310562193366323128596283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84873708128910882085730855 127310562193366323128596283)
  ·
    refine ⟨190965843290049484692894425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127310562193366323128596283 190965843290049484692894425)
    ·
      refine ⟨143224382467537113519670819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190965843290049484692894425 143224382467537113519670819)
      ·
        refine ⟨214836573701305670279506229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143224382467537113519670819 214836573701305670279506229)
        ·
          refine ⟨20140928784497406588703709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214836573701305670279506229 20140928784497406588703709)
          ·
            refine ⟨7552848294186527470763891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20140928784497406588703709 7552848294186527470763891)
            ·
              refine ⟨11329272441279791206145837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552848294186527470763891 11329272441279791206145837)
              ·
                refine ⟨4248477165479921702304689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11329272441279791206145837 4248477165479921702304689)
                ·
                  refine ⟨3186357874109941276728517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248477165479921702304689 3186357874109941276728517)
                  ·
                    refine ⟨597442101395613989386597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186357874109941276728517 597442101395613989386597)
                    ·
                      rfl

theorem cell23_3490543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_3490543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490543 prefixEnd_3490543 := by exact prefixLift 3490543
  have htrace : WordTrace (prefixWord ++ tailWord_3490543) baseStart_3490543 baseEnd_3490543 := by
    simpa [prefixWord, tailWord_3490543, baseEnd_3490543] using wordTrace_append hprefix tailTrace_3490543
  have hstable : (prefixWord ++ tailWord_3490543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490543).length < 2 ^ (prefixWord ++ tailWord_3490543).sum := by decide
  have hdescent : baseEnd_3490543 < baseStart_3490543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490546 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3490546 : Nat := 118140960795 + 3490546 * 2 ^ 59
def prefixEnd_3490546 : Nat := 4983230072969 + 3 ^ 40 * 3490546 * 2
def baseEnd_3490546 : Nat := 1792327844628805456422277

theorem tailTrace_3490546 : CollatzResearch.WordTrace tailWord_3490546 prefixEnd_3490546 1792327844628805456422277 := by
  unfold tailWord_3490546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31827667903088863660238873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84873781074903636427303661 31827667903088863660238873)
  ·
    refine ⟨23870750927316647745179155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31827667903088863660238873 23870750927316647745179155)
    ·
      refine ⟨35806126390974971617768733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23870750927316647745179155 35806126390974971617768733)
      ·
        refine ⟨13427297396615614356663275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35806126390974971617768733 13427297396615614356663275)
        ·
          refine ⟨20140946094923421534994913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13427297396615614356663275 20140946094923421534994913)
          ·
            refine ⟨15105709571192566151246185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20140946094923421534994913 15105709571192566151246185)
            ·
              refine ⟨11329282178394424613434639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15105709571192566151246185 11329282178394424613434639)
              ·
                refine ⟨16993923267591636920151959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11329282178394424613434639 16993923267591636920151959)
                ·
                  refine ⟨25490884901387455380227939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16993923267591636920151959 25490884901387455380227939)
                  ·
                    refine ⟨38236327352081183070341909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25490884901387455380227939 38236327352081183070341909)
                    ·
                      refine ⟨1792327844628805456422277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38236327352081183070341909 1792327844628805456422277)
                      ·
                        rfl

theorem cell23_3490546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3490546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490546 prefixEnd_3490546 := by exact prefixLift 3490546
  have htrace : WordTrace (prefixWord ++ tailWord_3490546) baseStart_3490546 baseEnd_3490546 := by
    simpa [prefixWord, tailWord_3490546, baseEnd_3490546] using wordTrace_append hprefix tailTrace_3490546
  have hstable : (prefixWord ++ tailWord_3490546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490546).length < 2 ^ (prefixWord ++ tailWord_3490546).sum := by decide
  have hdescent : baseEnd_3490546 < baseStart_3490546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490550 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3490550 : Nat := 118140960795 + 3490550 * 2 ^ 59
def prefixEnd_3490550 : Nat := 4983230072969 + 3 ^ 40 * 3490550 * 2
def baseEnd_3490550 : Nat := 1792329898551423440772259

theorem tailTrace_3490550 : CollatzResearch.WordTrace tailWord_3490550 prefixEnd_3490550 1792329898551423440772259 := by
  unfold tailWord_3490550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956926094021310207756319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84873878336227308882734069 7956926094021310207756319)
  ·
    refine ⟨11935389141031965311634479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956926094021310207756319 11935389141031965311634479)
    ·
      refine ⟨17903083711547947967451719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11935389141031965311634479 17903083711547947967451719)
      ·
        refine ⟨26854625567321921951177579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17903083711547947967451719 26854625567321921951177579)
        ·
          refine ⟨40281938350982882926766369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26854625567321921951177579 40281938350982882926766369)
          ·
            refine ⟨30211453763237162195074777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40281938350982882926766369 30211453763237162195074777)
            ·
              refine ⟨22658590322427871646306083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30211453763237162195074777 22658590322427871646306083)
              ·
                refine ⟨33987885483641807469459125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22658590322427871646306083 33987885483641807469459125)
                ·
                  refine ⟨3186364264091419450261793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33987885483641807469459125 3186364264091419450261793)
                  ·
                    refine ⟨2389773198068564587696345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3186364264091419450261793 2389773198068564587696345)
                    ·
                      refine ⟨1792329898551423440772259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389773198068564587696345 1792329898551423440772259)
                      ·
                        rfl

theorem cell23_3490550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3490550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490550 prefixEnd_3490550 := by exact prefixLift 3490550
  have htrace : WordTrace (prefixWord ++ tailWord_3490550) baseStart_3490550 baseEnd_3490550 := by
    simpa [prefixWord, tailWord_3490550, baseEnd_3490550] using wordTrace_append hprefix tailTrace_3490550
  have hstable : (prefixWord ++ tailWord_3490550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490550).length < 2 ^ (prefixWord ++ tailWord_3490550).sum := by decide
  have hdescent : baseEnd_3490550 < baseStart_3490550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490570 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_3490570 : Nat := 118140960795 + 3490570 * 2 ^ 59
def prefixEnd_3490570 : Nat := 4983230072969 + 3 ^ 40 * 3490570 * 2
def baseEnd_3490570 : Nat := 1792340168164513362522167

theorem tailTrace_3490570 : CollatzResearch.WordTrace tailWord_3490570 prefixEnd_3490570 1792340168164513362522167 := by
  unfold tailWord_3490570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31827886741067126684957291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84874364642845671159886109 31827886741067126684957291)
  ·
    refine ⟨47741830111600690027435937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31827886741067126684957291 47741830111600690027435937)
    ·
      refine ⟨35806372583700517520576953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47741830111600690027435937 35806372583700517520576953)
      ·
        refine ⟨26854779437775388140432715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35806372583700517520576953 26854779437775388140432715)
        ·
          refine ⟨40282169156663082210649073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26854779437775388140432715 40282169156663082210649073)
          ·
            refine ⟨30211626867497311657986805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40282169156663082210649073 30211626867497311657986805)
            ·
              refine ⟨2832340018827872967936263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30211626867497311657986805 2832340018827872967936263)
              ·
                refine ⟨4248510028241809451904395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832340018827872967936263 4248510028241809451904395)
                ·
                  refine ⟨6372765042362714177856593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248510028241809451904395 6372765042362714177856593)
                  ·
                    refine ⟨4779573781772035633392445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6372765042362714177856593 4779573781772035633392445)
                    ·
                      refine ⟨1792340168164513362522167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779573781772035633392445 1792340168164513362522167)
                      ·
                        rfl

theorem cell23_3490570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_3490570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490570 prefixEnd_3490570 := by exact prefixLift 3490570
  have htrace : WordTrace (prefixWord ++ tailWord_3490570) baseStart_3490570 baseEnd_3490570 := by
    simpa [prefixWord, tailWord_3490570, baseEnd_3490570] using wordTrace_append hprefix tailTrace_3490570
  have hstable : (prefixWord ++ tailWord_3490570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490570).length < 2 ^ (prefixWord ++ tailWord_3490570).sum := by decide
  have hdescent : baseEnd_3490570 < baseStart_3490570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490573 : List Nat := [1, 7, 2, 13]
def baseStart_3490573 : Nat := 118140960795 + 3490573 * 2 ^ 59
def prefixEnd_3490573 : Nat := 4983230072969 + 3 ^ 40 * 3490573 * 2
def baseEnd_3490573 : Nat := 819543533884991701319

theorem tailTrace_3490573 : CollatzResearch.WordTrace tailWord_3490573 prefixEnd_3490573 819543533884991701319 := by
  unfold tailWord_3490573
  simp only [CollatzResearch.WordTrace]
  refine ⟨127311656383257638252188373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84874437588838425501458915 127311656383257638252188373)
  ·
    refine ⟨2983866946482600896535665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127311656383257638252188373 2983866946482600896535665)
    ·
      refine ⟨2237900209861950672401749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2983866946482600896535665 2237900209861950672401749)
      ·
        refine ⟨819543533884991701319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2237900209861950672401749 819543533884991701319)
        ·
          rfl

theorem cell23_3490573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 13].length) (baseStart_3490573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490573 prefixEnd_3490573 := by exact prefixLift 3490573
  have htrace : WordTrace (prefixWord ++ tailWord_3490573) baseStart_3490573 baseEnd_3490573 := by
    simpa [prefixWord, tailWord_3490573, baseEnd_3490573] using wordTrace_append hprefix tailTrace_3490573
  have hstable : (prefixWord ++ tailWord_3490573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490573).length < 2 ^ (prefixWord ++ tailWord_3490573).sum := by decide
  have hdescent : baseEnd_3490573 < baseStart_3490573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490578 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3490578 : Nat := 118140960795 + 3490578 * 2 ^ 59
def prefixEnd_3490578 : Nat := 4983230072969 + 3 ^ 40 * 3490578 * 2
def baseEnd_3490578 : Nat := 1792344276009749331222131

theorem tailTrace_3490578 : CollatzResearch.WordTrace tailWord_3490578 prefixEnd_3490578 1792344276009749331222131 := by
  unfold tailWord_3490578
  simp only [CollatzResearch.WordTrace]
  refine ⟨31827959687059881026530097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84874559165493016070746925 31827959687059881026530097)
  ·
    refine ⟨23870969765294910769897573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31827959687059881026530097 23870969765294910769897573)
    ·
      refine ⟨4475806830992795769355795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23870969765294910769897573 4475806830992795769355795)
      ·
        refine ⟨6713710246489193654033693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475806830992795769355795 6713710246489193654033693)
        ·
          refine ⟨2517641342433447620262635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6713710246489193654033693 2517641342433447620262635)
          ·
            refine ⟨3776462013650171430393953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517641342433447620262635 3776462013650171430393953)
            ·
              refine ⟨2832346510237628572795465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3776462013650171430393953 2832346510237628572795465)
              ·
                refine ⟨2124259882678221429596599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832346510237628572795465 2124259882678221429596599)
                ·
                  refine ⟨3186389824017332144394899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124259882678221429596599 3186389824017332144394899)
                  ·
                    refine ⟨4779584736025998216592349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3186389824017332144394899 4779584736025998216592349)
                    ·
                      refine ⟨1792344276009749331222131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779584736025998216592349 1792344276009749331222131)
                      ·
                        rfl

theorem cell23_3490578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3490578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490578 prefixEnd_3490578 := by exact prefixLift 3490578
  have htrace : WordTrace (prefixWord ++ tailWord_3490578) baseStart_3490578 baseEnd_3490578 := by
    simpa [prefixWord, tailWord_3490578, baseEnd_3490578] using wordTrace_append hprefix tailTrace_3490578
  have hstable : (prefixWord ++ tailWord_3490578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490578).length < 2 ^ (prefixWord ++ tailWord_3490578).sum := by decide
  have hdescent : baseEnd_3490578 < baseStart_3490578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490593 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_3490593 : Nat := 118140960795 + 3490593 * 2 ^ 59
def prefixEnd_3490593 : Nat := 4983230072969 + 3 ^ 40 * 3490593 * 2
def baseEnd_3490593 : Nat := 1792351978219566772534561

theorem tailTrace_3490593 : CollatzResearch.WordTrace tailWord_3490593 prefixEnd_3490593 1792351978219566772534561 := by
  unfold tailWord_3490593
  simp only [CollatzResearch.WordTrace]
  refine ⟨127312385843185181667916433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84874923895456787778610955 127312385843185181667916433)
  ·
    refine ⟨95484289382388886250937325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127312385843185181667916433 95484289382388886250937325)
    ·
      refine ⟨35806608518395832344101497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95484289382388886250937325 35806608518395832344101497)
      ·
        refine ⟨26854956388796874258076123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35806608518395832344101497 26854956388796874258076123)
        ·
          refine ⟨40282434583195311387114185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26854956388796874258076123 40282434583195311387114185)
          ·
            refine ⟨30211825937396483540335639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40282434583195311387114185 30211825937396483540335639)
            ·
              refine ⟨45317738906094725310503459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30211825937396483540335639 45317738906094725310503459)
              ·
                refine ⟨67976608359142087965755189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45317738906094725310503459 67976608359142087965755189)
                ·
                  refine ⟨6372807033669570746789549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67976608359142087965755189 6372807033669570746789549)
                  ·
                    refine ⟨2389802637626089030046081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6372807033669570746789549 2389802637626089030046081)
                    ·
                      refine ⟨1792351978219566772534561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389802637626089030046081 1792351978219566772534561)
                      ·
                        rfl

theorem cell23_3490593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_3490593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490593 prefixEnd_3490593 := by exact prefixLift 3490593
  have htrace : WordTrace (prefixWord ++ tailWord_3490593) baseStart_3490593 baseEnd_3490593 := by
    simpa [prefixWord, tailWord_3490593, baseEnd_3490593] using wordTrace_append hprefix tailTrace_3490593
  have hstable : (prefixWord ++ tailWord_3490593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490593).length < 2 ^ (prefixWord ++ tailWord_3490593).sum := by decide
  have hdescent : baseEnd_3490593 < baseStart_3490593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490600 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3490600 : Nat := 118140960795 + 3490600 * 2 ^ 59
def prefixEnd_3490600 : Nat := 4983230072969 + 3 ^ 40 * 3490600 * 2
def baseEnd_3490600 : Nat := 1792355572584148245147029

theorem tailTrace_3490600 : CollatzResearch.WordTrace tailWord_3490600 prefixEnd_3490600 1792355572584148245147029 := by
  unfold tailWord_3490600
  simp only [CollatzResearch.WordTrace]
  refine ⟨63656320577079910931710627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84875094102773214575614169 63656320577079910931710627)
  ·
    refine ⟨95484480865619866397565941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63656320577079910931710627 95484480865619866397565941)
    ·
      refine ⟨8951670081151862474771807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95484480865619866397565941 8951670081151862474771807)
      ·
        refine ⟨13427505121727793712157711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8951670081151862474771807 13427505121727793712157711)
        ·
          refine ⟨20141257682591690568236567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13427505121727793712157711 20141257682591690568236567)
          ·
            refine ⟨30211886523887535852354851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20141257682591690568236567 30211886523887535852354851)
            ·
              refine ⟨45317829785831303778532277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30211886523887535852354851 45317829785831303778532277)
              ·
                refine ⟨4248546542421684729237401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45317829785831303778532277 4248546542421684729237401)
                ·
                  refine ⟨3186409906816263546928051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248546542421684729237401 3186409906816263546928051)
                  ·
                    refine ⟨4779614860224395320392077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3186409906816263546928051 4779614860224395320392077)
                    ·
                      refine ⟨1792355572584148245147029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779614860224395320392077 1792355572584148245147029)
                      ·
                        rfl

theorem cell23_3490600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3490600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490600 prefixEnd_3490600 := by exact prefixLift 3490600
  have htrace : WordTrace (prefixWord ++ tailWord_3490600) baseStart_3490600 baseEnd_3490600 := by
    simpa [prefixWord, tailWord_3490600, baseEnd_3490600] using wordTrace_append hprefix tailTrace_3490600
  have hstable : (prefixWord ++ tailWord_3490600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490600).length < 2 ^ (prefixWord ++ tailWord_3490600).sum := by decide
  have hdescent : baseEnd_3490600 < baseStart_3490600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490610 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_3490610 : Nat := 118140960795 + 3490610 * 2 ^ 59
def prefixEnd_3490610 : Nat := 4983230072969 + 3 ^ 40 * 3490610 * 2
def baseEnd_3490610 : Nat := 1792360707390693206021983

theorem tailTrace_3490610 : CollatzResearch.WordTrace tailWord_3490610 prefixEnd_3490610 1792360707390693206021983 := by
  unfold tailWord_3490610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31828251471030898392821321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84875337256082395714190189 31828251471030898392821321)
  ·
    refine ⟨23871188603273173794615991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31828251471030898392821321 23871188603273173794615991)
    ·
      refine ⟨35806782904909760691923987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23871188603273173794615991 35806782904909760691923987)
      ·
        refine ⟨53710174357364641037885981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35806782904909760691923987 53710174357364641037885981)
        ·
          refine ⟨20141315384011740389207243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53710174357364641037885981 20141315384011740389207243)
          ·
            refine ⟨30211973076017610583810865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20141315384011740389207243 30211973076017610583810865)
            ·
              refine ⟨22658979807013207937858149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30211973076017610583810865 22658979807013207937858149)
              ·
                refine ⟨4248558713814976488348403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22658979807013207937858149 4248558713814976488348403)
                ·
                  refine ⟨6372838070722464732522605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248558713814976488348403 6372838070722464732522605)
                  ·
                    refine ⟨2389814276520924274695977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6372838070722464732522605 2389814276520924274695977)
                    ·
                      refine ⟨1792360707390693206021983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389814276520924274695977 1792360707390693206021983)
                      ·
                        rfl

theorem cell23_3490610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_3490610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490610 prefixEnd_3490610 := by exact prefixLift 3490610
  have htrace : WordTrace (prefixWord ++ tailWord_3490610) baseStart_3490610 baseEnd_3490610 := by
    simpa [prefixWord, tailWord_3490610, baseEnd_3490610] using wordTrace_append hprefix tailTrace_3490610
  have hstable : (prefixWord ++ tailWord_3490610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490610).length < 2 ^ (prefixWord ++ tailWord_3490610).sum := by decide
  have hdescent : baseEnd_3490610 < baseStart_3490610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490693 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_3490693 : Nat := 118140960795 + 3490693 * 2 ^ 59
def prefixEnd_3490693 : Nat := 4983230072969 + 3 ^ 40 * 3490693 * 2
def baseEnd_3490693 : Nat := 597467775428338793761367

theorem tailTrace_3490693 : CollatzResearch.WordTrace tailWord_3490693 prefixEnd_3490693 597467775428338793761367 := by
  unfold tailWord_3490693
  simp only [CollatzResearch.WordTrace]
  refine ⟨127316033142822898746556733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84877355428548599164371155 127316033142822898746556733)
  ·
    refine ⟨47743512428558587029958775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127316033142822898746556733 47743512428558587029958775)
    ·
      refine ⟨71615268642837880544938163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47743512428558587029958775 71615268642837880544938163)
      ·
        refine ⟨107422902964256820817407245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71615268642837880544938163 107422902964256820817407245)
        ·
          refine ⟨40283588611596307806527717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107422902964256820817407245 40283588611596307806527717)
          ·
            refine ⟨7553172864674307713723947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40283588611596307806527717 7553172864674307713723947)
            ·
              refine ⟨11329759297011461570585921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553172864674307713723947 11329759297011461570585921)
              ·
                refine ⟨8497319472758596177939441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11329759297011461570585921 8497319472758596177939441)
                ·
                  refine ⟨6372989604568947133454581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8497319472758596177939441 6372989604568947133454581)
                  ·
                    refine ⟨597467775428338793761367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6372989604568947133454581 597467775428338793761367)
                    ·
                      rfl

theorem cell23_3490693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_3490693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490693 prefixEnd_3490693 := by exact prefixLift 3490693
  have htrace : WordTrace (prefixWord ++ tailWord_3490693) baseStart_3490693 baseEnd_3490693 := by
    simpa [prefixWord, tailWord_3490693, baseEnd_3490693] using wordTrace_append hprefix tailTrace_3490693
  have hstable : (prefixWord ++ tailWord_3490693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490693).length < 2 ^ (prefixWord ++ tailWord_3490693).sum := by decide
  have hdescent : baseEnd_3490693 < baseStart_3490693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490713 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 6, 2]
def baseStart_3490713 : Nat := 118140960795 + 3490713 * 2 ^ 59
def prefixEnd_3490713 : Nat := 4983230072969 + 3 ^ 40 * 3490713 * 2
def baseEnd_3490713 : Nat := 1792413595898106303034009

theorem tailTrace_3490713 : CollatzResearch.WordTrace tailWord_3490713 prefixEnd_3490713 1792413595898106303034009 := by
  unfold tailWord_3490713
  simp only [CollatzResearch.WordTrace]
  refine ⟨127316762602750442162284793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84877841735166961441523195 127316762602750442162284793)
  ·
    refine ⟨95487571952062831621713595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127316762602750442162284793 95487571952062831621713595)
    ·
      refine ⟨143231357928094247432570393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95487571952062831621713595 143231357928094247432570393)
      ·
        refine ⟨107423518446070685574427795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143231357928094247432570393 107423518446070685574427795)
        ·
          refine ⟨161135277669106028361641693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107423518446070685574427795 161135277669106028361641693)
          ·
            refine ⟨60425729125914760635615635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161135277669106028361641693 60425729125914760635615635)
            ·
              refine ⟨90638593688872140953423453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60425729125914760635615635 90638593688872140953423453)
              ·
                refine ⟨33989472633327052857533795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90638593688872140953423453 33989472633327052857533795)
                ·
                  refine ⟨50984208949990579286300693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33989472633327052857533795 50984208949990579286300693)
                  ·
                    refine ⟨2389884794530808404045345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50984208949990579286300693 2389884794530808404045345)
                    ·
                      refine ⟨1792413595898106303034009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2389884794530808404045345 1792413595898106303034009)
                      ·
                        rfl

theorem cell23_3490713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_3490713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490713 prefixEnd_3490713 := by exact prefixLift 3490713
  have htrace : WordTrace (prefixWord ++ tailWord_3490713) baseStart_3490713 baseEnd_3490713 := by
    simpa [prefixWord, tailWord_3490713, baseEnd_3490713] using wordTrace_append hprefix tailTrace_3490713
  have hstable : (prefixWord ++ tailWord_3490713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490713).length < 2 ^ (prefixWord ++ tailWord_3490713).sum := by decide
  have hdescent : baseEnd_3490713 < baseStart_3490713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490723 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 3, 4]
def baseStart_3490723 : Nat := 118140960795 + 3490723 * 2 ^ 59
def prefixEnd_3490723 : Nat := 4983230072969 + 3 ^ 40 * 3490723 * 2
def baseEnd_3490723 : Nat := 597472910234883754636321

theorem tailTrace_3490723 : CollatzResearch.WordTrace tailWord_3490723 prefixEnd_3490723 597472910234883754636321 := by
  unfold tailWord_3490723
  simp only [CollatzResearch.WordTrace]
  refine ⟨127317127332714213870148823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84878084888476142580099215 127317127332714213870148823)
  ·
    refine ⟨190975690999071320805223235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127317127332714213870148823 190975690999071320805223235)
    ·
      refine ⟨286463536498606981207834853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190975690999071320805223235 286463536498606981207834853)
      ·
        refine ⟨53711913093488808976469035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286463536498606981207834853 53711913093488808976469035)
        ·
          refine ⟨80567869640233213464703553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53711913093488808976469035 80567869640233213464703553)
          ·
            refine ⟨60425902230174910098527665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80567869640233213464703553 60425902230174910098527665)
            ·
              refine ⟨45319426672631182573895749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60425902230174910098527665 45319426672631182573895749)
              ·
                refine ⟨8497392501118346732605453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45319426672631182573895749 8497392501118346732605453)
                ·
                  refine ⟨3186522187919380024727045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8497392501118346732605453 3186522187919380024727045)
                  ·
                    refine ⟨597472910234883754636321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186522187919380024727045 597472910234883754636321)
                    ·
                      rfl

theorem cell23_3490723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 4].length) (baseStart_3490723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490723 prefixEnd_3490723 := by exact prefixLift 3490723
  have htrace : WordTrace (prefixWord ++ tailWord_3490723) baseStart_3490723 baseEnd_3490723 := by
    simpa [prefixWord, tailWord_3490723, baseEnd_3490723] using wordTrace_append hprefix tailTrace_3490723
  have hstable : (prefixWord ++ tailWord_3490723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490723).length < 2 ^ (prefixWord ++ tailWord_3490723).sum := by decide
  have hdescent : baseEnd_3490723 < baseStart_3490723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490750 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_3490750 : Nat := 118140960795 + 3490750 * 2 ^ 59
def prefixEnd_3490750 : Nat := 4983230072969 + 3 ^ 40 * 3490750 * 2
def baseEnd_3490750 : Nat := 1792432594682322658271339

theorem tailTrace_3490750 : CollatzResearch.WordTrace tailWord_3490750 prefixEnd_3490750 1792432594682322658271339 := by
  unfold tailWord_3490750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914764012952049685172713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84878741402410931654254469 15914764012952049685172713)
  ·
    refine ⟨11936073009714037263879535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15914764012952049685172713 11936073009714037263879535)
    ·
      refine ⟨17904109514571055895819303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936073009714037263879535 17904109514571055895819303)
      ·
        refine ⟨26856164271856583843728955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17904109514571055895819303 26856164271856583843728955)
        ·
          refine ⟨40284246407784875765593433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26856164271856583843728955 40284246407784875765593433)
          ·
            refine ⟨30213184805838656824195075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40284246407784875765593433 30213184805838656824195075)
            ·
              refine ⟨45319777208757985236292613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30213184805838656824195075 45319777208757985236292613)
              ·
                refine ⟨8497458226642122231804865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45319777208757985236292613 8497458226642122231804865)
                ·
                  refine ⟨6373093669981591673853649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8497458226642122231804865 6373093669981591673853649)
                  ·
                    refine ⟨4779820252486193755390237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373093669981591673853649 4779820252486193755390237)
                    ·
                      refine ⟨1792432594682322658271339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779820252486193755390237 1792432594682322658271339)
                      ·
                        rfl

theorem cell23_3490750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_3490750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490750 prefixEnd_3490750 := by exact prefixLift 3490750
  have htrace : WordTrace (prefixWord ++ tailWord_3490750) baseStart_3490750 baseEnd_3490750 := by
    simpa [prefixWord, tailWord_3490750, baseEnd_3490750] using wordTrace_append hprefix tailTrace_3490750
  have hstable : (prefixWord ++ tailWord_3490750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490750).length < 2 ^ (prefixWord ++ tailWord_3490750).sum := by decide
  have hdescent : baseEnd_3490750 < baseStart_3490750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490770 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_3490770 : Nat := 118140960795 + 3490770 * 2 ^ 59
def prefixEnd_3490770 : Nat := 4983230072969 + 3 ^ 40 * 3490770 * 2
def baseEnd_3490770 : Nat := 199160318255045842224583

theorem tailTrace_3490770 : CollatzResearch.WordTrace tailWord_3490770 prefixEnd_3490770 199160318255045842224583 := by
  unfold tailWord_3490770
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829710390885985224277441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84879227709029293931406509 31829710390885985224277441)
  ·
    refine ⟨23872282793164488918208081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31829710390885985224277441 23872282793164488918208081)
    ·
      refine ⟨17904212094873366688656061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23872282793164488918208081 17904212094873366688656061)
      ·
        refine ⟨6714079535577512508246023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17904212094873366688656061 6714079535577512508246023)
        ·
          refine ⟨10071119303366268762369035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714079535577512508246023 10071119303366268762369035)
          ·
            refine ⟨15106678955049403143553553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071119303366268762369035 15106678955049403143553553)
            ·
              refine ⟨11330009216287052357665165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15106678955049403143553553 11330009216287052357665165)
              ·
                refine ⟨4248753456107644634124437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11330009216287052357665165 4248753456107644634124437)
                ·
                  refine ⟨199160318255045842224583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4248753456107644634124437 199160318255045842224583)
                  ·
                    rfl

theorem cell23_3490770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_3490770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490770 prefixEnd_3490770 := by exact prefixLift 3490770
  have htrace : WordTrace (prefixWord ++ tailWord_3490770) baseStart_3490770 baseEnd_3490770 := by
    simpa [prefixWord, tailWord_3490770, baseEnd_3490770] using wordTrace_append hprefix tailTrace_3490770
  have hstable : (prefixWord ++ tailWord_3490770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490770).length < 2 ^ (prefixWord ++ tailWord_3490770).sum := by decide
  have hdescent : baseEnd_3490770 < baseStart_3490770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490830 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3490830 : Nat := 118140960795 + 3490830 * 2 ^ 59
def prefixEnd_3490830 : Nat := 4983230072969 + 3 ^ 40 * 3490830 * 2
def baseEnd_3490830 : Nat := 597491224378227448423657

theorem tailTrace_3490830 : CollatzResearch.WordTrace tailWord_3490830 prefixEnd_3490830 597491224378227448423657 := by
  unfold tailWord_3490830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15915128742915821393036743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84880686628884380762862629 15915128742915821393036743)
  ·
    refine ⟨23872693114373732089555115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15915128742915821393036743 23872693114373732089555115)
    ·
      refine ⟨35809039671560598134332673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23872693114373732089555115 35809039671560598134332673)
      ·
        refine ⟨26856779753670448600749505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35809039671560598134332673 26856779753670448600749505)
        ·
          refine ⟨20142584815252836450562129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26856779753670448600749505 20142584815252836450562129)
          ·
            refine ⟨15106938611439627337921597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20142584815252836450562129 15106938611439627337921597)
            ·
              refine ⟨5665101979289860251720599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15106938611439627337921597 5665101979289860251720599)
              ·
                refine ⟨8497652968934790377580899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665101979289860251720599 8497652968934790377580899)
                ·
                  refine ⟨12746479453402185566371349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497652968934790377580899 12746479453402185566371349)
                  ·
                    refine ⟨597491224378227448423657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12746479453402185566371349 597491224378227448423657)
                    ·
                      rfl

theorem cell23_3490830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3490830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490830 prefixEnd_3490830 := by exact prefixLift 3490830
  have htrace : WordTrace (prefixWord ++ tailWord_3490830) baseStart_3490830 baseEnd_3490830 := by
    simpa [prefixWord, tailWord_3490830, baseEnd_3490830] using wordTrace_append hprefix tailTrace_3490830
  have hstable : (prefixWord ++ tailWord_3490830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490830).length < 2 ^ (prefixWord ++ tailWord_3490830).sum := by decide
  have hdescent : baseEnd_3490830 < baseStart_3490830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490837 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_3490837 : Nat := 118140960795 + 3490837 * 2 ^ 59
def prefixEnd_3490837 : Nat := 4983230072969 + 3 ^ 40 * 3490837 * 2
def baseEnd_3490837 : Nat := 1792477267499263817883439

theorem tailTrace_3490837 : CollatzResearch.WordTrace tailWord_3490837 prefixEnd_3490837 1792477267499263817883439 := by
  unfold tailWord_3490837
  simp only [CollatzResearch.WordTrace]
  refine ⟨127321285254301211339798765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84880856836200807559865843 127321285254301211339798765)
  ·
    refine ⟨47745481970362954252424537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127321285254301211339798765 47745481970362954252424537)
    ·
      refine ⟨35809111477772215689318403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47745481970362954252424537 35809111477772215689318403)
      ·
        refine ⟨53713667216658323533977605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35809111477772215689318403 53713667216658323533977605)
        ·
          refine ⟨10071312603123435662620801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53713667216658323533977605 10071312603123435662620801)
          ·
            refine ⟨7553484452342576746965601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10071312603123435662620801 7553484452342576746965601)
            ·
              refine ⟨5665113339256932560224201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7553484452342576746965601 5665113339256932560224201)
              ·
                refine ⟨4248835004442699420168151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665113339256932560224201 4248835004442699420168151)
                ·
                  refine ⟨6373252506664049130252227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248835004442699420168151 6373252506664049130252227)
                  ·
                    refine ⟨9559878759996073695378341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6373252506664049130252227 9559878759996073695378341)
                    ·
                      refine ⟨1792477267499263817883439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9559878759996073695378341 1792477267499263817883439)
                      ·
                        rfl

theorem cell23_3490837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_3490837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490837 prefixEnd_3490837 := by exact prefixLift 3490837
  have htrace : WordTrace (prefixWord ++ tailWord_3490837) baseStart_3490837 baseEnd_3490837 := by
    simpa [prefixWord, tailWord_3490837, baseEnd_3490837] using wordTrace_append hprefix tailTrace_3490837
  have hstable : (prefixWord ++ tailWord_3490837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490837).length < 2 ^ (prefixWord ++ tailWord_3490837).sum := by decide
  have hdescent : baseEnd_3490837 < baseStart_3490837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490848 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3490848 : Nat := 118140960795 + 3490848 * 2 ^ 59
def prefixEnd_3490848 : Nat := 4983230072969 + 3 ^ 40 * 3490848 * 2
def baseEnd_3490848 : Nat := 1792482915786463274845889

theorem tailTrace_3490848 : CollatzResearch.WordTrace tailWord_3490848 prefixEnd_3490848 1792482915786463274845889 := by
  unfold tailWord_3490848
  simp only [CollatzResearch.WordTrace]
  refine ⟨63660843228630680109224599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84881124304840906812299465 63660843228630680109224599)
  ·
    refine ⟨95491264842946020163836899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63660843228630680109224599 95491264842946020163836899)
    ·
      refine ⟨143236897264419030245755349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95491264842946020163836899 143236897264419030245755349)
      ·
        refine ⟨3357114779634821021384891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 143236897264419030245755349 3357114779634821021384891)
        ·
          refine ⟨5035672169452231532077337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357114779634821021384891 5035672169452231532077337)
          ·
            refine ⟨3776754127089173649058003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5035672169452231532077337 3776754127089173649058003)
            ·
              refine ⟨5665131190633760473587005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776754127089173649058003 5665131190633760473587005)
              ·
                refine ⟨2124424196487660177595127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5665131190633760473587005 2124424196487660177595127)
                ·
                  refine ⟨3186636294731490266392691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124424196487660177595127 3186636294731490266392691)
                  ·
                    refine ⟨4779954442097235399589037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3186636294731490266392691 4779954442097235399589037)
                    ·
                      refine ⟨1792482915786463274845889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4779954442097235399589037 1792482915786463274845889)
                      ·
                        rfl

theorem cell23_3490848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3490848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490848 prefixEnd_3490848 := by exact prefixLift 3490848
  have htrace : WordTrace (prefixWord ++ tailWord_3490848) baseStart_3490848 baseEnd_3490848 := by
    simpa [prefixWord, tailWord_3490848, baseEnd_3490848] using wordTrace_append hprefix tailTrace_3490848
  have hstable : (prefixWord ++ tailWord_3490848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490848).length < 2 ^ (prefixWord ++ tailWord_3490848).sum := by decide
  have hdescent : baseEnd_3490848 < baseStart_3490848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490881 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3490881 : Nat := 118140960795 + 3490881 * 2 ^ 59
def prefixEnd_3490881 : Nat := 4983230072969 + 3 ^ 40 * 3490881 * 2
def baseEnd_3490881 : Nat := 597499953549353881911079

theorem tailTrace_3490881 : CollatzResearch.WordTrace tailWord_3490881 prefixEnd_3490881 597499953549353881911079 := by
  unfold tailWord_3490881
  simp only [CollatzResearch.WordTrace]
  refine ⟨127322890066141806854400497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84881926710761204569600331 127322890066141806854400497)
  ·
    refine ⟨95492167549606355140800373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127322890066141806854400497 95492167549606355140800373)
    ·
      refine ⟨8952390707775595794450035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95492167549606355140800373 8952390707775595794450035)
      ·
        refine ⟨13428586061663393691675053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952390707775595794450035 13428586061663393691675053)
        ·
          refine ⟨5035719773123772634378145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13428586061663393691675053 5035719773123772634378145)
          ·
            refine ⟨3776789829842829475783609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5035719773123772634378145 3776789829842829475783609)
            ·
              refine ⟨2832592372382122106837707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3776789829842829475783609 2832592372382122106837707)
              ·
                refine ⟨4248888558573183160256561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832592372382122106837707 4248888558573183160256561)
                ·
                  refine ⟨3186666418929887370192421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248888558573183160256561 3186666418929887370192421)
                  ·
                    refine ⟨597499953549353881911079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186666418929887370192421 597499953549353881911079)
                    ·
                      rfl

theorem cell23_3490881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3490881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490881 prefixEnd_3490881 := by exact prefixLift 3490881
  have htrace : WordTrace (prefixWord ++ tailWord_3490881) baseStart_3490881 baseEnd_3490881 := by
    simpa [prefixWord, tailWord_3490881, baseEnd_3490881] using wordTrace_append hprefix tailTrace_3490881
  have hstable : (prefixWord ++ tailWord_3490881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490881).length < 2 ^ (prefixWord ++ tailWord_3490881).sum := by decide
  have hdescent : baseEnd_3490881 < baseStart_3490881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490903 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 4, 6]
def baseStart_3490903 : Nat := 118140960795 + 3490903 * 2 ^ 59
def prefixEnd_3490903 : Nat := 4983230072969 + 3 ^ 40 * 3490903 * 2
def baseEnd_3490903 : Nat := 597503719074153519886045

theorem tailTrace_3490903 : CollatzResearch.WordTrace tailWord_3490903 prefixEnd_3490903 597503719074153519886045 := by
  unfold tailWord_3490903
  simp only [CollatzResearch.WordTrace]
  refine ⟨127323692472062104611701363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84882461648041403074467575 127323692472062104611701363)
  ·
    refine ⟨190985538708093156917552045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127323692472062104611701363 190985538708093156917552045)
    ·
      refine ⟨71619577015534933844082017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190985538708093156917552045 71619577015534933844082017)
      ·
        refine ⟨53714682761651200383061513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71619577015534933844082017 53714682761651200383061513)
        ·
          refine ⟨40286012071238400287296135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53714682761651200383061513 40286012071238400287296135)
          ·
            refine ⟨60429018106857600430944203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40286012071238400287296135 60429018106857600430944203)
            ·
              refine ⟨90643527160286400646416305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60429018106857600430944203 90643527160286400646416305)
              ·
                refine ⟨67982645370214800484812229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90643527160286400646416305 67982645370214800484812229)
                ·
                  refine ⟨12746746006915275090902293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67982645370214800484812229 12746746006915275090902293)
                  ·
                    refine ⟨597503719074153519886045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12746746006915275090902293 597503719074153519886045)
                    ·
                      rfl

theorem cell23_3490903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_3490903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490903 prefixEnd_3490903 := by exact prefixLift 3490903
  have htrace : WordTrace (prefixWord ++ tailWord_3490903) baseStart_3490903 baseEnd_3490903 := by
    simpa [prefixWord, tailWord_3490903, baseEnd_3490903] using wordTrace_append hprefix tailTrace_3490903
  have hstable : (prefixWord ++ tailWord_3490903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490903).length < 2 ^ (prefixWord ++ tailWord_3490903).sum := by decide
  have hdescent : baseEnd_3490903 < baseStart_3490903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490923 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4]
def baseStart_3490923 : Nat := 118140960795 + 3490923 * 2 ^ 59
def prefixEnd_3490923 : Nat := 4983230072969 + 3 ^ 40 * 3490923 * 2
def baseEnd_3490923 : Nat := 1792521426835550481408043

theorem tailTrace_3490923 : CollatzResearch.WordTrace tailWord_3490923 prefixEnd_3490923 1792521426835550481408043 := by
  unfold tailWord_3490923
  simp only [CollatzResearch.WordTrace]
  refine ⟨127324421931989648027429423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84882947954659765351619615 127324421931989648027429423)
  ·
    refine ⟨190986632897984472041144135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127324421931989648027429423 190986632897984472041144135)
    ·
      refine ⟨286479949346976708061716203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190986632897984472041144135 286479949346976708061716203)
      ·
        refine ⟨429719924020465062092574305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286479949346976708061716203 429719924020465062092574305)
        ·
          refine ⟨322289943015348796569430729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429719924020465062092574305 322289943015348796569430729)
          ·
            refine ⟨241717457261511597427073047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322289943015348796569430729 241717457261511597427073047)
            ·
              refine ⟨362576185892267396140609571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241717457261511597427073047 362576185892267396140609571)
              ·
                refine ⟨543864278838401094210914357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362576185892267396140609571 543864278838401094210914357)
                ·
                  refine ⟨50987276141100102582273221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543864278838401094210914357 50987276141100102582273221)
                  ·
                    refine ⟨9560114276456269234176229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50987276141100102582273221 9560114276456269234176229)
                    ·
                      refine ⟨1792521426835550481408043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9560114276456269234176229 1792521426835550481408043)
                      ·
                        rfl

theorem cell23_3490923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_3490923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490923 prefixEnd_3490923 := by exact prefixLift 3490923
  have htrace : WordTrace (prefixWord ++ tailWord_3490923) baseStart_3490923 baseEnd_3490923 := by
    simpa [prefixWord, tailWord_3490923, baseEnd_3490923] using wordTrace_append hprefix tailTrace_3490923
  have hstable : (prefixWord ++ tailWord_3490923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490923).length < 2 ^ (prefixWord ++ tailWord_3490923).sum := by decide
  have hdescent : baseEnd_3490923 < baseStart_3490923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490930 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3490930 : Nat := 118140960795 + 3490930 * 2 ^ 59
def prefixEnd_3490930 : Nat := 4983230072969 + 3 ^ 40 * 3490930 * 2
def baseEnd_3490930 : Nat := 1792525021200131954020511

theorem tailTrace_3490930 : CollatzResearch.WordTrace tailWord_3490930 prefixEnd_3490930 1792525021200131954020511 := by
  unfold tailWord_3490930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31831169310741072055733561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84883118161976192148622829 31831169310741072055733561)
  ·
    refine ⟨23873376983055804041800171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31831169310741072055733561 23873376983055804041800171)
    ·
      refine ⟨35810065474583706062700257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23873376983055804041800171 35810065474583706062700257)
      ·
        refine ⟨26857549105937779547025193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35810065474583706062700257 26857549105937779547025193)
        ·
          refine ⟨20143161829453334660268895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26857549105937779547025193 20143161829453334660268895)
          ·
            refine ⟨30214742744180001990403343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20143161829453334660268895 30214742744180001990403343)
            ·
              refine ⟨45322114116270002985605015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30214742744180001990403343 45322114116270002985605015)
              ·
                refine ⟨67983171174405004478407523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45322114116270002985605015 67983171174405004478407523)
                ·
                  refine ⟨101974756761607506717611285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67983171174405004478407523 101974756761607506717611285)
                  ·
                    refine ⟨4780066723200351877388029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101974756761607506717611285 4780066723200351877388029)
                    ·
                      refine ⟨1792525021200131954020511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4780066723200351877388029 1792525021200131954020511)
                      ·
                        rfl

theorem cell23_3490930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3490930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490930 prefixEnd_3490930 := by exact prefixLift 3490930
  have htrace : WordTrace (prefixWord ++ tailWord_3490930) baseStart_3490930 baseEnd_3490930 := by
    simpa [prefixWord, tailWord_3490930, baseEnd_3490930] using wordTrace_append hprefix tailTrace_3490930
  have hstable : (prefixWord ++ tailWord_3490930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490930).length < 2 ^ (prefixWord ++ tailWord_3490930).sum := by decide
  have hdescent : baseEnd_3490930 < baseStart_3490930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490940 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3490940 : Nat := 118140960795 + 3490940 * 2 ^ 59
def prefixEnd_3490940 : Nat := 4983230072969 + 3 ^ 40 * 3490940 * 2
def baseEnd_3490940 : Nat := 1792530156006676914895465

theorem tailTrace_3490940 : CollatzResearch.WordTrace tailWord_3490940 prefixEnd_3490940 1792530156006676914895465 := by
  unfold tailWord_3490940
  simp only [CollatzResearch.WordTrace]
  refine ⟨63662520986464029965399137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84883361315285373287198849 63662520986464029965399137)
  ·
    refine ⟨47746890739848022474049353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63662520986464029965399137 47746890739848022474049353)
    ·
      refine ⟨35810168054886016855537015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47746890739848022474049353 35810168054886016855537015)
      ·
        refine ⟨53715252082329025283305523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35810168054886016855537015 53715252082329025283305523)
        ·
          refine ⟨80572878123493537924958285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53715252082329025283305523 80572878123493537924958285)
          ·
            refine ⟨30214829296310076721859357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80572878123493537924958285 30214829296310076721859357)
            ·
              refine ⟨11330560986116278770697259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30214829296310076721859357 11330560986116278770697259)
              ·
                refine ⟨16995841479174418156045889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330560986116278770697259 16995841479174418156045889)
                ·
                  refine ⟨12746881109380813617034417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16995841479174418156045889 12746881109380813617034417)
                  ·
                    refine ⟨9560160832035610212775813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12746881109380813617034417 9560160832035610212775813)
                    ·
                      refine ⟨1792530156006676914895465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9560160832035610212775813 1792530156006676914895465)
                      ·
                        rfl

theorem cell23_3490940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3490940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490940 prefixEnd_3490940 := by exact prefixLift 3490940
  have htrace : WordTrace (prefixWord ++ tailWord_3490940) baseStart_3490940 baseEnd_3490940 := by
    simpa [prefixWord, tailWord_3490940, baseEnd_3490940] using wordTrace_append hprefix tailTrace_3490940
  have hstable : (prefixWord ++ tailWord_3490940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490940).length < 2 ^ (prefixWord ++ tailWord_3490940).sum := by decide
  have hdescent : baseEnd_3490940 < baseStart_3490940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490944 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 2, 2, 2]
def baseStart_3490944 : Nat := 118140960795 + 3490944 * 2 ^ 59
def prefixEnd_3490944 : Nat := 4983230072969 + 3 ^ 40 * 3490944 * 2
def baseEnd_3490944 : Nat := 1792532209929294899245447

theorem tailTrace_3490944 : CollatzResearch.WordTrace tailWord_3490944 prefixEnd_3490944 1792532209929294899245447 := by
  unfold tailWord_3490944
  simp only [CollatzResearch.WordTrace]
  refine ⟨63662593932456784306971943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84883458576609045742629257 63662593932456784306971943)
  ·
    refine ⟨95493890898685176460457915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63662593932456784306971943 95493890898685176460457915)
    ·
      refine ⟨143240836348027764690686873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95493890898685176460457915 143240836348027764690686873)
      ·
        refine ⟨107430627261020823518015155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143240836348027764690686873 107430627261020823518015155)
        ·
          refine ⟨161145940891531235277022733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107430627261020823518015155 161145940891531235277022733)
          ·
            refine ⟨60429727834324213228883525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161145940891531235277022733 60429727834324213228883525)
            ·
              refine ⟨11330573968935789980415661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60429727834324213228883525 11330573968935789980415661)
              ·
                refine ⟨4248965238350921242655873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11330573968935789980415661 4248965238350921242655873)
                ·
                  refine ⟨3186723928763190931991905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248965238350921242655873 3186723928763190931991905)
                  ·
                    refine ⟨2390042946572393198993929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3186723928763190931991905 2390042946572393198993929)
                    ·
                      refine ⟨1792532209929294899245447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2390042946572393198993929 1792532209929294899245447)
                      ·
                        rfl

theorem cell23_3490944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_3490944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490944 prefixEnd_3490944 := by exact prefixLift 3490944
  have htrace : WordTrace (prefixWord ++ tailWord_3490944) baseStart_3490944 baseEnd_3490944 := by
    simpa [prefixWord, tailWord_3490944, baseEnd_3490944] using wordTrace_append hprefix tailTrace_3490944
  have hstable : (prefixWord ++ tailWord_3490944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490944).length < 2 ^ (prefixWord ++ tailWord_3490944).sum := by decide
  have hdescent : baseEnd_3490944 < baseStart_3490944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3490967 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 5]
def baseStart_3490967 : Nat := 118140960795 + 3490967 * 2 ^ 59
def prefixEnd_3490967 : Nat := 4983230072969 + 3 ^ 40 * 3490967 * 2
def baseEnd_3490967 : Nat := 199171557776038701028649

theorem tailTrace_3490967 : CollatzResearch.WordTrace tailWord_3490967 prefixEnd_3490967 199171557776038701028649 := by
  unfold tailWord_3490967
  simp only [CollatzResearch.WordTrace]
  refine ⟨127326026743830243542031155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84884017829220162361354103 127326026743830243542031155)
  ·
    refine ⟨190989040115745365313046733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127326026743830243542031155 190989040115745365313046733)
    ·
      refine ⟨71620890043404511992392525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190989040115745365313046733 71620890043404511992392525)
      ·
        refine ⟨26857833766276691997147197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71620890043404511992392525 26857833766276691997147197)
        ·
          refine ⟨10071687662353759498930199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26857833766276691997147197 10071687662353759498930199)
          ·
            refine ⟨15107531493530639248395299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071687662353759498930199 15107531493530639248395299)
            ·
              refine ⟨22661297240295958872592949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15107531493530639248395299 22661297240295958872592949)
              ·
                refine ⟨2124496616277746144305589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22661297240295958872592949 2124496616277746144305589)
                ·
                  refine ⟨199171557776038701028649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2124496616277746144305589 199171557776038701028649)
                  ·
                    rfl

theorem cell23_3490967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 5].length) (baseStart_3490967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3490967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3490967 prefixEnd_3490967 := by exact prefixLift 3490967
  have htrace : WordTrace (prefixWord ++ tailWord_3490967) baseStart_3490967 baseEnd_3490967 := by
    simpa [prefixWord, tailWord_3490967, baseEnd_3490967] using wordTrace_append hprefix tailTrace_3490967
  have hstable : (prefixWord ++ tailWord_3490967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3490967).length < 2 ^ (prefixWord ++ tailWord_3490967).sum := by decide
  have hdescent : baseEnd_3490967 < baseStart_3490967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3490967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491000 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_3491000 : Nat := 118140960795 + 3491000 * 2 ^ 59
def prefixEnd_3491000 : Nat := 4983230072969 + 3 ^ 40 * 3491000 * 2
def baseEnd_3491000 : Nat := 1792560964845946680145189

theorem tailTrace_3491000 : CollatzResearch.WordTrace tailWord_3491000 prefixEnd_3491000 1792560964845946680145189 := by
  unfold tailWord_3491000
  simp only [CollatzResearch.WordTrace]
  refine ⟨63663615176355345088991227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84884820235140460118654969 63663615176355345088991227)
  ·
    refine ⟨95495422764533017633486841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63663615176355345088991227 95495422764533017633486841)
    ·
      refine ⟨71621567073399763225115131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95495422764533017633486841 71621567073399763225115131)
      ·
        refine ⟨107432350610099644837672697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71621567073399763225115131 107432350610099644837672697)
        ·
          refine ⟨80574262957574733628254523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107432350610099644837672697 80574262957574733628254523)
          ·
            refine ⟨120861394436362100442381785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80574262957574733628254523 120861394436362100442381785)
            ·
              refine ⟨90646045827271575331786339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120861394436362100442381785 90646045827271575331786339)
              ·
                refine ⟨135969068740907362997679509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90646045827271575331786339 135969068740907362997679509)
                ·
                  refine ⟨6373550097230032640516227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135969068740907362997679509 6373550097230032640516227)
                  ·
                    refine ⟨9560325145845048960774341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6373550097230032640516227 9560325145845048960774341)
                    ·
                      refine ⟨1792560964845946680145189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9560325145845048960774341 1792560964845946680145189)
                      ·
                        rfl

theorem cell23_3491000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_3491000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491000 prefixEnd_3491000 := by exact prefixLift 3491000
  have htrace : WordTrace (prefixWord ++ tailWord_3491000) baseStart_3491000 baseEnd_3491000 := by
    simpa [prefixWord, tailWord_3491000, baseEnd_3491000] using wordTrace_append hprefix tailTrace_3491000
  have hstable : (prefixWord ++ tailWord_3491000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491000).length < 2 ^ (prefixWord ++ tailWord_3491000).sum := by decide
  have hdescent : baseEnd_3491000 < baseStart_3491000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491040 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 8]
def baseStart_3491040 : Nat := 118140960795 + 3491040 * 2 ^ 59
def prefixEnd_3491040 : Nat := 4983230072969 + 3 ^ 40 * 3491040 * 2
def baseEnd_3491040 : Nat := 199175722674680724849445

theorem tailTrace_3491040 : CollatzResearch.WordTrace tailWord_3491040 prefixEnd_3491040 199175722674680724849445 := by
  unfold tailWord_3491040
  simp only [CollatzResearch.WordTrace]
  refine ⟨63664344636282888504719287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84885792848377184672959049 63664344636282888504719287)
  ·
    refine ⟨95496516954424332757078931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63664344636282888504719287 95496516954424332757078931)
    ·
      refine ⟨143244775431636499135618397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95496516954424332757078931 143244775431636499135618397)
      ·
        refine ⟨53716790786863687175856899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143244775431636499135618397 53716790786863687175856899)
        ·
          refine ⟨80575186180295530763785349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53716790786863687175856899 80575186180295530763785349)
          ·
            refine ⟨15107847408805412018209753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80575186180295530763785349 15107847408805412018209753)
            ·
              refine ⟨11330885556604059013657315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15107847408805412018209753 11330885556604059013657315)
              ·
                refine ⟨16996328334906088520485973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330885556604059013657315 16996328334906088520485973)
                ·
                  refine ⟨199175722674680724849445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16996328334906088520485973 199175722674680724849445)
                  ·
                    rfl

theorem cell23_3491040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_3491040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491040 prefixEnd_3491040 := by exact prefixLift 3491040
  have htrace : WordTrace (prefixWord ++ tailWord_3491040) baseStart_3491040 baseEnd_3491040 := by
    simpa [prefixWord, tailWord_3491040, baseEnd_3491040] using wordTrace_append hprefix tailTrace_3491040
  have hstable : (prefixWord ++ tailWord_3491040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491040).length < 2 ^ (prefixWord ++ tailWord_3491040).sum := by decide
  have hdescent : baseEnd_3491040 < baseStart_3491040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491044 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_3491044 : Nat := 118140960795 + 3491044 * 2 ^ 59
def prefixEnd_3491044 : Nat := 4983230072969 + 3 ^ 40 * 3491044 * 2
def baseEnd_3491044 : Nat := 597527852664914835998329

theorem tailTrace_3491044 : CollatzResearch.WordTrace tailWord_3491044 prefixEnd_3491044 597527852664914835998329 := by
  unfold tailWord_3491044
  simp only [CollatzResearch.WordTrace]
  refine ⟨63664417582275642846292093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84885890109700857128389457 63664417582275642846292093)
  ·
    refine ⟨23874156593353366067359535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63664417582275642846292093 23874156593353366067359535)
    ·
      refine ⟨35811234890030049101039303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23874156593353366067359535 35811234890030049101039303)
      ·
        refine ⟨53716852335045073651558955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35811234890030049101039303 53716852335045073651558955)
        ·
          refine ⟨80575278502567610477338433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53716852335045073651558955 80575278502567610477338433)
          ·
            refine ⟨60431458876925707858003825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80575278502567610477338433 60431458876925707858003825)
            ·
              refine ⟨45323594157694280893502869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60431458876925707858003825 45323594157694280893502869)
              ·
                refine ⟨2124543476141919416882947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45323594157694280893502869 2124543476141919416882947)
                ·
                  refine ⟨3186815214212879125324421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124543476141919416882947 3186815214212879125324421)
                  ·
                    refine ⟨597527852664914835998329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186815214212879125324421 597527852664914835998329)
                    ·
                      rfl

theorem cell23_3491044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_3491044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491044 prefixEnd_3491044 := by exact prefixLift 3491044
  have htrace : WordTrace (prefixWord ++ tailWord_3491044) baseStart_3491044 baseEnd_3491044 := by
    simpa [prefixWord, tailWord_3491044, baseEnd_3491044] using wordTrace_append hprefix tailTrace_3491044
  have hstable : (prefixWord ++ tailWord_3491044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491044).length < 2 ^ (prefixWord ++ tailWord_3491044).sum := by decide
  have hdescent : baseEnd_3491044 < baseStart_3491044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491107 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 4]
def baseStart_3491107 : Nat := 118140960795 + 3491107 * 2 ^ 59
def prefixEnd_3491107 : Nat := 4983230072969 + 3 ^ 40 * 3491107 * 2
def baseEnd_3491107 : Nat := 1792615907275977761507197

theorem tailTrace_3491107 : CollatzResearch.WordTrace tailWord_3491107 prefixEnd_3491107 1792615907275977761507197 := by
  unfold tailWord_3491107
  simp only [CollatzResearch.WordTrace]
  refine ⟨127331132963323047452127575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84887421975548698301418383 127331132963323047452127575)
  ·
    refine ⟨190996699444984571178191363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127331132963323047452127575 190996699444984571178191363)
    ·
      refine ⟨286495049167476856767287045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190996699444984571178191363 286495049167476856767287045)
      ·
        refine ⟨53717821718901910643866321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286495049167476856767287045 53717821718901910643866321)
        ·
          refine ⟨40288366289176432982899741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53717821718901910643866321 40288366289176432982899741)
          ·
            refine ⟨15108137358441162368587403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40288366289176432982899741 15108137358441162368587403)
            ·
              refine ⟨22662206037661743552881105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108137358441162368587403 22662206037661743552881105)
              ·
                refine ⟨16996654528246307664660829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22662206037661743552881105 16996654528246307664660829)
                ·
                  refine ⟨6373745448092365374247811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16996654528246307664660829 6373745448092365374247811)
                  ·
                    refine ⟨9560618172138548061371717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6373745448092365374247811 9560618172138548061371717)
                    ·
                      refine ⟨1792615907275977761507197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9560618172138548061371717 1792615907275977761507197)
                      ·
                        rfl

theorem cell23_3491107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_3491107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491107 prefixEnd_3491107 := by exact prefixLift 3491107
  have htrace : WordTrace (prefixWord ++ tailWord_3491107) baseStart_3491107 baseEnd_3491107 := by
    simpa [prefixWord, tailWord_3491107, baseEnd_3491107] using wordTrace_append hprefix tailTrace_3491107
  have hstable : (prefixWord ++ tailWord_3491107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491107).length < 2 ^ (prefixWord ++ tailWord_3491107).sum := by decide
  have hdescent : baseEnd_3491107 < baseStart_3491107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491124 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3491124 : Nat := 118140960795 + 3491124 * 2 ^ 59
def prefixEnd_3491124 : Nat := 4983230072969 + 3 ^ 40 * 3491124 * 2
def baseEnd_3491124 : Nat := 1792624636447104194994619

theorem tailTrace_3491124 : CollatzResearch.WordTrace tailWord_3491124 prefixEnd_3491124 1792624636447104194994619 := by
  unfold tailWord_3491124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63665876502130729677748213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84887835336174306236997617 63665876502130729677748213)
  ·
    refine ⟨5968675922074755907288895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63665876502130729677748213 5968675922074755907288895)
    ·
      refine ⟨8953013883112133860933343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968675922074755907288895 8953013883112133860933343)
      ·
        refine ⟨13429520824668200791400015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953013883112133860933343 13429520824668200791400015)
        ·
          refine ⟨20144281237002301187100023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429520824668200791400015 20144281237002301187100023)
          ·
            refine ⟨30216421855503451780650035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20144281237002301187100023 30216421855503451780650035)
            ·
              refine ⟨45324632783255177670975053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30216421855503451780650035 45324632783255177670975053)
              ·
                refine ⟨16996737293720691626615645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45324632783255177670975053 16996737293720691626615645)
                ·
                  refine ⟨6373776485145259359980867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16996737293720691626615645 6373776485145259359980867)
                  ·
                    refine ⟨9560664727717889039971301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6373776485145259359980867 9560664727717889039971301)
                    ·
                      refine ⟨1792624636447104194994619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9560664727717889039971301 1792624636447104194994619)
                      ·
                        rfl

theorem cell23_3491124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3491124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491124 prefixEnd_3491124 := by exact prefixLift 3491124
  have htrace : WordTrace (prefixWord ++ tailWord_3491124) baseStart_3491124 baseEnd_3491124 := by
    simpa [prefixWord, tailWord_3491124, baseEnd_3491124] using wordTrace_append hprefix tailTrace_3491124
  have hstable : (prefixWord ++ tailWord_3491124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491124).length < 2 ^ (prefixWord ++ tailWord_3491124).sum := by decide
  have hdescent : baseEnd_3491124 < baseStart_3491124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491134 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3491134 : Nat := 118140960795 + 3491134 * 2 ^ 59
def prefixEnd_3491134 : Nat := 4983230072969 + 3 ^ 40 * 3491134 * 2
def baseEnd_3491134 : Nat := 597543257084549718623191

theorem tailTrace_3491134 : CollatzResearch.WordTrace tailWord_3491134 prefixEnd_3491134 597543257084549718623191 := by
  unfold tailWord_3491134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916514716778153882920057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84888078489483487375573637 15916514716778153882920057)
  ·
    refine ⟨11937386037583615412190043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15916514716778153882920057 11937386037583615412190043)
    ·
      refine ⟨17906079056375423118285065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11937386037583615412190043 17906079056375423118285065)
      ·
        refine ⟨13429559292281567338713799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17906079056375423118285065 13429559292281567338713799)
        ·
          refine ⟨20144338938422351008070699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429559292281567338713799 20144338938422351008070699)
          ·
            refine ⟨30216508407633526512106049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20144338938422351008070699 30216508407633526512106049)
            ·
              refine ⟨22662381305725144884079537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30216508407633526512106049 22662381305725144884079537)
              ·
                refine ⟨16996785979293858663059653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22662381305725144884079537 16996785979293858663059653)
                ·
                  refine ⟨3186897371117598499323685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16996785979293858663059653 3186897371117598499323685)
                  ·
                    refine ⟨597543257084549718623191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186897371117598499323685 597543257084549718623191)
                    ·
                      rfl

theorem cell23_3491134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3491134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491134 prefixEnd_3491134 := by exact prefixLift 3491134
  have htrace : WordTrace (prefixWord ++ tailWord_3491134) baseStart_3491134 baseEnd_3491134 := by
    simpa [prefixWord, tailWord_3491134, baseEnd_3491134] using wordTrace_append hprefix tailTrace_3491134
  have hstable : (prefixWord ++ tailWord_3491134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491134).length < 2 ^ (prefixWord ++ tailWord_3491134).sum := by decide
  have hdescent : baseEnd_3491134 < baseStart_3491134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491178 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3491178 : Nat := 118140960795 + 3491178 * 2 ^ 59
def prefixEnd_3491178 : Nat := 4983230072969 + 3 ^ 40 * 3491178 * 2
def baseEnd_3491178 : Nat := 1792652364402446983719371

theorem tailTrace_3491178 : CollatzResearch.WordTrace tailWord_3491178 prefixEnd_3491178 1792652364402446983719371 := by
  unfold tailWord_3491178
  simp only [CollatzResearch.WordTrace]
  refine ⟨31833430636516456644490547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84889148364043884385308125 31833430636516456644490547)
  ·
    refine ⟨47750145954774684966735821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31833430636516456644490547 47750145954774684966735821)
    ·
      refine ⟨17906304733040506862525933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47750145954774684966735821 17906304733040506862525933)
      ·
        refine ⟨6714864274890190073447225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17906304733040506862525933 6714864274890190073447225)
        ·
          refine ⟨5036148206167642555085419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6714864274890190073447225 5036148206167642555085419)
          ·
            refine ⟨7554222309251463832628129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036148206167642555085419 7554222309251463832628129)
            ·
              refine ⟨5665666731938597874471097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7554222309251463832628129 5665666731938597874471097)
              ·
                refine ⟨4249250048953948405853323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665666731938597874471097 4249250048953948405853323)
                ·
                  refine ⟨6373875073430922608779985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249250048953948405853323 6373875073430922608779985)
                  ·
                    refine ⟨4780406305073191956584989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373875073430922608779985 4780406305073191956584989)
                    ·
                      refine ⟨1792652364402446983719371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4780406305073191956584989 1792652364402446983719371)
                      ·
                        rfl

theorem cell23_3491178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3491178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491178 prefixEnd_3491178 := by exact prefixLift 3491178
  have htrace : WordTrace (prefixWord ++ tailWord_3491178) baseStart_3491178 baseEnd_3491178 := by
    simpa [prefixWord, tailWord_3491178, baseEnd_3491178] using wordTrace_append hprefix tailTrace_3491178
  have hstable : (prefixWord ++ tailWord_3491178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491178).length < 2 ^ (prefixWord ++ tailWord_3491178).sum := by decide
  have hdescent : baseEnd_3491178 < baseStart_3491178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491198 : List Nat := [4, 2, 3, 2, 2, 1, 9]
def baseStart_3491198 : Nat := 118140960795 + 3491198 * 2 ^ 59
def prefixEnd_3491198 : Nat := 4983230072969 + 3 ^ 40 * 3491198 * 2
def baseEnd_3491198 : Nat := 22131637456981937104559

theorem tailTrace_3491198 : CollatzResearch.WordTrace tailWord_3491198 prefixEnd_3491198 22131637456981937104559 := by
  unfold tailWord_3491198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916806500749171249211281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84889634670662246662460165 15916806500749171249211281)
  ·
    refine ⟨11937604875561878436908461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15916806500749171249211281 11937604875561878436908461)
    ·
      refine ⟨4476601828335704413840673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11937604875561878436908461 4476601828335704413840673)
      ·
        refine ⟨3357451371251778310380505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4476601828335704413840673 3357451371251778310380505)
        ·
          refine ⟨2518088528438833732785379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3357451371251778310380505 2518088528438833732785379)
          ·
            refine ⟨3777132792658250599178069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518088528438833732785379 3777132792658250599178069)
            ·
              refine ⟨22131637456981937104559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3777132792658250599178069 22131637456981937104559)
              ·
                rfl

theorem cell23_3491198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 9].length) (baseStart_3491198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491198 prefixEnd_3491198 := by exact prefixLift 3491198
  have htrace : WordTrace (prefixWord ++ tailWord_3491198) baseStart_3491198 baseEnd_3491198 := by
    simpa [prefixWord, tailWord_3491198, baseEnd_3491198] using wordTrace_append hprefix tailTrace_3491198
  have hstable : (prefixWord ++ tailWord_3491198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491198).length < 2 ^ (prefixWord ++ tailWord_3491198).sum := by decide
  have hdescent : baseEnd_3491198 < baseStart_3491198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491217 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_3491217 : Nat := 118140960795 + 3491217 * 2 ^ 59
def prefixEnd_3491217 : Nat := 4983230072969 + 3 ^ 40 * 3491217 * 2
def baseEnd_3491217 : Nat := 1792672390147972331131691

theorem tailTrace_3491217 : CollatzResearch.WordTrace tailWord_3491217 prefixEnd_3491217 1792672390147972331131691 := by
  unfold tailWord_3491217
  simp only [CollatzResearch.WordTrace]
  refine ⟨127335144992924536238631905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84890096661949690825754603 127335144992924536238631905)
  ·
    refine ⟨95501358744693402178973929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127335144992924536238631905 95501358744693402178973929)
    ·
      refine ⟨71626019058520051634230447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95501358744693402178973929 71626019058520051634230447)
      ·
        refine ⟨107439028587780077451345671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71626019058520051634230447 107439028587780077451345671)
        ·
          refine ⟨161158542881670116177018507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107439028587780077451345671 161158542881670116177018507)
          ·
            refine ⟨241737814322505174265527761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161158542881670116177018507 241737814322505174265527761)
            ·
              refine ⟨181303360741878880699145821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241737814322505174265527761 181303360741878880699145821)
              ·
                refine ⟨67988760278204580262179683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181303360741878880699145821 67988760278204580262179683)
                ·
                  refine ⟨101983140417306870393269525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67988760278204580262179683 101983140417306870393269525)
                  ·
                    refine ⟨4780459707061259549684509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101983140417306870393269525 4780459707061259549684509)
                    ·
                      refine ⟨1792672390147972331131691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4780459707061259549684509 1792672390147972331131691)
                      ·
                        rfl

theorem cell23_3491217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_3491217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491217 prefixEnd_3491217 := by exact prefixLift 3491217
  have htrace : WordTrace (prefixWord ++ tailWord_3491217) baseStart_3491217 baseEnd_3491217 := by
    simpa [prefixWord, tailWord_3491217, baseEnd_3491217] using wordTrace_append hprefix tailTrace_3491217
  have hstable : (prefixWord ++ tailWord_3491217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491217).length < 2 ^ (prefixWord ++ tailWord_3491217).sum := by decide
  have hdescent : baseEnd_3491217 < baseStart_3491217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491234 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3491234 : Nat := 118140960795 + 3491234 * 2 ^ 59
def prefixEnd_3491234 : Nat := 4983230072969 + 3 ^ 40 * 3491234 * 2
def baseEnd_3491234 : Nat := 1792681119319098764619113

theorem tailTrace_3491234 : CollatzResearch.WordTrace tailWord_3491234 prefixEnd_3491234 1792681119319098764619113 := by
  unfold tailWord_3491234
  simp only [CollatzResearch.WordTrace]
  refine ⟨31833941258465737035500189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84890510022575298761333837 31833941258465737035500189)
  ·
    refine ⟨11937727971924651388312571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31833941258465737035500189 11937727971924651388312571)
    ·
      refine ⟨17906591957886977082468857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11937727971924651388312571 17906591957886977082468857)
      ·
        refine ⟨13429943968415232811851643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17906591957886977082468857 13429943968415232811851643)
        ·
          refine ⟨20144915952622849217777465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429943968415232811851643 20144915952622849217777465)
          ·
            refine ⟨15108686964467136913333099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20144915952622849217777465 15108686964467136913333099)
            ·
              refine ⟨22663030446700705369999649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108686964467136913333099 22663030446700705369999649)
              ·
                refine ⟨16997272835025529027499737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22663030446700705369999649 16997272835025529027499737)
                ·
                  refine ⟨12747954626269146770624803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16997272835025529027499737 12747954626269146770624803)
                  ·
                    refine ⟨19121931939403720155937205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12747954626269146770624803 19121931939403720155937205)
                    ·
                      refine ⟨1792681119319098764619113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19121931939403720155937205 1792681119319098764619113)
                      ·
                        rfl

theorem cell23_3491234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3491234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491234 prefixEnd_3491234 := by exact prefixLift 3491234
  have htrace : WordTrace (prefixWord ++ tailWord_3491234) baseStart_3491234 baseEnd_3491234 := by
    simpa [prefixWord, tailWord_3491234, baseEnd_3491234] using wordTrace_append hprefix tailTrace_3491234
  have hstable : (prefixWord ++ tailWord_3491234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491234).length < 2 ^ (prefixWord ++ tailWord_3491234).sum := by decide
  have hdescent : baseEnd_3491234 < baseStart_3491234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491301 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_3491301 : Nat := 118140960795 + 3491301 * 2 ^ 59
def prefixEnd_3491301 : Nat := 4983230072969 + 3 ^ 40 * 3491301 * 2
def baseEnd_3491301 : Nat := 597571840840983334160435

theorem tailTrace_3491301 : CollatzResearch.WordTrace tailWord_3491301 prefixEnd_3491301 597571840840983334160435 := by
  unfold tailWord_3491301
  simp only [CollatzResearch.WordTrace]
  refine ⟨127338208724620218584689757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84892139149746812389793171 127338208724620218584689757)
  ·
    refine ⟨47751828271732581969258659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127338208724620218584689757 47751828271732581969258659)
    ·
      refine ⟨71627742407598872953887989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47751828271732581969258659 71627742407598872953887989)
      ·
        refine ⟨6715100850712394339426999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71627742407598872953887989 6715100850712394339426999)
        ·
          refine ⟨10072651276068591509140499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715100850712394339426999 10072651276068591509140499)
          ·
            refine ⟨15108976914102887263710749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072651276068591509140499 15108976914102887263710749)
            ·
              refine ⟨5665866342788582723891531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15108976914102887263710749 5665866342788582723891531)
              ·
                refine ⟨8498799514182874085837297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665866342788582723891531 8498799514182874085837297)
                ·
                  refine ⟨6374099635637155564377973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8498799514182874085837297 6374099635637155564377973)
                  ·
                    refine ⟨597571840840983334160435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6374099635637155564377973 597571840840983334160435)
                    ·
                      rfl

theorem cell23_3491301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_3491301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491301 prefixEnd_3491301 := by exact prefixLift 3491301
  have htrace : WordTrace (prefixWord ++ tailWord_3491301) baseStart_3491301 baseEnd_3491301 := by
    simpa [prefixWord, tailWord_3491301, baseEnd_3491301] using wordTrace_append hprefix tailTrace_3491301
  have hstable : (prefixWord ++ tailWord_3491301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491301).length < 2 ^ (prefixWord ++ tailWord_3491301).sum := by decide
  have hdescent : baseEnd_3491301 < baseStart_3491301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491304 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3491304 : Nat := 118140960795 + 3491304 * 2 ^ 59
def prefixEnd_3491304 : Nat := 4983230072969 + 3 ^ 40 * 3491304 * 2
def baseEnd_3491304 : Nat := 1792717062964913490743791

theorem tailTrace_3491304 : CollatzResearch.WordTrace tailWord_3491304 prefixEnd_3491304 1792717062964913490743791 := by
  unfold tailWord_3491304
  simp only [CollatzResearch.WordTrace]
  refine ⟨63669159071804675048524483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84892212095739566731365977 63669159071804675048524483)
  ·
    refine ⟨95503738607707012572786725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63669159071804675048524483 95503738607707012572786725)
    ·
      refine ⟨17906950988945064857397511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95503738607707012572786725 17906950988945064857397511)
      ·
        refine ⟨26860426483417597286096267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17906950988945064857397511 26860426483417597286096267)
        ·
          refine ⟨40290639725126395929144401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26860426483417597286096267 40290639725126395929144401)
          ·
            refine ⟨30217979793844796946858301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40290639725126395929144401 30217979793844796946858301)
            ·
              refine ⟨11331742422691798855071863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30217979793844796946858301 11331742422691798855071863)
              ·
                refine ⟨16997613634037698282607795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11331742422691798855071863 16997613634037698282607795)
                ·
                  refine ⟨25496420451056547423911693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16997613634037698282607795 25496420451056547423911693)
                  ·
                    refine ⟨9561157669146205283966885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25496420451056547423911693 9561157669146205283966885)
                    ·
                      refine ⟨1792717062964913490743791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9561157669146205283966885 1792717062964913490743791)
                      ·
                        rfl

theorem cell23_3491304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3491304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491304 prefixEnd_3491304 := by exact prefixLift 3491304
  have htrace : WordTrace (prefixWord ++ tailWord_3491304) baseStart_3491304 baseEnd_3491304 := by
    simpa [prefixWord, tailWord_3491304, baseEnd_3491304] using wordTrace_append hprefix tailTrace_3491304
  have hstable : (prefixWord ++ tailWord_3491304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491304).length < 2 ^ (prefixWord ++ tailWord_3491304).sum := by decide
  have hdescent : baseEnd_3491304 < baseStart_3491304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491307 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_3491307 : Nat := 118140960795 + 3491307 * 2 ^ 59
def prefixEnd_3491307 : Nat := 4983230072969 + 3 ^ 40 * 3491307 * 2
def baseEnd_3491307 : Nat := 1792718603406876979006277

theorem tailTrace_3491307 : CollatzResearch.WordTrace tailWord_3491307 prefixEnd_3491307 1792718603406876979006277 := by
  unfold tailWord_3491307
  simp only [CollatzResearch.WordTrace]
  refine ⟨127338427562598481609408175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84892285041732321072938783 127338427562598481609408175)
  ·
    refine ⟨191007641343897722414112263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127338427562598481609408175 191007641343897722414112263)
    ·
      refine ⟨286511462015846583621168395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191007641343897722414112263 286511462015846583621168395)
      ·
        refine ⟨429767193023769875431752593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286511462015846583621168395 429767193023769875431752593)
        ·
          refine ⟨322325394767827406573814445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429767193023769875431752593 322325394767827406573814445)
          ·
            refine ⟨120872023037935277465180417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322325394767827406573814445 120872023037935277465180417)
            ·
              refine ⟨90654017278451458098885313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120872023037935277465180417 90654017278451458098885313)
              ·
                refine ⟨67990512958838593574163985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90654017278451458098885313 67990512958838593574163985)
                ·
                  refine ⟨50992884719128945180622989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67990512958838593574163985 50992884719128945180622989)
                  ·
                    refine ⟨19122331769673354442733621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50992884719128945180622989 19122331769673354442733621)
                    ·
                      refine ⟨1792718603406876979006277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19122331769673354442733621 1792718603406876979006277)
                      ·
                        rfl

theorem cell23_3491307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_3491307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491307 prefixEnd_3491307 := by exact prefixLift 3491307
  have htrace : WordTrace (prefixWord ++ tailWord_3491307) baseStart_3491307 baseEnd_3491307 := by
    simpa [prefixWord, tailWord_3491307, baseEnd_3491307] using wordTrace_append hprefix tailTrace_3491307
  have hstable : (prefixWord ++ tailWord_3491307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491307).length < 2 ^ (prefixWord ++ tailWord_3491307).sum := by decide
  have hdescent : baseEnd_3491307 < baseStart_3491307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491354 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_3491354 : Nat := 118140960795 + 3491354 * 2 ^ 59
def prefixEnd_3491354 : Nat := 4983230072969 + 3 ^ 40 * 3491354 * 2
def baseEnd_3491354 : Nat := 1792742736997638295118561

theorem tailTrace_3491354 : CollatzResearch.WordTrace tailWord_3491354 prefixEnd_3491354 1792742736997638295118561 := by
  unfold tailWord_3491354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31835035448357052159092279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84893427862285472424246077 31835035448357052159092279)
  ·
    refine ⟨47752553172535578238638419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31835035448357052159092279 47752553172535578238638419)
    ·
      refine ⟨71628829758803367357957629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47752553172535578238638419 71628829758803367357957629)
      ·
        refine ⟨26860811159551262759234111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71628829758803367357957629 26860811159551262759234111)
        ·
          refine ⟨40291216739326894138851167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26860811159551262759234111 40291216739326894138851167)
          ·
            refine ⟨60436825108990341208276751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40291216739326894138851167 60436825108990341208276751)
            ·
              refine ⟨90655237663485511812415127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60436825108990341208276751 90655237663485511812415127)
              ·
                refine ⟨135982856495228267718622691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90655237663485511812415127 135982856495228267718622691)
                ·
                  refine ⟨203974284742842401577934037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135982856495228267718622691 203974284742842401577934037)
                  ·
                    refine ⟨4780647298660368786982829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 203974284742842401577934037 4780647298660368786982829)
                    ·
                      refine ⟨1792742736997638295118561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4780647298660368786982829 1792742736997638295118561)
                      ·
                        rfl

theorem cell23_3491354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_3491354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491354 prefixEnd_3491354 := by exact prefixLift 3491354
  have htrace : WordTrace (prefixWord ++ tailWord_3491354) baseStart_3491354 baseEnd_3491354 := by
    simpa [prefixWord, tailWord_3491354, baseEnd_3491354] using wordTrace_append hprefix tailTrace_3491354
  have hstable : (prefixWord ++ tailWord_3491354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491354).length < 2 ^ (prefixWord ++ tailWord_3491354).sum := by decide
  have hdescent : baseEnd_3491354 < baseStart_3491354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491382 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3491382 : Nat := 118140960795 + 3491382 * 2 ^ 59
def prefixEnd_3491382 : Nat := 4983230072969 + 3 ^ 40 * 3491382 * 2
def baseEnd_3491382 : Nat := 597585704818654728522811

theorem tailTrace_3491382 : CollatzResearch.WordTrace tailWord_3491382 prefixEnd_3491382 597585704818654728522811 := by
  unfold tailWord_3491382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958822689832923088649275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84894108691551179612258933 7958822689832923088649275)
  ·
    refine ⟨11938234034749384632973913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958822689832923088649275 11938234034749384632973913)
    ·
      refine ⟨8953675526062038474730435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11938234034749384632973913 8953675526062038474730435)
      ·
        refine ⟨13430513289093057712095653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953675526062038474730435 13430513289093057712095653)
        ·
          refine ⟨2518221241704948321017935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13430513289093057712095653 2518221241704948321017935)
          ·
            refine ⟨3777331862557422481526903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518221241704948321017935 3777331862557422481526903)
            ·
              refine ⟨5665997793836133722290355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777331862557422481526903 5665997793836133722290355)
              ·
                refine ⟨8498996690754200583435533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665997793836133722290355 8498996690754200583435533)
                ·
                  refine ⟨3187123759032825218788325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8498996690754200583435533 3187123759032825218788325)
                  ·
                    refine ⟨597585704818654728522811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3187123759032825218788325 597585704818654728522811)
                    ·
                      rfl

theorem cell23_3491382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3491382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491382 prefixEnd_3491382 := by exact prefixLift 3491382
  have htrace : WordTrace (prefixWord ++ tailWord_3491382) baseStart_3491382 baseEnd_3491382 := by
    simpa [prefixWord, tailWord_3491382, baseEnd_3491382] using wordTrace_append hprefix tailTrace_3491382
  have hstable : (prefixWord ++ tailWord_3491382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491382).length < 2 ^ (prefixWord ++ tailWord_3491382).sum := by decide
  have hdescent : baseEnd_3491382 < baseStart_3491382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491431 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_3491431 : Nat := 118140960795 + 3491431 * 2 ^ 59
def prefixEnd_3491431 : Nat := 4983230072969 + 3 ^ 40 * 3491431 * 2
def baseEnd_3491431 : Nat := 1792782275008034493855707

theorem tailTrace_3491431 : CollatzResearch.WordTrace tailWord_3491431 prefixEnd_3491431 1792782275008034493855707 := by
  unfold tailWord_3491431
  simp only [CollatzResearch.WordTrace]
  refine ⟨127342950214149250786922147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84895300142766167191281431 127342950214149250786922147)
  ·
    refine ⟨191014425321223876180383221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127342950214149250786922147 191014425321223876180383221)
    ·
      refine ⟨17907602373864738391910927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191014425321223876180383221 17907602373864738391910927)
      ·
        refine ⟨26861403560797107587866391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17907602373864738391910927 26861403560797107587866391)
        ·
          refine ⟨40292105341195661381799587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26861403560797107587866391 40292105341195661381799587)
          ·
            refine ⟨60438158011793492072699381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40292105341195661381799587 60438158011793492072699381)
            ·
              refine ⟨5666077313605639881815567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60438158011793492072699381 5666077313605639881815567)
              ·
                refine ⟨8499115970408459822723351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666077313605639881815567 8499115970408459822723351)
                ·
                  refine ⟨12748673955612689734085027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8499115970408459822723351 12748673955612689734085027)
                  ·
                    refine ⟨19123010933419034601127541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12748673955612689734085027 19123010933419034601127541)
                    ·
                      refine ⟨1792782275008034493855707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19123010933419034601127541 1792782275008034493855707)
                      ·
                        rfl

theorem cell23_3491431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_3491431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491431 prefixEnd_3491431 := by exact prefixLift 3491431
  have htrace : WordTrace (prefixWord ++ tailWord_3491431) baseStart_3491431 baseEnd_3491431 := by
    simpa [prefixWord, tailWord_3491431, baseEnd_3491431] using wordTrace_append hprefix tailTrace_3491431
  have hstable : (prefixWord ++ tailWord_3491431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491431).length < 2 ^ (prefixWord ++ tailWord_3491431).sum := by decide
  have hdescent : baseEnd_3491431 < baseStart_3491431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491434 : List Nat := [3, 1, 3, 2, 1, 13]
def baseStart_3491434 : Nat := 118140960795 + 3491434 * 2 ^ 59
def prefixEnd_3491434 : Nat := 4983230072969 + 3 ^ 40 * 3491434 * 2
def baseEnd_3491434 : Nat := 7377711174691349720651

theorem tailTrace_3491434 : CollatzResearch.WordTrace tailWord_3491434 prefixEnd_3491434 7377711174691349720651 := by
  unfold tailWord_3491434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31835764908284595574820339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84895373088758921532854237 31835764908284595574820339)
  ·
    refine ⟨47753647362426893362230509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31835764908284595574820339 47753647362426893362230509)
    ·
      refine ⟨17907617760910085010836441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47753647362426893362230509 17907617760910085010836441)
      ·
        refine ⟨13430713320682563758127331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17907617760910085010836441 13430713320682563758127331)
        ·
          refine ⟨20146069981023845637190997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13430713320682563758127331 20146069981023845637190997)
          ·
            refine ⟨7377711174691349720651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 20146069981023845637190997 7377711174691349720651)
            ·
              rfl

theorem cell23_3491434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 13].length) (baseStart_3491434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491434 prefixEnd_3491434 := by exact prefixLift 3491434
  have htrace : WordTrace (prefixWord ++ tailWord_3491434) baseStart_3491434 baseEnd_3491434 := by
    simpa [prefixWord, tailWord_3491434, baseEnd_3491434] using wordTrace_append hprefix tailTrace_3491434
  have hstable : (prefixWord ++ tailWord_3491434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491434).length < 2 ^ (prefixWord ++ tailWord_3491434).sum := by decide
  have hdescent : baseEnd_3491434 < baseStart_3491434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491496 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3491496 : Nat := 118140960795 + 3491496 * 2 ^ 59
def prefixEnd_3491496 : Nat := 4983230072969 + 3 ^ 40 * 3491496 * 2
def baseEnd_3491496 : Nat := 1792815651250576739542909

theorem tailTrace_3491496 : CollatzResearch.WordTrace tailWord_3491496 prefixEnd_3491496 1792815651250576739542909 := by
  unfold tailWord_3491496
  simp only [CollatzResearch.WordTrace]
  refine ⟨63672660479456883444019171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84896880639275844592025561 63672660479456883444019171)
  ·
    refine ⟨95508990719185325166028757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63672660479456883444019171 95508990719185325166028757)
    ·
      refine ⟨2238491969980906058578799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95508990719185325166028757 2238491969980906058578799)
      ·
        refine ⟨3357737954971359087868199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238491969980906058578799 3357737954971359087868199)
        ·
          refine ⟨5036606932457038631802299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357737954971359087868199 5036606932457038631802299)
          ·
            refine ⟨7554910398685557947703449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036606932457038631802299 7554910398685557947703449)
            ·
              refine ⟨5666182799014168460777587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7554910398685557947703449 5666182799014168460777587)
              ·
                refine ⟨8499274198521252691166381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666182799014168460777587 8499274198521252691166381)
                ·
                  refine ⟨3187227824445469759187393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8499274198521252691166381 3187227824445469759187393)
                  ·
                    refine ⟨2390420868334102319390545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3187227824445469759187393 2390420868334102319390545)
                    ·
                      refine ⟨1792815651250576739542909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2390420868334102319390545 1792815651250576739542909)
                      ·
                        rfl

theorem cell23_3491496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3491496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491496 prefixEnd_3491496 := by exact prefixLift 3491496
  have htrace : WordTrace (prefixWord ++ tailWord_3491496) baseStart_3491496 baseEnd_3491496 := by
    simpa [prefixWord, tailWord_3491496, baseEnd_3491496] using wordTrace_append hprefix tailTrace_3491496
  have hstable : (prefixWord ++ tailWord_3491496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491496).length < 2 ^ (prefixWord ++ tailWord_3491496).sum := by decide
  have hdescent : baseEnd_3491496 < baseStart_3491496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491511 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 2, 6]
def baseStart_3491511 : Nat := 118140960795 + 3491511 * 2 ^ 59
def prefixEnd_3491511 : Nat := 4983230072969 + 3 ^ 40 * 3491511 * 2
def baseEnd_3491511 : Nat := 597607784486798060285113

theorem tailTrace_3491511 : CollatzResearch.WordTrace tailWord_3491511 prefixEnd_3491511 597607784486798060285113 := by
  unfold tailWord_3491511
  simp only [CollatzResearch.WordTrace]
  refine ⟨127345868053859424449834387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84897245369239616299889591 127345868053859424449834387)
  ·
    refine ⟨191018802080789136674751581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127345868053859424449834387 191018802080789136674751581)
    ·
      refine ⟨71632050780295926253031843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191018802080789136674751581 71632050780295926253031843)
      ·
        refine ⟨107448076170443889379547765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71632050780295926253031843 107448076170443889379547765)
        ·
          refine ⟨10073257140979114629332603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107448076170443889379547765 10073257140979114629332603)
          ·
            refine ⟨15109885711468671943998905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10073257140979114629332603 15109885711468671943998905)
            ·
              refine ⟨11332414283601503957999179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15109885711468671943998905 11332414283601503957999179)
              ·
                refine ⟨16998621425402255936998769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11332414283601503957999179 16998621425402255936998769)
                ·
                  refine ⟨12748966069051691952749077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16998621425402255936998769 12748966069051691952749077)
                  ·
                    refine ⟨597607784486798060285113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12748966069051691952749077 597607784486798060285113)
                    ·
                      rfl

theorem cell23_3491511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_3491511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491511 prefixEnd_3491511 := by exact prefixLift 3491511
  have htrace : WordTrace (prefixWord ++ tailWord_3491511) baseStart_3491511 baseEnd_3491511 := by
    simpa [prefixWord, tailWord_3491511, baseEnd_3491511] using wordTrace_append hprefix tailTrace_3491511
  have hstable : (prefixWord ++ tailWord_3491511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491511).length < 2 ^ (prefixWord ++ tailWord_3491511).sum := by decide
  have hdescent : baseEnd_3491511 < baseStart_3491511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491538 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3491538 : Nat := 118140960795 + 3491538 * 2 ^ 59
def prefixEnd_3491538 : Nat := 4983230072969 + 3 ^ 40 * 3491538 * 2
def baseEnd_3491538 : Nat := 1792837217438065575217715

theorem tailTrace_3491538 : CollatzResearch.WordTrace tailWord_3491538 prefixEnd_3491538 1792837217438065575217715 := by
  unfold tailWord_3491538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31836713206190402015266817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84897901883174405374044845 31836713206190402015266817)
  ·
    refine ⟨23877534904642801511450113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31836713206190402015266817 23877534904642801511450113)
    ·
      refine ⟨17908151178482101133587585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23877534904642801511450113 17908151178482101133587585)
      ·
        refine ⟨13431113383861575850190689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17908151178482101133587585 13431113383861575850190689)
        ·
          refine ⟨10073335037896181887643017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13431113383861575850190689 10073335037896181887643017)
          ·
            refine ⟨7555001278422136415732263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10073335037896181887643017 7555001278422136415732263)
            ·
              refine ⟨11332501917633204623598395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555001278422136415732263 11332501917633204623598395)
              ·
                refine ⟨16998752876449806935397593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11332501917633204623598395 16998752876449806935397593)
                ·
                  refine ⟨12749064657337355201548195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16998752876449806935397593 12749064657337355201548195)
                  ·
                    refine ⟨19123596986006032802322293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12749064657337355201548195 19123596986006032802322293)
                    ·
                      refine ⟨1792837217438065575217715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19123596986006032802322293 1792837217438065575217715)
                      ·
                        rfl

theorem cell23_3491538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3491538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491538 prefixEnd_3491538 := by exact prefixLift 3491538
  have htrace : WordTrace (prefixWord ++ tailWord_3491538) baseStart_3491538 baseEnd_3491538 := by
    simpa [prefixWord, tailWord_3491538, baseEnd_3491538] using wordTrace_append hprefix tailTrace_3491538
  have hstable : (prefixWord ++ tailWord_3491538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491538).length < 2 ^ (prefixWord ++ tailWord_3491538).sum := by decide
  have hdescent : baseEnd_3491538 < baseStart_3491538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491569 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 2, 2, 2]
def baseStart_3491569 : Nat := 118140960795 + 3491569 * 2 ^ 59
def prefixEnd_3491569 : Nat := 4983230072969 + 3 ^ 40 * 3491569 * 2
def baseEnd_3491569 : Nat := 1792853135338354953930073

theorem tailTrace_3491569 : CollatzResearch.WordTrace tailWord_3491569 prefixEnd_3491569 1792853135338354953930073 := by
  unfold tailWord_3491569
  simp only [CollatzResearch.WordTrace]
  refine ⟨127347983487649300355445761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84898655658432866903630507 127347983487649300355445761)
  ·
    refine ⟨95510987615736975266584321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127347983487649300355445761 95510987615736975266584321)
    ·
      refine ⟨71633240711802731449938241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95510987615736975266584321 71633240711802731449938241)
      ·
        refine ⟨53724930533852048587453681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71633240711802731449938241 53724930533852048587453681)
        ·
          refine ⟨40293697900389036440590261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53724930533852048587453681 40293697900389036440590261)
          ·
            refine ⟨3777534178161472166305337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40293697900389036440590261 3777534178161472166305337)
            ·
              refine ⟨2833150633621104124729003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777534178161472166305337 2833150633621104124729003)
              ·
                refine ⟨4249725950431656187093505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833150633621104124729003 4249725950431656187093505)
                ·
                  refine ⟨3187294462823742140320129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249725950431656187093505 3187294462823742140320129)
                  ·
                    refine ⟨2390470847117806605240097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3187294462823742140320129 2390470847117806605240097)
                    ·
                      refine ⟨1792853135338354953930073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2390470847117806605240097 1792853135338354953930073)
                      ·
                        rfl

theorem cell23_3491569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_3491569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491569 prefixEnd_3491569 := by exact prefixLift 3491569
  have htrace : WordTrace (prefixWord ++ tailWord_3491569) baseStart_3491569 baseEnd_3491569 := by
    simpa [prefixWord, tailWord_3491569, baseEnd_3491569] using wordTrace_append hprefix tailTrace_3491569
  have hstable : (prefixWord ++ tailWord_3491569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491569).length < 2 ^ (prefixWord ++ tailWord_3491569).sum := by decide
  have hdescent : baseEnd_3491569 < baseStart_3491569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491588 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_3491588 : Nat := 118140960795 + 3491588 * 2 ^ 59
def prefixEnd_3491588 : Nat := 4983230072969 + 3 ^ 40 * 3491588 * 2
def baseEnd_3491588 : Nat := 597620963823596793197495

theorem tailTrace_3491588 : CollatzResearch.WordTrace tailWord_3491588 prefixEnd_3491588 597620963823596793197495 := by
  unfold tailWord_3491588
  simp only [CollatzResearch.WordTrace]
  refine ⟨63674338237290233300193709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84899117649720311066924945 63674338237290233300193709)
  ·
    refine ⟨23877876838983837487572641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63674338237290233300193709 23877876838983837487572641)
    ·
      refine ⟨17908407629237878115679481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23877876838983837487572641 17908407629237878115679481)
      ·
        refine ⟨13431305721928408586759611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17908407629237878115679481 13431305721928408586759611)
        ·
          refine ⟨20146958582892612880139417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13431305721928408586759611 20146958582892612880139417)
          ·
            refine ⟨15110218937169459660104563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20146958582892612880139417 15110218937169459660104563)
            ·
              refine ⟨22665328405754189490156845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15110218937169459660104563 22665328405754189490156845)
              ·
                refine ⟨8499498152157821058808817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22665328405754189490156845 8499498152157821058808817)
                ·
                  refine ⟨6374623614118365794106613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8499498152157821058808817 6374623614118365794106613)
                  ·
                    refine ⟨597620963823596793197495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6374623614118365794106613 597620963823596793197495)
                    ·
                      rfl

theorem cell23_3491588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_3491588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491588 prefixEnd_3491588 := by exact prefixLift 3491588
  have htrace : WordTrace (prefixWord ++ tailWord_3491588) baseStart_3491588 baseEnd_3491588 := by
    simpa [prefixWord, tailWord_3491588, baseEnd_3491588] using wordTrace_append hprefix tailTrace_3491588
  have hstable : (prefixWord ++ tailWord_3491588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491588).length < 2 ^ (prefixWord ++ tailWord_3491588).sum := by decide
  have hdescent : baseEnd_3491588 < baseStart_3491588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491608 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3491608 : Nat := 118140960795 + 3491608 * 2 ^ 59
def prefixEnd_3491608 : Nat := 4983230072969 + 3 ^ 40 * 3491608 * 2
def baseEnd_3491608 : Nat := 1792873161083880301342393

theorem tailTrace_3491608 : CollatzResearch.WordTrace tailWord_3491608 prefixEnd_3491608 1792873161083880301342393 := by
  unfold tailWord_3491608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63674702967254005008057739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84899603956338673344076985 63674702967254005008057739)
  ·
    refine ⟨95512054450881007512086609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63674702967254005008057739 95512054450881007512086609)
    ·
      refine ⟨71634040838160755634064957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95512054450881007512086609 71634040838160755634064957)
      ·
        refine ⟨26862765314310283362774359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71634040838160755634064957 26862765314310283362774359)
        ·
          refine ⟨40294147971465425044161539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26862765314310283362774359 40294147971465425044161539)
          ·
            refine ⟨60441221957198137566242309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40294147971465425044161539 60441221957198137566242309)
            ·
              refine ⟨11332729116974650793670433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60441221957198137566242309 11332729116974650793670433)
              ·
                refine ⟨8499546837730988095252825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11332729116974650793670433 8499546837730988095252825)
                ·
                  refine ⟨6374660128298241071439619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8499546837730988095252825 6374660128298241071439619)
                  ·
                    refine ⟨9561990192447361607159429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6374660128298241071439619 9561990192447361607159429)
                    ·
                      refine ⟨1792873161083880301342393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9561990192447361607159429 1792873161083880301342393)
                      ·
                        rfl

theorem cell23_3491608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3491608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491608 prefixEnd_3491608 := by exact prefixLift 3491608
  have htrace : WordTrace (prefixWord ++ tailWord_3491608) baseStart_3491608 baseEnd_3491608 := by
    simpa [prefixWord, tailWord_3491608, baseEnd_3491608] using wordTrace_append hprefix tailTrace_3491608
  have hstable : (prefixWord ++ tailWord_3491608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491608).length < 2 ^ (prefixWord ++ tailWord_3491608).sum := by decide
  have hdescent : baseEnd_3491608 < baseStart_3491608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491635 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 3, 4]
def baseStart_3491635 : Nat := 118140960795 + 3491635 * 2 ^ 59
def prefixEnd_3491635 : Nat := 4983230072969 + 3 ^ 40 * 3491635 * 2
def baseEnd_3491635 : Nat := 597629008353850565234923

theorem tailTrace_3491635 : CollatzResearch.WordTrace tailWord_3491635 prefixEnd_3491635 597629008353850565234923 := by
  unfold tailWord_3491635
  simp only [CollatzResearch.WordTrace]
  refine ⟨127350390705410193627348359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84900260470273462418232239 127350390705410193627348359)
  ·
    refine ⟨191025586058115290441022539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127350390705410193627348359 191025586058115290441022539)
    ·
      refine ⟨286538379087172935661533809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191025586058115290441022539 286538379087172935661533809)
      ·
        refine ⟨214903784315379701746150357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286538379087172935661533809 214903784315379701746150357)
        ·
          refine ⟨5036807444891711759675399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 214903784315379701746150357 5036807444891711759675399)
          ·
            refine ⟨7555211167337567639513099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036807444891711759675399 7555211167337567639513099)
            ·
              refine ⟨11332816751006351459269649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555211167337567639513099 11332816751006351459269649)
              ·
                refine ⟨8499612563254763594452237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11332816751006351459269649 8499612563254763594452237)
                ·
                  refine ⟨3187354711220536347919589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8499612563254763594452237 3187354711220536347919589)
                  ·
                    refine ⟨597629008353850565234923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3187354711220536347919589 597629008353850565234923)
                    ·
                      rfl

theorem cell23_3491635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 4].length) (baseStart_3491635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491635 prefixEnd_3491635 := by exact prefixLift 3491635
  have htrace : WordTrace (prefixWord ++ tailWord_3491635) baseStart_3491635 baseEnd_3491635 := by
    simpa [prefixWord, tailWord_3491635, baseEnd_3491635] using wordTrace_append hprefix tailTrace_3491635
  have hstable : (prefixWord ++ tailWord_3491635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491635).length < 2 ^ (prefixWord ++ tailWord_3491635).sum := by decide
  have hdescent : baseEnd_3491635 < baseStart_3491635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491645 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3491645 : Nat := 118140960795 + 3491645 * 2 ^ 59
def prefixEnd_3491645 : Nat := 4983230072969 + 3 ^ 40 * 3491645 * 2
def baseEnd_3491645 : Nat := 1792892159868096656579723

theorem tailTrace_3491645 : CollatzResearch.WordTrace tailWord_3491645 prefixEnd_3491645 1792892159868096656579723 := by
  unfold tailWord_3491645
  simp only [CollatzResearch.WordTrace]
  refine ⟨127350755435373965335212389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84900503623582643556808259 127350755435373965335212389)
  ·
    refine ⟨23878266644132618500352323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127350755435373965335212389 23878266644132618500352323)
    ·
      refine ⟨35817399966198927750528485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23878266644132618500352323 35817399966198927750528485)
      ·
        refine ⟨6715762493662298953224091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35817399966198927750528485 6715762493662298953224091)
        ·
          refine ⟨10073643740493448429836137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715762493662298953224091 10073643740493448429836137)
          ·
            refine ⟨7555232805370086322377103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10073643740493448429836137 7555232805370086322377103)
            ·
              refine ⟨11332849208055129483565655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555232805370086322377103 11332849208055129483565655)
              ·
                refine ⟨16999273812082694225348483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11332849208055129483565655 16999273812082694225348483)
                ·
                  refine ⟨25498910718124041338022725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16999273812082694225348483 25498910718124041338022725)
                  ·
                    refine ⟨4781045759648257750879261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25498910718124041338022725 4781045759648257750879261)
                    ·
                      refine ⟨1792892159868096656579723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4781045759648257750879261 1792892159868096656579723)
                      ·
                        rfl

theorem cell23_3491645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3491645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491645 prefixEnd_3491645 := by exact prefixLift 3491645
  have htrace : WordTrace (prefixWord ++ tailWord_3491645) baseStart_3491645 baseEnd_3491645 := by
    simpa [prefixWord, tailWord_3491645, baseEnd_3491645] using wordTrace_append hprefix tailTrace_3491645
  have hstable : (prefixWord ++ tailWord_3491645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491645).length < 2 ^ (prefixWord ++ tailWord_3491645).sum := by decide
  have hdescent : baseEnd_3491645 < baseStart_3491645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491665 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 6]
def baseStart_3491665 : Nat := 118140960795 + 3491665 * 2 ^ 59
def prefixEnd_3491665 : Nat := 4983230072969 + 3 ^ 40 * 3491665 * 2
def baseEnd_3491665 : Nat := 199211381053465175369959

theorem tailTrace_3491665 : CollatzResearch.WordTrace tailWord_3491665 prefixEnd_3491665 199211381053465175369959 := by
  unfold tailWord_3491665
  simp only [CollatzResearch.WordTrace]
  refine ⟨127351484895301508750940449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84900989930201005833960299 127351484895301508750940449)
  ·
    refine ⟨95513613671476131563205337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127351484895301508750940449 95513613671476131563205337)
    ·
      refine ⟨71635210253607098672404003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95513613671476131563205337 71635210253607098672404003)
      ·
        refine ⟨107452815380410648008606005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71635210253607098672404003 107452815380410648008606005)
        ·
          refine ⟨10073701441913498250806813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107452815380410648008606005 10073701441913498250806813)
          ·
            refine ⟨3777638040717561844052555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10073701441913498250806813 3777638040717561844052555)
            ·
              refine ⟨5666457061076342766078833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777638040717561844052555 5666457061076342766078833)
              ·
                refine ⟨4249842795807257074559125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5666457061076342766078833 4249842795807257074559125)
                ·
                  refine ⟨199211381053465175369959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4249842795807257074559125 199211381053465175369959)
                  ·
                    rfl

theorem cell23_3491665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 6].length) (baseStart_3491665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491665 prefixEnd_3491665 := by exact prefixLift 3491665
  have htrace : WordTrace (prefixWord ++ tailWord_3491665) baseStart_3491665 baseEnd_3491665 := by
    simpa [prefixWord, tailWord_3491665, baseEnd_3491665] using wordTrace_append hprefix tailTrace_3491665
  have hstable : (prefixWord ++ tailWord_3491665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491665).length < 2 ^ (prefixWord ++ tailWord_3491665).sum := by decide
  have hdescent : baseEnd_3491665 < baseStart_3491665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491668 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3491668 : Nat := 118140960795 + 3491668 * 2 ^ 59
def prefixEnd_3491668 : Nat := 4983230072969 + 3 ^ 40 * 3491668 * 2
def baseEnd_3491668 : Nat := 1792903969923150066592117

theorem tailTrace_3491668 : CollatzResearch.WordTrace tailWord_3491668 prefixEnd_3491668 1792903969923150066592117 := by
  unfold tailWord_3491668
  simp only [CollatzResearch.WordTrace]
  refine ⟨63675797157145320131649829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84901062876193760175533105 63675797157145320131649829)
  ·
    refine ⟨11939211966964747524684343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63675797157145320131649829 11939211966964747524684343)
    ·
      refine ⟨17908817950447121287026515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11939211966964747524684343 17908817950447121287026515)
      ·
        refine ⟨26863226925670681930539773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17908817950447121287026515 26863226925670681930539773)
        ·
          refine ⟨10073710097126505723952415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26863226925670681930539773 10073710097126505723952415)
          ·
            refine ⟨15110565145689758585928623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10073710097126505723952415 15110565145689758585928623)
            ·
              refine ⟨22665847718534637878892935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15110565145689758585928623 22665847718534637878892935)
              ·
                refine ⟨33998771577801956818339403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22665847718534637878892935 33998771577801956818339403)
                ·
                  refine ⟨50998157366702935227509105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33998771577801956818339403 50998157366702935227509105)
                  ·
                    refine ⟨38248618025027201420631829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50998157366702935227509105 38248618025027201420631829)
                    ·
                      refine ⟨1792903969923150066592117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38248618025027201420631829 1792903969923150066592117)
                      ·
                        rfl

theorem cell23_3491668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3491668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491668 prefixEnd_3491668 := by exact prefixLift 3491668
  have htrace : WordTrace (prefixWord ++ tailWord_3491668) baseStart_3491668 baseEnd_3491668 := by
    simpa [prefixWord, tailWord_3491668, baseEnd_3491668] using wordTrace_append hprefix tailTrace_3491668
  have hstable : (prefixWord ++ tailWord_3491668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491668).length < 2 ^ (prefixWord ++ tailWord_3491668).sum := by decide
  have hdescent : baseEnd_3491668 < baseStart_3491668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491682 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_3491682 : Nat := 118140960795 + 3491682 * 2 ^ 59
def prefixEnd_3491682 : Nat := 4983230072969 + 3 ^ 40 * 3491682 * 2
def baseEnd_3491682 : Nat := 199212350961368112424117

theorem tailTrace_3491682 : CollatzResearch.WordTrace tailWord_3491682 prefixEnd_3491682 199212350961368112424117 := by
  unfold tailWord_3491682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31838026234059980163577325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84901403290826613769539533 31838026234059980163577325)
  ·
    refine ⟨11939259837772492561341497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31838026234059980163577325 11939259837772492561341497)
    ·
      refine ⟨8954444878329369421006123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11939259837772492561341497 8954444878329369421006123)
      ·
        refine ⟨13431667317494054131509185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8954444878329369421006123 13431667317494054131509185)
        ·
          refine ⟨10073750488120540598631889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13431667317494054131509185 10073750488120540598631889)
          ·
            refine ⟨7555312866090405448973917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10073750488120540598631889 7555312866090405448973917)
            ·
              refine ⟨2833242324783902043365219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7555312866090405448973917 2833242324783902043365219)
              ·
                refine ⟨4249863487175853065047829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833242324783902043365219 4249863487175853065047829)
                ·
                  refine ⟨199212350961368112424117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4249863487175853065047829 199212350961368112424117)
                  ·
                    rfl

theorem cell23_3491682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_3491682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491682 prefixEnd_3491682 := by exact prefixLift 3491682
  have htrace : WordTrace (prefixWord ++ tailWord_3491682) baseStart_3491682 baseEnd_3491682 := by
    simpa [prefixWord, tailWord_3491682, baseEnd_3491682] using wordTrace_append hprefix tailTrace_3491682
  have hstable : (prefixWord ++ tailWord_3491682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491682).length < 2 ^ (prefixWord ++ tailWord_3491682).sum := by decide
  have hdescent : baseEnd_3491682 < baseStart_3491682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491715 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 4]
def baseStart_3491715 : Nat := 118140960795 + 3491715 * 2 ^ 59
def prefixEnd_3491715 : Nat := 4983230072969 + 3 ^ 40 * 3491715 * 2
def baseEnd_3491715 : Nat := 1792928103513911382704401

theorem tailTrace_3491715 : CollatzResearch.WordTrace tailWord_3491715 prefixEnd_3491715 1792928103513911382704401 := by
  unfold tailWord_3491715
  simp only [CollatzResearch.WordTrace]
  refine ⟨127353308545120367290260599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84902205696746911526840399 127353308545120367290260599)
  ·
    refine ⟨191029962817680550935390899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127353308545120367290260599 191029962817680550935390899)
    ·
      refine ⟨286544944226520826403086349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191029962817680550935390899 286544944226520826403086349)
      ·
        refine ⟨107454354084945309901157381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286544944226520826403086349 107454354084945309901157381)
        ·
          refine ⟨20147691390927245606467009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107454354084945309901157381 20147691390927245606467009)
          ·
            refine ⟨15110768543195434204850257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20147691390927245606467009 15110768543195434204850257)
            ·
              refine ⟨11333076407396575653637693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15110768543195434204850257 11333076407396575653637693)
              ·
                refine ⟨4249903652773715870114135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11333076407396575653637693 4249903652773715870114135)
                ·
                  refine ⟨6374855479160573805171203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249903652773715870114135 6374855479160573805171203)
                  ·
                    refine ⟨9562283218740860707756805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6374855479160573805171203 9562283218740860707756805)
                    ·
                      refine ⟨1792928103513911382704401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9562283218740860707756805 1792928103513911382704401)
                      ·
                        rfl

theorem cell23_3491715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_3491715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491715 prefixEnd_3491715 := by exact prefixLift 3491715
  have htrace : WordTrace (prefixWord ++ tailWord_3491715) baseStart_3491715 baseEnd_3491715 := by
    simpa [prefixWord, tailWord_3491715, baseEnd_3491715] using wordTrace_append hprefix tailTrace_3491715
  have hstable : (prefixWord ++ tailWord_3491715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491715).length < 2 ^ (prefixWord ++ tailWord_3491715).sum := by decide
  have hdescent : baseEnd_3491715 < baseStart_3491715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491726 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3491726 : Nat := 118140960795 + 3491726 * 2 ^ 59
def prefixEnd_3491726 : Nat := 4983230072969 + 3 ^ 40 * 3491726 * 2
def baseEnd_3491726 : Nat := 1792933751801110839666851

theorem tailTrace_3491726 : CollatzResearch.WordTrace tailWord_3491726 prefixEnd_3491726 1792933751801110839666851 := by
  unfold tailWord_3491726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919213718510064521113879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84902473165387010779274021 15919213718510064521113879)
  ·
    refine ⟨23878820577765096781670819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15919213718510064521113879 23878820577765096781670819)
    ·
      refine ⟨35818230866647645172506229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23878820577765096781670819 35818230866647645172506229)
      ·
        refine ⟨3357959143748216734922459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35818230866647645172506229 3357959143748216734922459)
        ·
          refine ⟨5036938715622325102383689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357959143748216734922459 5036938715622325102383689)
          ·
            refine ⟨3777704036716743826787767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5036938715622325102383689 3777704036716743826787767)
            ·
              refine ⟨5666556055075115740181651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777704036716743826787767 5666556055075115740181651)
              ·
                refine ⟨8499834082612673610272477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666556055075115740181651 8499834082612673610272477)
                ·
                  refine ⟨3187437780979752603852179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8499834082612673610272477 3187437780979752603852179)
                  ·
                    refine ⟨4781156671469628905778269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3187437780979752603852179 4781156671469628905778269)
                    ·
                      refine ⟨1792933751801110839666851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4781156671469628905778269 1792933751801110839666851)
                      ·
                        rfl

theorem cell23_3491726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3491726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491726 prefixEnd_3491726 := by exact prefixLift 3491726
  have htrace : WordTrace (prefixWord ++ tailWord_3491726) baseStart_3491726 baseEnd_3491726 := by
    simpa [prefixWord, tailWord_3491726, baseEnd_3491726] using wordTrace_append hprefix tailTrace_3491726
  have hstable : (prefixWord ++ tailWord_3491726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491726).length < 2 ^ (prefixWord ++ tailWord_3491726).sum := by decide
  have hdescent : baseEnd_3491726 < baseStart_3491726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491738 : List Nat := [3, 1, 1, 4, 2, 1, 1, 10]
def baseStart_3491738 : Nat := 118140960795 + 3491738 * 2 ^ 59
def prefixEnd_3491738 : Nat := 4983230072969 + 3 ^ 40 * 3491738 * 2
def baseEnd_3491738 : Nat := 66405181984035733063585

theorem tailTrace_3491738 : CollatzResearch.WordTrace tailWord_3491738 prefixEnd_3491738 66405181984035733063585 := by
  unfold tailWord_3491738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31838536856009260554586967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84902764949358028145565245 31838536856009260554586967)
  ·
    refine ⟨47757805284013890831880451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31838536856009260554586967 47757805284013890831880451)
    ·
      refine ⟨71636707926020836247820677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47757805284013890831880451 71636707926020836247820677)
      ·
        refine ⟨13431882736128906796466377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71636707926020836247820677 13431882736128906796466377)
        ·
          refine ⟨10073912052096680097349783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13431882736128906796466377 10073912052096680097349783)
          ·
            refine ⟨15110868078145020146024675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10073912052096680097349783 15110868078145020146024675)
            ·
              refine ⟨22666302117217530219037013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15110868078145020146024675 22666302117217530219037013)
              ·
                refine ⟨66405181984035733063585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22666302117217530219037013 66405181984035733063585)
                ·
                  rfl

theorem cell23_3491738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_3491738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491738 prefixEnd_3491738 := by exact prefixLift 3491738
  have htrace : WordTrace (prefixWord ++ tailWord_3491738) baseStart_3491738 baseEnd_3491738 := by
    simpa [prefixWord, tailWord_3491738, baseEnd_3491738] using wordTrace_append hprefix tailTrace_3491738
  have hstable : (prefixWord ++ tailWord_3491738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491738).length < 2 ^ (prefixWord ++ tailWord_3491738).sum := by decide
  have hdescent : baseEnd_3491738 < baseStart_3491738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491765 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3491765 : Nat := 118140960795 + 3491765 * 2 ^ 59
def prefixEnd_3491765 : Nat := 4983230072969 + 3 ^ 40 * 3491765 * 2
def baseEnd_3491765 : Nat := 1792953777546636187079171

theorem tailTrace_3491765 : CollatzResearch.WordTrace tailWord_3491765 prefixEnd_3491765 1792953777546636187079171 := by
  unfold tailWord_3491765
  simp only [CollatzResearch.WordTrace]
  refine ⟨127355132194939225829580749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84903421463292817219720499 127355132194939225829580749)
  ·
    refine ⟨47758174573102209686092781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127355132194939225829580749 47758174573102209686092781)
    ·
      refine ⟨17909315464913328632284793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47758174573102209686092781 17909315464913328632284793)
      ·
        refine ⟨13431986598684996474213595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17909315464913328632284793 13431986598684996474213595)
        ·
          refine ⟨20147979898027494711320393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13431986598684996474213595 20147979898027494711320393)
          ·
            refine ⟨15110984923520621033490295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20147979898027494711320393 15110984923520621033490295)
            ·
              refine ⟨22666477385280931550235443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15110984923520621033490295 22666477385280931550235443)
              ·
                refine ⟨33999716077921397325353165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22666477385280931550235443 33999716077921397325353165)
                ·
                  refine ⟨12749893529220523997007437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33999716077921397325353165 12749893529220523997007437)
                  ·
                    refine ⟨4781210073457696498877789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12749893529220523997007437 4781210073457696498877789)
                    ·
                      refine ⟨1792953777546636187079171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4781210073457696498877789 1792953777546636187079171)
                      ·
                        rfl

theorem cell23_3491765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3491765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491765 prefixEnd_3491765 := by exact prefixLift 3491765
  have htrace : WordTrace (prefixWord ++ tailWord_3491765) baseStart_3491765 baseEnd_3491765 := by
    simpa [prefixWord, tailWord_3491765, baseEnd_3491765] using wordTrace_append hprefix tailTrace_3491765
  have hstable : (prefixWord ++ tailWord_3491765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491765).length < 2 ^ (prefixWord ++ tailWord_3491765).sum := by decide
  have hdescent : baseEnd_3491765 < baseStart_3491765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491808 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_3491808 : Nat := 118140960795 + 3491808 * 2 ^ 59
def prefixEnd_3491808 : Nat := 4983230072969 + 3 ^ 40 * 3491808 * 2
def baseEnd_3491808 : Nat := 1792975857214779518841473

theorem tailTrace_3491808 : CollatzResearch.WordTrace tailWord_3491808 prefixEnd_3491808 1792975857214779518841473 := by
  unfold tailWord_3491808
  simp only [CollatzResearch.WordTrace]
  refine ⟨63678350266891722086698039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84904467022522296115597385 63678350266891722086698039)
  ·
    refine ⟨95517525400337583130047059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63678350266891722086698039 95517525400337583130047059)
    ·
      refine ⟨143276288100506374695070589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95517525400337583130047059 143276288100506374695070589)
      ·
        refine ⟨53728608037689890510651471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143276288100506374695070589 53728608037689890510651471)
        ·
          refine ⟨80592912056534835765977207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53728608037689890510651471 80592912056534835765977207)
          ·
            refine ⟨120889368084802253648965811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80592912056534835765977207 120889368084802253648965811)
            ·
              refine ⟨181334052127203380473448717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120889368084802253648965811 181334052127203380473448717)
              ·
                refine ⟨68000269547701267677543269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181334052127203380473448717 68000269547701267677543269)
                ·
                  refine ⟨12750050540193987689539363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68000269547701267677543269 12750050540193987689539363)
                  ·
                    refine ⟨19125075810290981534309045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12750050540193987689539363 19125075810290981534309045)
                    ·
                      refine ⟨1792975857214779518841473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19125075810290981534309045 1792975857214779518841473)
                      ·
                        rfl

theorem cell23_3491808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_3491808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491808 prefixEnd_3491808 := by exact prefixLift 3491808
  have htrace : WordTrace (prefixWord ++ tailWord_3491808) baseStart_3491808 baseEnd_3491808 := by
    simpa [prefixWord, tailWord_3491808, baseEnd_3491808] using wordTrace_append hprefix tailTrace_3491808
  have hstable : (prefixWord ++ tailWord_3491808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491808).length < 2 ^ (prefixWord ++ tailWord_3491808).sum := by decide
  have hdescent : baseEnd_3491808 < baseStart_3491808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491845 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 7]
def baseStart_3491845 : Nat := 118140960795 + 3491845 * 2 ^ 59
def prefixEnd_3491845 : Nat := 4983230072969 + 3 ^ 40 * 3491845 * 2
def baseEnd_3491845 : Nat := 199221650666555097119867

theorem tailTrace_3491845 : CollatzResearch.WordTrace tailWord_3491845 prefixEnd_3491845 199221650666555097119867 := by
  unfold tailWord_3491845
  simp only [CollatzResearch.WordTrace]
  refine ⟨127358050034649399492492989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84905366689766266328328659 127358050034649399492492989)
  ·
    refine ⟨47759268762993524809684871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127358050034649399492492989 47759268762993524809684871)
    ·
      refine ⟨71638903144490287214527307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47759268762993524809684871 71638903144490287214527307)
      ·
        refine ⟨107458354716735430821790961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71638903144490287214527307 107458354716735430821790961)
        ·
          refine ⟨80593766037551573116343221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107458354716735430821790961 80593766037551573116343221)
          ·
            refine ⟨7555665566020459979657177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80593766037551573116343221 7555665566020459979657177)
            ·
              refine ⟨5666749174515344984742883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555665566020459979657177 5666749174515344984742883)
              ·
                refine ⟨8500123761773017477114325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666749174515344984742883 8500123761773017477114325)
                ·
                  refine ⟨199221650666555097119867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8500123761773017477114325 199221650666555097119867)
                  ·
                    rfl

theorem cell23_3491845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_3491845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491845 prefixEnd_3491845 := by exact prefixLift 3491845
  have htrace : WordTrace (prefixWord ++ tailWord_3491845) baseStart_3491845 baseEnd_3491845 := by
    simpa [prefixWord, tailWord_3491845, baseEnd_3491845] using wordTrace_append hprefix tailTrace_3491845
  have hstable : (prefixWord ++ tailWord_3491845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491845).length < 2 ^ (prefixWord ++ tailWord_3491845).sum := by decide
  have hdescent : baseEnd_3491845 < baseStart_3491845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491875 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 2, 5]
def baseStart_3491875 : Nat := 118140960795 + 3491875 * 2 ^ 59
def prefixEnd_3491875 : Nat := 4983230072969 + 3 ^ 40 * 3491875 * 2
def baseEnd_3491875 : Nat := 597670086806210252234555

theorem tailTrace_3491875 : CollatzResearch.WordTrace tailWord_3491875 prefixEnd_3491875 597670086806210252234555 := by
  unfold tailWord_3491875
  simp only [CollatzResearch.WordTrace]
  refine ⟨127359144224540714616085079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84906096149693809744056719 127359144224540714616085079)
  ·
    refine ⟨191038716336811071924127619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127359144224540714616085079 191038716336811071924127619)
    ·
      refine ⟨286558074505216607886191429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191038716336811071924127619 286558074505216607886191429)
      ·
        refine ⟨53729638969728113978660893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286558074505216607886191429 53729638969728113978660893)
        ·
          refine ⟨20148614613648042741997835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53729638969728113978660893 20148614613648042741997835)
          ·
            refine ⟨30222921920472064112996753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20148614613648042741997835 30222921920472064112996753)
            ·
              refine ⟨22667191440354048084747565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30222921920472064112996753 22667191440354048084747565)
              ·
                refine ⟨8500196790132768031780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22667191440354048084747565 8500196790132768031780337)
                ·
                  refine ⟨6375147592599576023835253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8500196790132768031780337 6375147592599576023835253)
                  ·
                    refine ⟨597670086806210252234555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6375147592599576023835253 597670086806210252234555)
                    ·
                      rfl

theorem cell23_3491875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 5].length) (baseStart_3491875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491875 prefixEnd_3491875 := by exact prefixLift 3491875
  have htrace : WordTrace (prefixWord ++ tailWord_3491875) baseStart_3491875 baseEnd_3491875 := by
    simpa [prefixWord, tailWord_3491875, baseEnd_3491875] using wordTrace_append hprefix tailTrace_3491875
  have hstable : (prefixWord ++ tailWord_3491875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491875).length < 2 ^ (prefixWord ++ tailWord_3491875).sum := by decide
  have hdescent : baseEnd_3491875 < baseStart_3491875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491895 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_3491895 : Nat := 118140960795 + 3491895 * 2 ^ 59
def prefixEnd_3491895 : Nat := 4983230072969 + 3 ^ 40 * 3491895 * 2
def baseEnd_3491895 : Nat := 1793020530031720678453573

theorem tailTrace_3491895 : CollatzResearch.WordTrace tailWord_3491895 prefixEnd_3491895 1793020530031720678453573 := by
  unfold tailWord_3491895
  simp only [CollatzResearch.WordTrace]
  refine ⟨127359873684468258031813139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84906582456312172021208759 127359873684468258031813139)
  ·
    refine ⟨191039810526702387047719709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127359873684468258031813139 191039810526702387047719709)
    ·
      refine ⟨71639928947513395142894891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191039810526702387047719709 71639928947513395142894891)
      ·
        refine ⟨107459893421270092714342337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71639928947513395142894891 107459893421270092714342337)
        ·
          refine ⟨80594920065952569535756753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107459893421270092714342337 80594920065952569535756753)
          ·
            refine ⟨60446190049464427151817565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80594920065952569535756753 60446190049464427151817565)
            ·
              refine ⟨22667321268549160181931587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60446190049464427151817565 22667321268549160181931587)
              ·
                refine ⟨34000981902823740272897381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22667321268549160181931587 34000981902823740272897381)
                ·
                  refine ⟨6375184106779451301168259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34000981902823740272897381 6375184106779451301168259)
                  ·
                    refine ⟨9562776160169176951752389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375184106779451301168259 9562776160169176951752389)
                    ·
                      refine ⟨1793020530031720678453573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9562776160169176951752389 1793020530031720678453573)
                      ·
                        rfl

theorem cell23_3491895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_3491895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491895 prefixEnd_3491895 := by exact prefixLift 3491895
  have htrace : WordTrace (prefixWord ++ tailWord_3491895) baseStart_3491895 baseEnd_3491895 := by
    simpa [prefixWord, tailWord_3491895, baseEnd_3491895] using wordTrace_append hprefix tailTrace_3491895
  have hstable : (prefixWord ++ tailWord_3491895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491895).length < 2 ^ (prefixWord ++ tailWord_3491895).sum := by decide
  have hdescent : baseEnd_3491895 < baseStart_3491895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491926 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3491926 : Nat := 118140960795 + 3491926 * 2 ^ 59
def prefixEnd_3491926 : Nat := 4983230072969 + 3 ^ 40 * 3491926 * 2
def baseEnd_3491926 : Nat := 597678815977336685721977

theorem tailTrace_3491926 : CollatzResearch.WordTrace tailWord_3491926 prefixEnd_3491926 597678815977336685721977 := by
  unfold tailWord_3491926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960062771709746895386977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84907336231570633550794421 7960062771709746895386977)
  ·
    refine ⟨5970047078782310171540233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7960062771709746895386977 5970047078782310171540233)
    ·
      refine ⟨4477535309086732628655175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5970047078782310171540233 4477535309086732628655175)
      ·
        refine ⟨6716302963630098942982763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477535309086732628655175 6716302963630098942982763)
        ·
          refine ⟨10074454445445148414474145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716302963630098942982763 10074454445445148414474145)
          ·
            refine ⟨7555840834083861310855609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10074454445445148414474145 7555840834083861310855609)
            ·
              refine ⟨5666880625562895983141707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555840834083861310855609 5666880625562895983141707)
              ·
                refine ⟨8500320938344343974712561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666880625562895983141707 8500320938344343974712561)
                ·
                  refine ⟨6375240703758257981034421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8500320938344343974712561 6375240703758257981034421)
                  ·
                    refine ⟨597678815977336685721977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6375240703758257981034421 597678815977336685721977)
                    ·
                      rfl

theorem cell23_3491926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3491926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491926 prefixEnd_3491926 := by exact prefixLift 3491926
  have htrace : WordTrace (prefixWord ++ tailWord_3491926) baseStart_3491926 baseEnd_3491926 := by
    simpa [prefixWord, tailWord_3491926, baseEnd_3491926] using wordTrace_append hprefix tailTrace_3491926
  have hstable : (prefixWord ++ tailWord_3491926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491926).length < 2 ^ (prefixWord ++ tailWord_3491926).sum := by decide
  have hdescent : baseEnd_3491926 < baseStart_3491926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491952 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 6]
def baseStart_3491952 : Nat := 118140960795 + 3491952 * 2 ^ 59
def prefixEnd_3491952 : Nat := 4983230072969 + 3 ^ 40 * 3491952 * 2
def baseEnd_3491952 : Nat := 199227755381002995048979

theorem tailTrace_3491952 : CollatzResearch.WordTrace tailWord_3491952 prefixEnd_3491952 199227755381002995048979 := by
  unfold tailWord_3491952
  simp only [CollatzResearch.WordTrace]
  refine ⟨63680976322630878383319055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84907968430174504511092073 63680976322630878383319055)
  ·
    refine ⟨95521464483946317574978583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63680976322630878383319055 95521464483946317574978583)
    ·
      refine ⟨143282196725919476362467875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95521464483946317574978583 143282196725919476362467875)
      ·
        refine ⟨214923295088879214543701813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143282196725919476362467875 214923295088879214543701813)
        ·
          refine ⟨20149058914582426363472045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214923295088879214543701813 20149058914582426363472045)
          ·
            refine ⟨7555897092968409886302017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20149058914582426363472045 7555897092968409886302017)
            ·
              refine ⟨5666922819726307414726513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555897092968409886302017 5666922819726307414726513)
              ·
                refine ⟨4250192114794730561044885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5666922819726307414726513 4250192114794730561044885)
                ·
                  refine ⟨199227755381002995048979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4250192114794730561044885 199227755381002995048979)
                  ·
                    rfl

theorem cell23_3491952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_3491952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491952 prefixEnd_3491952 := by exact prefixLift 3491952
  have htrace : WordTrace (prefixWord ++ tailWord_3491952) baseStart_3491952 baseEnd_3491952 := by
    simpa [prefixWord, tailWord_3491952, baseEnd_3491952] using wordTrace_append hprefix tailTrace_3491952
  have hstable : (prefixWord ++ tailWord_3491952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491952).length < 2 ^ (prefixWord ++ tailWord_3491952).sum := by decide
  have hdescent : baseEnd_3491952 < baseStart_3491952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491962 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_3491962 : Nat := 118140960795 + 3491962 * 2 ^ 59
def prefixEnd_3491962 : Nat := 4983230072969 + 3 ^ 40 * 3491962 * 2
def baseEnd_3491962 : Nat := 1793054933235571916315765

theorem tailTrace_3491962 : CollatzResearch.WordTrace tailWord_3491962 prefixEnd_3491962 1793054933235571916315765 := by
  unfold tailWord_3491962
  simp only [CollatzResearch.WordTrace]
  refine ⟨31840579343806382118625535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84908211583483685649668093 31840579343806382118625535)
  ·
    refine ⟨47760869015709573177938303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31840579343806382118625535 47760869015709573177938303)
    ·
      refine ⟨71641303523564359766907455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47760869015709573177938303 71641303523564359766907455)
      ·
        refine ⟨107461955285346539650361183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71641303523564359766907455 107461955285346539650361183)
        ·
          refine ⟨161192932928019809475541775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107461955285346539650361183 161192932928019809475541775)
          ·
            refine ⟨241789399392029714213312663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161192932928019809475541775 241789399392029714213312663)
            ·
              refine ⟨362684099088044571319968995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241789399392029714213312663 362684099088044571319968995)
              ·
                refine ⟨544026148632066856979953493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362684099088044571319968995 544026148632066856979953493)
                ·
                  refine ⟨3187653214641016740116915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 544026148632066856979953493 3187653214641016740116915)
                  ·
                    refine ⟨4781479821961525110175373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3187653214641016740116915 4781479821961525110175373)
                    ·
                      refine ⟨1793054933235571916315765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4781479821961525110175373 1793054933235571916315765)
                      ·
                        rfl

theorem cell23_3491962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_3491962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491962 prefixEnd_3491962 := by exact prefixLift 3491962
  have htrace : WordTrace (prefixWord ++ tailWord_3491962) baseStart_3491962 baseEnd_3491962 := by
    simpa [prefixWord, tailWord_3491962, baseEnd_3491962] using wordTrace_append hprefix tailTrace_3491962
  have hstable : (prefixWord ++ tailWord_3491962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491962).length < 2 ^ (prefixWord ++ tailWord_3491962).sum := by decide
  have hdescent : baseEnd_3491962 < baseStart_3491962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491995 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 1, 6]
def baseStart_3491995 : Nat := 118140960795 + 3491995 * 2 ^ 59
def prefixEnd_3491995 : Nat := 4983230072969 + 3 ^ 40 * 3491995 * 2
def baseEnd_3491995 : Nat := 597690626032390095734371

theorem tailTrace_3491995 : CollatzResearch.WordTrace tailWord_3491995 prefixEnd_3491995 597690626032390095734371 := by
  unfold tailWord_3491995
  simp only [CollatzResearch.WordTrace]
  refine ⟨127363520984105975110453439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84909013989403983406968959 127363520984105975110453439)
  ·
    refine ⟨191045281476158962665680159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127363520984105975110453439 191045281476158962665680159)
    ·
      refine ⟨286567922214238443998520239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191045281476158962665680159 286567922214238443998520239)
      ·
        refine ⟨429851883321357665997780359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286567922214238443998520239 429851883321357665997780359)
        ·
          refine ⟨644777824982036498996670539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429851883321357665997780359 644777824982036498996670539)
          ·
            refine ⟨967166737473054748495005809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644777824982036498996670539 967166737473054748495005809)
            ·
              refine ⟨725375053104791061371254357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967166737473054748495005809 725375053104791061371254357)
              ·
                refine ⟨8500488903571770250444387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 725375053104791061371254357 8500488903571770250444387)
                ·
                  refine ⟨12750733355357655375666581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500488903571770250444387 12750733355357655375666581)
                  ·
                    refine ⟨597690626032390095734371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12750733355357655375666581 597690626032390095734371)
                    ·
                      rfl

theorem cell23_3491995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 6].length) (baseStart_3491995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491995 prefixEnd_3491995 := by exact prefixLift 3491995
  have htrace : WordTrace (prefixWord ++ tailWord_3491995) baseStart_3491995 baseEnd_3491995 := by
    simpa [prefixWord, tailWord_3491995, baseEnd_3491995] using wordTrace_append hprefix tailTrace_3491995
  have hstable : (prefixWord ++ tailWord_3491995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491995).length < 2 ^ (prefixWord ++ tailWord_3491995).sum := by decide
  have hdescent : baseEnd_3491995 < baseStart_3491995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3491999 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 1, 5]
def baseStart_3491999 : Nat := 118140960795 + 3491999 * 2 ^ 59
def prefixEnd_3491999 : Nat := 4983230072969 + 3 ^ 40 * 3491999 * 2
def baseEnd_3491999 : Nat := 597691310673262757184365

theorem tailTrace_3491999 : CollatzResearch.WordTrace tailWord_3491999 prefixEnd_3491999 597691310673262757184365 := by
  unfold tailWord_3491999
  simp only [CollatzResearch.WordTrace]
  refine ⟨127363666876091483793599051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84909111250727655862399367 127363666876091483793599051)
  ·
    refine ⟨191045500314137225690398577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127363666876091483793599051 191045500314137225690398577)
    ·
      refine ⟨143284125235602919267798933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191045500314137225690398577 143284125235602919267798933)
      ·
        refine ⟨6716443370418886840678075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143284125235602919267798933 6716443370418886840678075)
        ·
          refine ⟨10074665055628330261017113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716443370418886840678075 10074665055628330261017113)
          ·
            refine ⟨7555998791721247695762835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10074665055628330261017113 7555998791721247695762835)
            ·
              refine ⟨11333998187581871543644253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555998791721247695762835 11333998187581871543644253)
              ·
                refine ⟨4250249320343201828866595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11333998187581871543644253 4250249320343201828866595)
                ·
                  refine ⟨6375373980514802743299893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250249320343201828866595 6375373980514802743299893)
                  ·
                    refine ⟨597691310673262757184365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6375373980514802743299893 597691310673262757184365)
                    ·
                      rfl

theorem cell23_3491999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_3491999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3491999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3491999 prefixEnd_3491999 := by exact prefixLift 3491999
  have htrace : WordTrace (prefixWord ++ tailWord_3491999) baseStart_3491999 baseEnd_3491999 := by
    simpa [prefixWord, tailWord_3491999, baseEnd_3491999] using wordTrace_append hprefix tailTrace_3491999
  have hstable : (prefixWord ++ tailWord_3491999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3491999).length < 2 ^ (prefixWord ++ tailWord_3491999).sum := by decide
  have hdescent : baseEnd_3491999 < baseStart_3491999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3491999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492013 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_3492013 : Nat := 118140960795 + 3492013 * 2 ^ 59
def prefixEnd_3492013 : Nat := 4983230072969 + 3 ^ 40 * 3492013 * 2
def baseEnd_3492013 : Nat := 1793081120748951216778031

theorem tailTrace_3492013 : CollatzResearch.WordTrace tailWord_3492013 prefixEnd_3492013 1793081120748951216778031 := by
  unfold tailWord_3492013
  simp only [CollatzResearch.WordTrace]
  refine ⟨127364177498040764184608693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84909451665360509456405795 127364177498040764184608693)
  ·
    refine ⟨11940391640441321642307065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127364177498040764184608693 11940391640441321642307065)
    ·
      refine ⟨8955293730330991231730299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11940391640441321642307065 8955293730330991231730299)
      ·
        refine ⟨13432940595496486847595449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8955293730330991231730299 13432940595496486847595449)
        ·
          refine ⟨10074705446622365135696587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13432940595496486847595449 10074705446622365135696587)
          ·
            refine ⟨15112058169933547703544881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074705446622365135696587 15112058169933547703544881)
            ·
              refine ⟨11334043627450160777658661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15112058169933547703544881 11334043627450160777658661)
              ·
                refine ⟨2125133180146905145810999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11334043627450160777658661 2125133180146905145810999)
                ·
                  refine ⟨3187699770220357718716499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125133180146905145810999 3187699770220357718716499)
                  ·
                    refine ⟨4781549655330536578074749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3187699770220357718716499 4781549655330536578074749)
                    ·
                      refine ⟨1793081120748951216778031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4781549655330536578074749 1793081120748951216778031)
                      ·
                        rfl

theorem cell23_3492013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_3492013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492013 prefixEnd_3492013 := by exact prefixLift 3492013
  have htrace : WordTrace (prefixWord ++ tailWord_3492013) baseStart_3492013 baseEnd_3492013 := by
    simpa [prefixWord, tailWord_3492013, baseEnd_3492013] using wordTrace_append hprefix tailTrace_3492013
  have hstable : (prefixWord ++ tailWord_3492013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492013).length < 2 ^ (prefixWord ++ tailWord_3492013).sum := by decide
  have hdescent : baseEnd_3492013 < baseStart_3492013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492015 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_3492015 : Nat := 118140960795 + 3492015 * 2 ^ 59
def prefixEnd_3492015 : Nat := 4983230072969 + 3 ^ 40 * 3492015 * 2
def baseEnd_3492015 : Nat := 1793082147710260208953021

theorem tailTrace_3492015 : CollatzResearch.WordTrace tailWord_3492015 prefixEnd_3492015 1793082147710260208953021 := by
  unfold tailWord_3492015
  simp only [CollatzResearch.WordTrace]
  refine ⟨127364250444033518526181499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84909500296022345684120999 127364250444033518526181499)
  ·
    refine ⟨191046375666050277789272249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127364250444033518526181499 191046375666050277789272249)
    ·
      refine ⟨143284781749537708341954187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191046375666050277789272249 143284781749537708341954187)
      ·
        refine ⟨214927172624306562512931281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143284781749537708341954187 214927172624306562512931281)
        ·
          refine ⟨161195379468229921884698461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214927172624306562512931281 161195379468229921884698461)
          ·
            refine ⟨60448267300586220706761923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161195379468229921884698461 60448267300586220706761923)
            ·
              refine ⟨90672400950879331060142885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60448267300586220706761923 90672400950879331060142885)
              ·
                refine ⟨17001075178289874573776791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90672400950879331060142885 17001075178289874573776791)
                ·
                  refine ⟨25501612767434811860665187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17001075178289874573776791 25501612767434811860665187)
                  ·
                    refine ⟨38252419151152217790997781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25501612767434811860665187 38252419151152217790997781)
                    ·
                      refine ⟨1793082147710260208953021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38252419151152217790997781 1793082147710260208953021)
                      ·
                        rfl

theorem cell23_3492015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_3492015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492015 prefixEnd_3492015 := by exact prefixLift 3492015
  have htrace : WordTrace (prefixWord ++ tailWord_3492015) baseStart_3492015 baseEnd_3492015 := by
    simpa [prefixWord, tailWord_3492015, baseEnd_3492015] using wordTrace_append hprefix tailTrace_3492015
  have hstable : (prefixWord ++ tailWord_3492015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492015).length < 2 ^ (prefixWord ++ tailWord_3492015).sum := by decide
  have hdescent : baseEnd_3492015 < baseStart_3492015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492020 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 6]
def baseStart_3492020 : Nat := 118140960795 + 3492020 * 2 ^ 59
def prefixEnd_3492020 : Nat := 4983230072969 + 3 ^ 40 * 3492020 * 2
def baseEnd_3492020 : Nat := 199231635012614743265611

theorem tailTrace_3492020 : CollatzResearch.WordTrace tailWord_3492020 prefixEnd_3492020 199231635012614743265611 := by
  unfold tailWord_3492020
  simp only [CollatzResearch.WordTrace]
  refine ⟨63682216404507702190056757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84909621872676936253409009 63682216404507702190056757)
  ·
    refine ⟨5970207787922597080317821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63682216404507702190056757 5970207787922597080317821)
    ·
      refine ⟨2238827920470973905119183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5970207787922597080317821 2238827920470973905119183)
      ·
        refine ⟨3358241880706460857678775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238827920470973905119183 3358241880706460857678775)
        ·
          refine ⟨5037362821059691286518163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358241880706460857678775 5037362821059691286518163)
          ·
            refine ⟨7556044231589536929777245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037362821059691286518163 7556044231589536929777245)
            ·
              refine ⟨2833516586846076348666467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7556044231589536929777245 2833516586846076348666467)
              ·
                refine ⟨4250274880269114522999701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833516586846076348666467 4250274880269114522999701)
                ·
                  refine ⟨199231635012614743265611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4250274880269114522999701 199231635012614743265611)
                  ·
                    rfl

theorem cell23_3492020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_3492020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492020 prefixEnd_3492020 := by exact prefixLift 3492020
  have htrace : WordTrace (prefixWord ++ tailWord_3492020) baseStart_3492020 baseEnd_3492020 := by
    simpa [prefixWord, tailWord_3492020, baseEnd_3492020] using wordTrace_append hprefix tailTrace_3492020
  have hstable : (prefixWord ++ tailWord_3492020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492020).length < 2 ^ (prefixWord ++ tailWord_3492020).sum := by decide
  have hdescent : baseEnd_3492020 < baseStart_3492020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492025 : List Nat := [1, 2, 1, 4, 1, 2, 2, 10]
def baseStart_3492025 : Nat := 118140960795 + 3492025 * 2 ^ 59
def prefixEnd_3492025 : Nat := 4983230072969 + 3 ^ 40 * 3492025 * 2
def baseEnd_3492025 : Nat := 66410640093215006289925

theorem tailTrace_3492025 : CollatzResearch.WordTrace tailWord_3492025 prefixEnd_3492025 66410640093215006289925 := by
  unfold tailWord_3492025
  simp only [CollatzResearch.WordTrace]
  refine ⟨127364615173997290234045529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84909743449331526822697019 127364615173997290234045529)
  ·
    refine ⟨95523461380497967675534147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127364615173997290234045529 95523461380497967675534147)
    ·
      refine ⟨143285192070746951513301221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95523461380497967675534147 143285192070746951513301221)
      ·
        refine ⟨26865973513265053408743979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143285192070746951513301221 26865973513265053408743979)
        ·
          refine ⟨40298960269897580113115969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26865973513265053408743979 40298960269897580113115969)
          ·
            refine ⟨30224220202423185084836977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40298960269897580113115969 30224220202423185084836977)
            ·
              refine ⟨22668165151817388813627733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30224220202423185084836977 22668165151817388813627733)
              ·
                refine ⟨66410640093215006289925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22668165151817388813627733 66410640093215006289925)
                ·
                  rfl

theorem cell23_3492025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 10].length) (baseStart_3492025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492025 prefixEnd_3492025 := by exact prefixLift 3492025
  have htrace : WordTrace (prefixWord ++ tailWord_3492025) baseStart_3492025 baseEnd_3492025 := by
    simpa [prefixWord, tailWord_3492025, baseEnd_3492025] using wordTrace_append hprefix tailTrace_3492025
  have hstable : (prefixWord ++ tailWord_3492025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492025).length < 2 ^ (prefixWord ++ tailWord_3492025).sum := by decide
  have hdescent : baseEnd_3492025 < baseStart_3492025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492032 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_3492032 : Nat := 118140960795 + 3492032 * 2 ^ 59
def prefixEnd_3492032 : Nat := 4983230072969 + 3 ^ 40 * 3492032 * 2
def baseEnd_3492032 : Nat := 1793090876881386642440443

theorem tailTrace_3492032 : CollatzResearch.WordTrace tailWord_3492032 prefixEnd_3492032 1793090876881386642440443 := by
  unfold tailWord_3492032
  simp only [CollatzResearch.WordTrace]
  refine ⟨63682435242485965214775175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84909913656647953619700233 63682435242485965214775175)
  ·
    refine ⟨95523652863728947822162763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63682435242485965214775175 95523652863728947822162763)
    ·
      refine ⟨143285479295593421733244145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95523652863728947822162763 143285479295593421733244145)
      ·
        refine ⟨107464109471695066299933109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143285479295593421733244145 107464109471695066299933109)
        ·
          refine ⟨10074760262971412465618729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107464109471695066299933109 10074760262971412465618729)
          ·
            refine ⟨7556070197228559349214047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10074760262971412465618729 7556070197228559349214047)
            ·
              refine ⟨11334105295842839023821071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7556070197228559349214047 11334105295842839023821071)
              ·
                refine ⟨17001157943764258535731607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11334105295842839023821071 17001157943764258535731607)
                ·
                  refine ⟨25501736915646387803597411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17001157943764258535731607 25501736915646387803597411)
                  ·
                    refine ⟨38252605373469581705396117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25501736915646387803597411 38252605373469581705396117)
                    ·
                      refine ⟨1793090876881386642440443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38252605373469581705396117 1793090876881386642440443)
                      ·
                        rfl

theorem cell23_3492032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_3492032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492032 prefixEnd_3492032 := by exact prefixLift 3492032
  have htrace : WordTrace (prefixWord ++ tailWord_3492032) baseStart_3492032 baseEnd_3492032 := by
    simpa [prefixWord, tailWord_3492032, baseEnd_3492032] using wordTrace_append hprefix tailTrace_3492032
  have hstable : (prefixWord ++ tailWord_3492032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492032).length < 2 ^ (prefixWord ++ tailWord_3492032).sum := by decide
  have hdescent : baseEnd_3492032 < baseStart_3492032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492036 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3492036 : Nat := 118140960795 + 3492036 * 2 ^ 59
def prefixEnd_3492036 : Nat := 4983230072969 + 3 ^ 40 * 3492036 * 2
def baseEnd_3492036 : Nat := 1793092930804004626790425

theorem tailTrace_3492036 : CollatzResearch.WordTrace tailWord_3492036 prefixEnd_3492036 1793092930804004626790425 := by
  unfold tailWord_3492036
  simp only [CollatzResearch.WordTrace]
  refine ⟨63682508188478719556347981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84910010917971626075130641 63682508188478719556347981)
  ·
    refine ⟨23880940570679519833630493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63682508188478719556347981 23880940570679519833630493)
    ·
      refine ⟨8955352714004819937611435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23880940570679519833630493 8955352714004819937611435)
      ·
        refine ⟨13433029071007229906417153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8955352714004819937611435 13433029071007229906417153)
        ·
          refine ⟨10074771803255422429812865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13433029071007229906417153 10074771803255422429812865)
          ·
            refine ⟨7556078852441566822359649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10074771803255422429812865 7556078852441566822359649)
            ·
              refine ⟨5667059139331175116769737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7556078852441566822359649 5667059139331175116769737)
              ·
                refine ⟨4250294354498381337577303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667059139331175116769737 4250294354498381337577303)
                ·
                  refine ⟨6375441531747572006365955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250294354498381337577303 6375441531747572006365955)
                  ·
                    refine ⟨9563162297621358009548933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375441531747572006365955 9563162297621358009548933)
                    ·
                      refine ⟨1793092930804004626790425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9563162297621358009548933 1793092930804004626790425)
                      ·
                        rfl

theorem cell23_3492036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3492036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492036 prefixEnd_3492036 := by exact prefixLift 3492036
  have htrace : WordTrace (prefixWord ++ tailWord_3492036) baseStart_3492036 baseEnd_3492036 := by
    simpa [prefixWord, tailWord_3492036, baseEnd_3492036] using wordTrace_append hprefix tailTrace_3492036
  have hstable : (prefixWord ++ tailWord_3492036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492036).length < 2 ^ (prefixWord ++ tailWord_3492036).sum := by decide
  have hdescent : baseEnd_3492036 < baseStart_3492036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492055 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 9]
def baseStart_3492055 : Nat := 118140960795 + 3492055 * 2 ^ 59
def prefixEnd_3492055 : Nat := 4983230072969 + 3 ^ 40 * 3492055 * 2
def baseEnd_3492055 : Nat := 597700895645480017484279

theorem tailTrace_3492055 : CollatzResearch.WordTrace tailWord_3492055 prefixEnd_3492055 597700895645480017484279 := by
  unfold tailWord_3492055
  simp only [CollatzResearch.WordTrace]
  refine ⟨127365709363888605357637619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84910472909259070238425079 127365709363888605357637619)
  ·
    refine ⟨191048564045832908036456429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127365709363888605357637619 191048564045832908036456429)
    ·
      refine ⟨71643211517187340513671161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191048564045832908036456429 71643211517187340513671161)
      ·
        refine ⟨53732408637890505385253371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71643211517187340513671161 53732408637890505385253371)
        ·
          refine ⟨80598612956835758077880057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53732408637890505385253371 80598612956835758077880057)
          ·
            refine ⟨60448959717626818558410043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80598612956835758077880057 60448959717626818558410043)
            ·
              refine ⟨90673439576440227837615065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60448959717626818558410043 90673439576440227837615065)
              ·
                refine ⟨68005079682330170878211299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90673439576440227837615065 68005079682330170878211299)
                ·
                  refine ⟨102007619523495256317316949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68005079682330170878211299 102007619523495256317316949)
                  ·
                    refine ⟨597700895645480017484279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 102007619523495256317316949 597700895645480017484279)
                    ·
                      rfl

theorem cell23_3492055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_3492055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492055 prefixEnd_3492055 := by exact prefixLift 3492055
  have htrace : WordTrace (prefixWord ++ tailWord_3492055) baseStart_3492055 baseEnd_3492055 := by
    simpa [prefixWord, tailWord_3492055, baseEnd_3492055] using wordTrace_append hprefix tailTrace_3492055
  have hstable : (prefixWord ++ tailWord_3492055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492055).length < 2 ^ (prefixWord ++ tailWord_3492055).sum := by decide
  have hdescent : baseEnd_3492055 < baseStart_3492055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492096 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 1, 3, 2]
def baseStart_3492096 : Nat := 118140960795 + 3492096 * 2 ^ 59
def prefixEnd_3492096 : Nat := 4983230072969 + 3 ^ 40 * 3492096 * 2
def baseEnd_3492096 : Nat := 1793123739643274392040149

theorem tailTrace_3492096 : CollatzResearch.WordTrace tailWord_3492096 prefixEnd_3492096 1793123739643274392040149 := by
  unfold tailWord_3492096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63683602378370034679940071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84911469837826712906586761 63683602378370034679940071)
  ·
    refine ⟨95525403567555052019910107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63683602378370034679940071 95525403567555052019910107)
    ·
      refine ⟨143288105351332578029865161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95525403567555052019910107 143288105351332578029865161)
      ·
        refine ⟨107466079013499433522398871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143288105351332578029865161 107466079013499433522398871)
        ·
          refine ⟨161199118520249150283598307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107466079013499433522398871 161199118520249150283598307)
          ·
            refine ⟨241798677780373725425397461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161199118520249150283598307 241798677780373725425397461)
            ·
              refine ⟨5667156510477509189657753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 241798677780373725425397461 5667156510477509189657753)
              ·
                refine ⟨4250367382858131892243315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667156510477509189657753 4250367382858131892243315)
                ·
                  refine ⟨6375551074287197838364973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250367382858131892243315 6375551074287197838364973)
                  ·
                    refine ⟨2390831652857699189386865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6375551074287197838364973 2390831652857699189386865)
                    ·
                      refine ⟨1793123739643274392040149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2390831652857699189386865 1793123739643274392040149)
                      ·
                        rfl

theorem cell23_3492096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_3492096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492096 prefixEnd_3492096 := by exact prefixLift 3492096
  have htrace : WordTrace (prefixWord ++ tailWord_3492096) baseStart_3492096 baseEnd_3492096 := by
    simpa [prefixWord, tailWord_3492096, baseEnd_3492096] using wordTrace_append hprefix tailTrace_3492096
  have hstable : (prefixWord ++ tailWord_3492096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492096).length < 2 ^ (prefixWord ++ tailWord_3492096).sum := by decide
  have hdescent : baseEnd_3492096 < baseStart_3492096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492113 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 1, 3, 2]
def baseStart_3492113 : Nat := 118140960795 + 3492113 * 2 ^ 59
def prefixEnd_3492113 : Nat := 4983230072969 + 3 ^ 40 * 3492113 * 2
def baseEnd_3492113 : Nat := 1793132468814400825527571

theorem tailTrace_3492113 : CollatzResearch.WordTrace tailWord_3492113 prefixEnd_3492113 1793132468814400825527571 := by
  unfold tailWord_3492113
  simp only [CollatzResearch.WordTrace]
  refine ⟨127367824797678481263248993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84911883198452320842165995 127367824797678481263248993)
  ·
    refine ⟨95525868598258860947436745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127367824797678481263248993 95525868598258860947436745)
    ·
      refine ⟨71644401448694145710577559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95525868598258860947436745 71644401448694145710577559)
      ·
        refine ⟨107466602173041218565866339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71644401448694145710577559 107466602173041218565866339)
        ·
          refine ⟨161199903259561827848799509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107466602173041218565866339 161199903259561827848799509)
          ·
            refine ⟨7556245465291960680412477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161199903259561827848799509 7556245465291960680412477)
            ·
              refine ⟨2833592049484485255154679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7556245465291960680412477 2833592049484485255154679)
              ·
                refine ⟨4250388074226727882732019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833592049484485255154679 4250388074226727882732019)
                ·
                  refine ⟨6375582111340091824098029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250388074226727882732019 6375582111340091824098029)
                  ·
                    refine ⟨2390843291752534434036761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6375582111340091824098029 2390843291752534434036761)
                    ·
                      refine ⟨1793132468814400825527571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2390843291752534434036761 1793132468814400825527571)
                      ·
                        rfl

theorem cell23_3492113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_3492113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492113 prefixEnd_3492113 := by exact prefixLift 3492113
  have htrace : WordTrace (prefixWord ++ tailWord_3492113) baseStart_3492113 baseEnd_3492113 := by
    simpa [prefixWord, tailWord_3492113, baseEnd_3492113] using wordTrace_append hprefix tailTrace_3492113
  have hstable : (prefixWord ++ tailWord_3492113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492113).length < 2 ^ (prefixWord ++ tailWord_3492113).sum := by decide
  have hdescent : baseEnd_3492113 < baseStart_3492113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492126 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3492126 : Nat := 118140960795 + 3492126 * 2 ^ 59
def prefixEnd_3492126 : Nat := 4983230072969 + 3 ^ 40 * 3492126 * 2
def baseEnd_3492126 : Nat := 1793139144062909274665011

theorem tailTrace_3492126 : CollatzResearch.WordTrace tailWord_3492126 prefixEnd_3492126 1793139144062909274665011 := by
  unfold tailWord_3492126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921037368328923060434029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84912199297754256322314821 15921037368328923060434029)
  ·
    refine ⟨5970389013123346147662761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15921037368328923060434029 5970389013123346147662761)
    ·
      refine ⟨4477791759842509610747071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5970389013123346147662761 4477791759842509610747071)
      ·
        refine ⟨6716687639763764416120607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477791759842509610747071 6716687639763764416120607)
        ·
          refine ⟨10075031459645646624180911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716687639763764416120607 10075031459645646624180911)
          ·
            refine ⟨15112547189468469936271367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075031459645646624180911 15112547189468469936271367)
            ·
              refine ⟨22668820784202704904407051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15112547189468469936271367 22668820784202704904407051)
              ·
                refine ⟨34003231176304057356610577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22668820784202704904407051 34003231176304057356610577)
                ·
                  refine ⟨25502423382228043017457933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34003231176304057356610577 25502423382228043017457933)
                  ·
                    refine ⟨9563408768335516131546725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25502423382228043017457933 9563408768335516131546725)
                    ·
                      refine ⟨1793139144062909274665011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9563408768335516131546725 1793139144062909274665011)
                      ·
                        rfl

theorem cell23_3492126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3492126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492126 prefixEnd_3492126 := by exact prefixLift 3492126
  have htrace : WordTrace (prefixWord ++ tailWord_3492126) baseStart_3492126 baseEnd_3492126 := by
    simpa [prefixWord, tailWord_3492126, baseEnd_3492126] using wordTrace_append hprefix tailTrace_3492126
  have hstable : (prefixWord ++ tailWord_3492126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492126).length < 2 ^ (prefixWord ++ tailWord_3492126).sum := by decide
  have hdescent : baseEnd_3492126 < baseStart_3492126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492164 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3492164 : Nat := 118140960795 + 3492164 * 2 ^ 59
def prefixEnd_3492164 : Nat := 4983230072969 + 3 ^ 40 * 3492164 * 2
def baseEnd_3492164 : Nat := 1793158656327780125989837

theorem tailTrace_3492164 : CollatzResearch.WordTrace tailWord_3492164 prefixEnd_3492164 1793158656327780125989837 := by
  unfold tailWord_3492164
  simp only [CollatzResearch.WordTrace]
  refine ⟨63684842460246858486677773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84913123280329144648903697 63684842460246858486677773)
  ·
    refine ⟨23881815922592571932504165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63684842460246858486677773 23881815922592571932504165)
    ·
      refine ⟨4477840485486107237344531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23881815922592571932504165 4477840485486107237344531)
      ·
        refine ⟨6716760728229160856016797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477840485486107237344531 6716760728229160856016797)
        ·
          refine ⟨2518785273085935321006299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6716760728229160856016797 2518785273085935321006299)
          ·
            refine ⟨3778177909628902981509449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518785273085935321006299 3778177909628902981509449)
            ·
              refine ⟨2833633432221677236132087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3778177909628902981509449 2833633432221677236132087)
              ·
                refine ⟨4250450148332515854198131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833633432221677236132087 4250450148332515854198131)
                ·
                  refine ⟨6375675222498773781297197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250450148332515854198131 6375675222498773781297197)
                  ·
                    refine ⟨2390878208437040167986449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6375675222498773781297197 2390878208437040167986449)
                    ·
                      refine ⟨1793158656327780125989837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2390878208437040167986449 1793158656327780125989837)
                      ·
                        rfl

theorem cell23_3492164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3492164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492164 prefixEnd_3492164 := by exact prefixLift 3492164
  have htrace : WordTrace (prefixWord ++ tailWord_3492164) baseStart_3492164 baseEnd_3492164 := by
    simpa [prefixWord, tailWord_3492164, baseEnd_3492164] using wordTrace_append hprefix tailTrace_3492164
  have hstable : (prefixWord ++ tailWord_3492164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492164).length < 2 ^ (prefixWord ++ tailWord_3492164).sum := by decide
  have hdescent : baseEnd_3492164 < baseStart_3492164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492199 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3492199 : Nat := 118140960795 + 3492199 * 2 ^ 59
def prefixEnd_3492199 : Nat := 4983230072969 + 3 ^ 40 * 3492199 * 2
def baseEnd_3492199 : Nat := 1793176628150687489052175

theorem tailTrace_3492199 : CollatzResearch.WordTrace tailWord_3492199 prefixEnd_3492199 1793176628150687489052175 := by
  unfold tailWord_3492199
  simp only [CollatzResearch.WordTrace]
  refine ⟨127370961475366917950879651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84913974316911278633919767 127370961475366917950879651)
  ·
    refine ⟨191056442213050376926319477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127370961475366917950879651 191056442213050376926319477)
    ·
      refine ⟨17911541457473472836842451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191056442213050376926319477 17911541457473472836842451)
      ·
        refine ⟨26867312186210209255263677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911541457473472836842451 26867312186210209255263677)
        ·
          refine ⟨10075242069828828470723879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26867312186210209255263677 10075242069828828470723879)
          ·
            refine ⟨15112863104743242706085819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075242069828828470723879 15112863104743242706085819)
            ·
              refine ⟨22669294657114864059128729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15112863104743242706085819 22669294657114864059128729)
              ·
                refine ⟨17001970992836148044346547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22669294657114864059128729 17001970992836148044346547)
                ·
                  refine ⟨25502956489254222066519821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17001970992836148044346547 25502956489254222066519821)
                  ·
                    refine ⟨9563608683470333274944933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25502956489254222066519821 9563608683470333274944933)
                    ·
                      refine ⟨1793176628150687489052175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9563608683470333274944933 1793176628150687489052175)
                      ·
                        rfl

theorem cell23_3492199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3492199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492199 prefixEnd_3492199 := by exact prefixLift 3492199
  have htrace : WordTrace (prefixWord ++ tailWord_3492199) baseStart_3492199 baseEnd_3492199 := by
    simpa [prefixWord, tailWord_3492199, baseEnd_3492199] using wordTrace_append hprefix tailTrace_3492199
  have hstable : (prefixWord ++ tailWord_3492199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492199).length < 2 ^ (prefixWord ++ tailWord_3492199).sum := by decide
  have hdescent : baseEnd_3492199 < baseStart_3492199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492219 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 3]
def baseStart_3492219 : Nat := 118140960795 + 3492219 * 2 ^ 59
def prefixEnd_3492219 : Nat := 4983230072969 + 3 ^ 40 * 3492219 * 2
def baseEnd_3492219 : Nat := 1793186897763777410802083

theorem tailTrace_3492219 : CollatzResearch.WordTrace tailWord_3492219 prefixEnd_3492219 1793186897763777410802083 := by
  unfold tailWord_3492219
  simp only [CollatzResearch.WordTrace]
  refine ⟨127371690935294461366607711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84914460623529640911071807 127371690935294461366607711)
  ·
    refine ⟨191057536402941692049911567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127371690935294461366607711 191057536402941692049911567)
    ·
      refine ⟨286586304604412538074867351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191057536402941692049911567 286586304604412538074867351)
      ·
        refine ⟨429879456906618807112301027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286586304604412538074867351 429879456906618807112301027)
        ·
          refine ⟨644819185359928210668451541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429879456906618807112301027 644819185359928210668451541)
          ·
            refine ⟨15112949656873317437541833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 644819185359928210668451541 15112949656873317437541833)
            ·
              refine ⟨11334712242654988078156375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15112949656873317437541833 11334712242654988078156375)
              ·
                refine ⟨17002068363982482117234563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11334712242654988078156375 17002068363982482117234563)
                ·
                  refine ⟨25503102545973723175851845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17002068363982482117234563 25503102545973723175851845)
                  ·
                    refine ⟨4781831727370073095472221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25503102545973723175851845 4781831727370073095472221)
                    ·
                      refine ⟨1793186897763777410802083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4781831727370073095472221 1793186897763777410802083)
                      ·
                        rfl

theorem cell23_3492219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 3].length) (baseStart_3492219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492219 prefixEnd_3492219 := by exact prefixLift 3492219
  have htrace : WordTrace (prefixWord ++ tailWord_3492219) baseStart_3492219 baseEnd_3492219 := by
    simpa [prefixWord, tailWord_3492219, baseEnd_3492219] using wordTrace_append hprefix tailTrace_3492219
  have hstable : (prefixWord ++ tailWord_3492219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492219).length < 2 ^ (prefixWord ++ tailWord_3492219).sum := by decide
  have hdescent : baseEnd_3492219 < baseStart_3492219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492236 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3492236 : Nat := 118140960795 + 3492236 * 2 ^ 59
def prefixEnd_3492236 : Nat := 4983230072969 + 3 ^ 40 * 3492236 * 2
def baseEnd_3492236 : Nat := 1793195626934903844289505

theorem tailTrace_3492236 : CollatzResearch.WordTrace tailWord_3492236 prefixEnd_3492236 1793195626934903844289505 := by
  unfold tailWord_3492236
  simp only [CollatzResearch.WordTrace]
  refine ⟨63686155488116436634988281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84914873984155248846651041 63686155488116436634988281)
  ·
    refine ⟨47764616616087327476241211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63686155488116436634988281 47764616616087327476241211)
    ·
      refine ⟨71646924924130991214361817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47764616616087327476241211 71646924924130991214361817)
      ·
        refine ⟨53735193693098243410771363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71646924924130991214361817 53735193693098243410771363)
        ·
          refine ⟨80602790539647365116157045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53735193693098243410771363 80602790539647365116157045)
          ·
            refine ⟨7556511613091940479639723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80602790539647365116157045 7556511613091940479639723)
            ·
              refine ⟨11334767419637910719459585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7556511613091940479639723 11334767419637910719459585)
              ·
                refine ⟨8501075564728433039594689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11334767419637910719459585 8501075564728433039594689)
                ·
                  refine ⟨6375806673546324779696017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8501075564728433039594689 6375806673546324779696017)
                  ·
                    refine ⟨4781855005159743584772013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6375806673546324779696017 4781855005159743584772013)
                    ·
                      refine ⟨1793195626934903844289505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4781855005159743584772013 1793195626934903844289505)
                      ·
                        rfl

theorem cell23_3492236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3492236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492236 prefixEnd_3492236 := by exact prefixLift 3492236
  have htrace : WordTrace (prefixWord ++ tailWord_3492236) baseStart_3492236 baseEnd_3492236 := by
    simpa [prefixWord, tailWord_3492236, baseEnd_3492236] using wordTrace_append hprefix tailTrace_3492236
  have hstable : (prefixWord ++ tailWord_3492236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492236).length < 2 ^ (prefixWord ++ tailWord_3492236).sum := by decide
  have hdescent : baseEnd_3492236 < baseStart_3492236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492256 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 6]
def baseStart_3492256 : Nat := 118140960795 + 3492256 * 2 ^ 59
def prefixEnd_3492256 : Nat := 4983230072969 + 3 ^ 40 * 3492256 * 2
def baseEnd_3492256 : Nat := 199245099616443751782157

theorem tailTrace_3492256 : CollatzResearch.WordTrace tailWord_3492256 prefixEnd_3492256 199245099616443751782157 := by
  unfold tailWord_3492256
  simp only [CollatzResearch.WordTrace]
  refine ⟨63686520218080208342852311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84915360290773611123803081 63686520218080208342852311)
  ·
    refine ⟨95529780327120312514278467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63686520218080208342852311 95529780327120312514278467)
    ·
      refine ⟨143294670490680468771417701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95529780327120312514278467 143294670490680468771417701)
      ·
        refine ⟨26867750717002587894640819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143294670490680468771417701 26867750717002587894640819)
        ·
          refine ⟨40301626075503881841961229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26867750717002587894640819 40301626075503881841961229)
          ·
            refine ⟨15113109778313955690735461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40301626075503881841961229 15113109778313955690735461)
            ·
              refine ⟨2833708083433866692012899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15113109778313955690735461 2833708083433866692012899)
              ·
                refine ⟨4250562125150800038019349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833708083433866692012899 4250562125150800038019349)
                ·
                  refine ⟨199245099616443751782157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4250562125150800038019349 199245099616443751782157)
                  ·
                    rfl

theorem cell23_3492256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 6].length) (baseStart_3492256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492256 prefixEnd_3492256 := by exact prefixLift 3492256
  have htrace : WordTrace (prefixWord ++ tailWord_3492256) baseStart_3492256 baseEnd_3492256 := by
    simpa [prefixWord, tailWord_3492256, baseEnd_3492256] using wordTrace_append hprefix tailTrace_3492256
  have hstable : (prefixWord ++ tailWord_3492256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492256).length < 2 ^ (prefixWord ++ tailWord_3492256).sum := by decide
  have hdescent : baseEnd_3492256 < baseStart_3492256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492286 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3492286 : Nat := 118140960795 + 3492286 * 2 ^ 59
def prefixEnd_3492286 : Nat := 4983230072969 + 3 ^ 40 * 3492286 * 2
def baseEnd_3492286 : Nat := 597740433655876216221425

theorem tailTrace_3492286 : CollatzResearch.WordTrace tailWord_3492286 prefixEnd_3492286 597740433655876216221425 := by
  unfold tailWord_3492286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921766828256466476162089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84916089750701154539531141 15921766828256466476162089)
  ·
    refine ⟨11941325121192349857121567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15921766828256466476162089 11941325121192349857121567)
    ·
      refine ⟨17911987681788524785682351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11941325121192349857121567 17911987681788524785682351)
      ·
        refine ⟨26867981522682787178523527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911987681788524785682351 26867981522682787178523527)
        ·
          refine ⟨40301972284024180767785291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26867981522682787178523527 40301972284024180767785291)
          ·
            refine ⟨60452958426036271151677937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40301972284024180767785291 60452958426036271151677937)
            ·
              refine ⟨45339718819527203363758453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60452958426036271151677937 45339718819527203363758453)
              ·
                refine ⟨4250598639330675315352355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45339718819527203363758453 4250598639330675315352355)
                ·
                  refine ⟨6375897958996012973028533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250598639330675315352355 6375897958996012973028533)
                  ·
                    refine ⟨597740433655876216221425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6375897958996012973028533 597740433655876216221425)
                    ·
                      rfl

theorem cell23_3492286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3492286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492286 prefixEnd_3492286 := by exact prefixLift 3492286
  have htrace : WordTrace (prefixWord ++ tailWord_3492286) baseStart_3492286 baseEnd_3492286 := by
    simpa [prefixWord, tailWord_3492286, baseEnd_3492286] using wordTrace_append hprefix tailTrace_3492286
  have hstable : (prefixWord ++ tailWord_3492286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492286).length < 2 ^ (prefixWord ++ tailWord_3492286).sum := by decide
  have hdescent : baseEnd_3492286 < baseStart_3492286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492389 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_3492389 : Nat := 118140960795 + 3492389 * 2 ^ 59
def prefixEnd_3492389 : Nat := 4983230072969 + 3 ^ 40 * 3492389 * 2
def baseEnd_3492389 : Nat := 597758063158347248558767

theorem tailTrace_3492389 : CollatzResearch.WordTrace tailWord_3492389 prefixEnd_3492389 597758063158347248558767 := by
  unfold tailWord_3492389
  simp only [CollatzResearch.WordTrace]
  refine ⟨127377891344678580400296221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84918594229785720266864147 127377891344678580400296221)
  ·
    refine ⟨47766709254254467650111083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127377891344678580400296221 47766709254254467650111083)
    ·
      refine ⟨71650063881381701475166625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47766709254254467650111083 71650063881381701475166625)
      ·
        refine ⟨53737547911036276106374969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71650063881381701475166625 53737547911036276106374969)
        ·
          refine ⟨40303160933277207079781227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53737547911036276106374969 40303160933277207079781227)
          ·
            refine ⟨60454741399915810619671841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40303160933277207079781227 60454741399915810619671841)
            ·
              refine ⟨45341056049936857964753881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60454741399915810619671841 45341056049936857964753881)
              ·
                refine ⟨34005792037452643473565411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45341056049936857964753881 34005792037452643473565411)
                ·
                  refine ⟨51008688056178965210348117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34005792037452643473565411 51008688056178965210348117)
                  ·
                    refine ⟨597758063158347248558767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51008688056178965210348117 597758063158347248558767)
                    ·
                      rfl

theorem cell23_3492389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_3492389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492389 prefixEnd_3492389 := by exact prefixLift 3492389
  have htrace : WordTrace (prefixWord ++ tailWord_3492389) baseStart_3492389 baseEnd_3492389 := by
    simpa [prefixWord, tailWord_3492389, baseEnd_3492389] using wordTrace_append hprefix tailTrace_3492389
  have hstable : (prefixWord ++ tailWord_3492389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492389).length < 2 ^ (prefixWord ++ tailWord_3492389).sum := by decide
  have hdescent : baseEnd_3492389 < baseStart_3492389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492397 : List Nat := [1, 5, 4, 1, 2, 1, 9]
def baseStart_3492397 : Nat := 118140960795 + 3492397 * 2 ^ 59
def prefixEnd_3492397 : Nat := 4983230072969 + 3 ^ 40 * 3492397 * 2
def baseEnd_3492397 : Nat := 22139238238521947091065

theorem tailTrace_3492397 : CollatzResearch.WordTrace tailWord_3492397 prefixEnd_3492397 22139238238521947091065 := by
  unfold tailWord_3492397
  simp only [CollatzResearch.WordTrace]
  refine ⟨127378183128649597766587445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84918788752433065177724963 127378183128649597766587445)
  ·
    refine ⟨11941704668310899790617573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127378183128649597766587445 11941704668310899790617573)
    ·
      refine ⟨2239069625308293710740795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11941704668310899790617573 2239069625308293710740795)
      ·
        refine ⟨3358604437962440566111193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239069625308293710740795 3358604437962440566111193)
        ·
          refine ⟨2518953328471830424583395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3358604437962440566111193 2518953328471830424583395)
          ·
            refine ⟨3778429992707745636875093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518953328471830424583395 3778429992707745636875093)
            ·
              refine ⟨22139238238521947091065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3778429992707745636875093 22139238238521947091065)
              ·
                rfl

theorem cell23_3492397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 9].length) (baseStart_3492397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492397 prefixEnd_3492397 := by exact prefixLift 3492397
  have htrace : WordTrace (prefixWord ++ tailWord_3492397) baseStart_3492397 baseEnd_3492397 := by
    simpa [prefixWord, tailWord_3492397, baseEnd_3492397] using wordTrace_append hprefix tailTrace_3492397
  have hstable : (prefixWord ++ tailWord_3492397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492397).length < 2 ^ (prefixWord ++ tailWord_3492397).sum := by decide
  have hdescent : baseEnd_3492397 < baseStart_3492397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492473 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 2, 5, 2]
def baseStart_3492473 : Nat := 118140960795 + 3492473 * 2 ^ 59
def prefixEnd_3492473 : Nat := 4983230072969 + 3 ^ 40 * 3492473 * 2
def baseEnd_3492473 : Nat := 1793317321850019417025915

theorem tailTrace_3492473 : CollatzResearch.WordTrace tailWord_3492473 prefixEnd_3492473 1793317321850019417025915 := by
  unfold tailWord_3492473
  simp only [CollatzResearch.WordTrace]
  refine ⟨127380955076374262746354073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84920636717582841830902715 127380955076374262746354073)
  ·
    refine ⟨95535716307280697059765555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127380955076374262746354073 95535716307280697059765555)
    ·
      refine ⟨143303574460921045589648333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95535716307280697059765555 143303574460921045589648333)
      ·
        refine ⟨53738840422845392096118125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143303574460921045589648333 53738840422845392096118125)
        ·
          refine ⟨20152065158567022036044297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53738840422845392096118125 20152065158567022036044297)
          ·
            refine ⟨15114048868925266527033223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20152065158567022036044297 15114048868925266527033223)
            ·
              refine ⟨22671073303387899790549835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114048868925266527033223 22671073303387899790549835)
              ·
                refine ⟨34006609955081849685824753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22671073303387899790549835 34006609955081849685824753)
                ·
                  refine ⟨25504957466311387264368565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34006609955081849685824753 25504957466311387264368565)
                  ·
                    refine ⟨2391089762466692556034553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25504957466311387264368565 2391089762466692556034553)
                    ·
                      refine ⟨1793317321850019417025915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391089762466692556034553 1793317321850019417025915)
                      ·
                        rfl

theorem cell23_3492473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_3492473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492473 prefixEnd_3492473 := by exact prefixLift 3492473
  have htrace : WordTrace (prefixWord ++ tailWord_3492473) baseStart_3492473 baseEnd_3492473 := by
    simpa [prefixWord, tailWord_3492473, baseEnd_3492473] using wordTrace_append hprefix tailTrace_3492473
  have hstable : (prefixWord ++ tailWord_3492473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492473).length < 2 ^ (prefixWord ++ tailWord_3492473).sum := by decide
  have hdescent : baseEnd_3492473 < baseStart_3492473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492476 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3492476 : Nat := 118140960795 + 3492476 * 2 ^ 59
def prefixEnd_3492476 : Nat := 4983230072969 + 3 ^ 40 * 3492476 * 2
def baseEnd_3492476 : Nat := 1793318862291982905288401

theorem tailTrace_3492476 : CollatzResearch.WordTrace tailWord_3492476 prefixEnd_3492476 1793318862291982905288401 := by
  unfold tailWord_3492476
  simp only [CollatzResearch.WordTrace]
  refine ⟨63690532247681697129356641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84920709663575596172475521 63690532247681697129356641)
  ·
    refine ⟨47767899185761272847017481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63690532247681697129356641 47767899185761272847017481)
    ·
      refine ⟨35825924389320954635263111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47767899185761272847017481 35825924389320954635263111)
      ·
        refine ⟨53738886583981431952894667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35825924389320954635263111 53738886583981431952894667)
        ·
          refine ⟨80608329875972147929342001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53738886583981431952894667 80608329875972147929342001)
          ·
            refine ⟨60456247406979110947006501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80608329875972147929342001 60456247406979110947006501)
            ·
              refine ⟨11335546388808583302563719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60456247406979110947006501 11335546388808583302563719)
              ·
                refine ⟨17003319583212874953845579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11335546388808583302563719 17003319583212874953845579)
                ·
                  refine ⟨25504979374819312430768369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17003319583212874953845579 25504979374819312430768369)
                  ·
                    refine ⟨19128734531114484323076277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25504979374819312430768369 19128734531114484323076277)
                    ·
                      refine ⟨1793318862291982905288401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19128734531114484323076277 1793318862291982905288401)
                      ·
                        rfl

theorem cell23_3492476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3492476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492476 prefixEnd_3492476 := by exact prefixLift 3492476
  have htrace : WordTrace (prefixWord ++ tailWord_3492476) baseStart_3492476 baseEnd_3492476 := by
    simpa [prefixWord, tailWord_3492476, baseEnd_3492476] using wordTrace_append hprefix tailTrace_3492476
  have hstable : (prefixWord ++ tailWord_3492476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492476).length < 2 ^ (prefixWord ++ tailWord_3492476).sum := by decide
  have hdescent : baseEnd_3492476 < baseStart_3492476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492500 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3492500 : Nat := 118140960795 + 3492500 * 2 ^ 59
def prefixEnd_3492500 : Nat := 4983230072969 + 3 ^ 40 * 3492500 * 2
def baseEnd_3492500 : Nat := 597777061942563603796097

theorem tailTrace_3492500 : CollatzResearch.WordTrace tailWord_3492500 prefixEnd_3492500 597777061942563603796097 := by
  unfold tailWord_3492500
  simp only [CollatzResearch.WordTrace]
  refine ⟨63690969923638223178793477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84921293231517630905057969 63690969923638223178793477)
  ·
    refine ⟨11942056860682166846023777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63690969923638223178793477 11942056860682166846023777)
    ·
      refine ⟨8956542645511625134517833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11942056860682166846023777 8956542645511625134517833)
      ·
        refine ⟨6717406984133718850888375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8956542645511625134517833 6717406984133718850888375)
        ·
          refine ⟨10076110476200578276332563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717406984133718850888375 10076110476200578276332563)
          ·
            refine ⟨15114165714300867414498845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076110476200578276332563 15114165714300867414498845)
            ·
              refine ⟨5667812142862825280437067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15114165714300867414498845 5667812142862825280437067)
              ·
                refine ⟨8501718214294237920655601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667812142862825280437067 8501718214294237920655601)
                ·
                  refine ⟨6376288660720678440491701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8501718214294237920655601 6376288660720678440491701)
                  ·
                    refine ⟨597777061942563603796097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6376288660720678440491701 597777061942563603796097)
                    ·
                      rfl

theorem cell23_3492500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3492500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492500 prefixEnd_3492500 := by exact prefixLift 3492500
  have htrace : WordTrace (prefixWord ++ tailWord_3492500) baseStart_3492500 baseEnd_3492500 := by
    simpa [prefixWord, tailWord_3492500, baseEnd_3492500] using wordTrace_append hprefix tailTrace_3492500
  have hstable : (prefixWord ++ tailWord_3492500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492500).length < 2 ^ (prefixWord ++ tailWord_3492500).sum := by decide
  have hdescent : baseEnd_3492500 < baseStart_3492500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492503 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 6, 2]
def baseStart_3492503 : Nat := 118140960795 + 3492503 * 2 ^ 59
def prefixEnd_3492503 : Nat := 4983230072969 + 3 ^ 40 * 3492503 * 2
def baseEnd_3492503 : Nat := 1793332726269654299650777

theorem tailTrace_3492503 : CollatzResearch.WordTrace tailWord_3492503 prefixEnd_3492503 1793332726269654299650777 := by
  unfold tailWord_3492503
  simp only [CollatzResearch.WordTrace]
  refine ⟨127382049266265577869946163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84921366177510385246630775 127382049266265577869946163)
  ·
    refine ⟨191073073899398366804919245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127382049266265577869946163 191073073899398366804919245)
    ·
      refine ⟨71652402712274387551844717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191073073899398366804919245 71652402712274387551844717)
      ·
        refine ⟨26869651017102895331941769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71652402712274387551844717 26869651017102895331941769)
        ·
          refine ⟨20152238262827171498956327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26869651017102895331941769 20152238262827171498956327)
          ·
            refine ⟨30228357394240757248434491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20152238262827171498956327 30228357394240757248434491)
            ·
              refine ⟨45342536091361135872651737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30228357394240757248434491 45342536091361135872651737)
              ·
                refine ⟨34006902068520851904488803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45342536091361135872651737 34006902068520851904488803)
                ·
                  refine ⟨51010353102781277856733205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34006902068520851904488803 51010353102781277856733205)
                  ·
                    refine ⟨2391110301692872399534369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51010353102781277856733205 2391110301692872399534369)
                    ·
                      refine ⟨1793332726269654299650777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391110301692872399534369 1793332726269654299650777)
                      ·
                        rfl

theorem cell23_3492503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_3492503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492503 prefixEnd_3492503 := by exact prefixLift 3492503
  have htrace : WordTrace (prefixWord ++ tailWord_3492503) baseStart_3492503 baseEnd_3492503 := by
    simpa [prefixWord, tailWord_3492503, baseEnd_3492503] using wordTrace_append hprefix tailTrace_3492503
  have hstable : (prefixWord ++ tailWord_3492503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492503).length < 2 ^ (prefixWord ++ tailWord_3492503).sum := by decide
  have hdescent : baseEnd_3492503 < baseStart_3492503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492516 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_3492516 : Nat := 118140960795 + 3492516 * 2 ^ 59
def prefixEnd_3492516 : Nat := 4983230072969 + 3 ^ 40 * 3492516 * 2
def baseEnd_3492516 : Nat := 1793339401518162748788217

theorem tailTrace_3492516 : CollatzResearch.WordTrace tailWord_3492516 prefixEnd_3492516 1793339401518162748788217 := by
  unfold tailWord_3492516
  simp only [CollatzResearch.WordTrace]
  refine ⟨63691261707609240545084701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84921682276812320726779601 63691261707609240545084701)
  ·
    refine ⟨23884223140353465204406763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63691261707609240545084701 23884223140353465204406763)
    ·
      refine ⟨35826334710530197806610145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23884223140353465204406763 35826334710530197806610145)
      ·
        refine ⟨26869751032897648354957609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35826334710530197806610145 26869751032897648354957609)
        ·
          refine ⟨20152313274673236266218207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26869751032897648354957609 20152313274673236266218207)
          ·
            refine ⟨30228469912009854399327311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20152313274673236266218207 30228469912009854399327311)
            ·
              refine ⟨45342704868014781598990967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30228469912009854399327311 45342704868014781598990967)
              ·
                refine ⟨68014057302022172398486451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45342704868014781598990967 68014057302022172398486451)
                ·
                  refine ⟨102021085953033258597729677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68014057302022172398486451 102021085953033258597729677)
                  ·
                    refine ⟨38257907232387471974148629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102021085953033258597729677 38257907232387471974148629)
                    ·
                      refine ⟨1793339401518162748788217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38257907232387471974148629 1793339401518162748788217)
                      ·
                        rfl

theorem cell23_3492516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_3492516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492516 prefixEnd_3492516 := by exact prefixLift 3492516
  have htrace : WordTrace (prefixWord ++ tailWord_3492516) baseStart_3492516 baseEnd_3492516 := by
    simpa [prefixWord, tailWord_3492516, baseEnd_3492516] using wordTrace_append hprefix tailTrace_3492516
  have hstable : (prefixWord ++ tailWord_3492516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492516).length < 2 ^ (prefixWord ++ tailWord_3492516).sum := by decide
  have hdescent : baseEnd_3492516 < baseStart_3492516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492580 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_3492580 : Nat := 118140960795 + 3492580 * 2 ^ 59
def prefixEnd_3492580 : Nat := 4983230072969 + 3 ^ 40 * 3492580 * 2
def baseEnd_3492580 : Nat := 1793372264280050498387923

theorem tailTrace_3492580 : CollatzResearch.WordTrace tailWord_3492580 prefixEnd_3492580 1793372264280050498387923 := by
  unfold tailWord_3492580
  simp only [CollatzResearch.WordTrace]
  refine ⟨63692428843493310010249597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84923238457991080013666129 63692428843493310010249597)
  ·
    refine ⟨23884660816309991253843599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63692428843493310010249597 23884660816309991253843599)
    ·
      refine ⟨35826991224464986880765399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23884660816309991253843599 35826991224464986880765399)
      ·
        refine ⟨53740486836697480321148099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35826991224464986880765399 53740486836697480321148099)
        ·
          refine ⟨80610730255046220481722149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53740486836697480321148099 80610730255046220481722149)
          ·
            refine ⟨15114511922821166340322903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80610730255046220481722149 15114511922821166340322903)
            ·
              refine ⟨22671767884231749510484355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114511922821166340322903 22671767884231749510484355)
              ·
                refine ⟨34007651826347624265726533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22671767884231749510484355 34007651826347624265726533)
                ·
                  refine ⟨6376434717440179549823725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34007651826347624265726533 6376434717440179549823725)
                  ·
                    refine ⟨2391163019040067331183897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6376434717440179549823725 2391163019040067331183897)
                    ·
                      refine ⟨1793372264280050498387923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391163019040067331183897 1793372264280050498387923)
                      ·
                        rfl

theorem cell23_3492580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_3492580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492580 prefixEnd_3492580 := by exact prefixLift 3492580
  have htrace : WordTrace (prefixWord ++ tailWord_3492580) baseStart_3492580 baseEnd_3492580 := by
    simpa [prefixWord, tailWord_3492580, baseEnd_3492580] using wordTrace_append hprefix tailTrace_3492580
  have hstable : (prefixWord ++ tailWord_3492580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492580).length < 2 ^ (prefixWord ++ tailWord_3492580).sum := by decide
  have hdescent : baseEnd_3492580 < baseStart_3492580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492593 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3492593 : Nat := 118140960795 + 3492593 * 2 ^ 59
def prefixEnd_3492593 : Nat := 4983230072969 + 3 ^ 40 * 3492593 * 2
def baseEnd_3492593 : Nat := 1793378939528558947525363

theorem tailTrace_3492593 : CollatzResearch.WordTrace tailWord_3492593 prefixEnd_3492593 1793378939528558947525363 := by
  unfold tailWord_3492593
  simp only [CollatzResearch.WordTrace]
  refine ⟨127385331835939523240722433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84923554557293015493814955 127385331835939523240722433)
  ·
    refine ⟨95538998876954642430541825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127385331835939523240722433 95538998876954642430541825)
    ·
      refine ⟨71654249157715981822906369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95538998876954642430541825 71654249157715981822906369)
      ·
        refine ⟨53740686868286986367179777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71654249157715981822906369 53740686868286986367179777)
        ·
          refine ⟨40305515151215239775384833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53740686868286986367179777 40305515151215239775384833)
          ·
            refine ⟨30229136363411429831538625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40305515151215239775384833 30229136363411429831538625)
            ·
              refine ⟨22671852272558572373653969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30229136363411429831538625 22671852272558572373653969)
              ·
                refine ⟨17003889204418929280240477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22671852272558572373653969 17003889204418929280240477)
                ·
                  refine ⟨6376458451657098480090179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17003889204418929280240477 6376458451657098480090179)
                  ·
                    refine ⟨9564687677485647720135269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6376458451657098480090179 9564687677485647720135269)
                    ·
                      refine ⟨1793378939528558947525363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9564687677485647720135269 1793378939528558947525363)
                      ·
                        rfl

theorem cell23_3492593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3492593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492593 prefixEnd_3492593 := by exact prefixLift 3492593
  have htrace : WordTrace (prefixWord ++ tailWord_3492593) baseStart_3492593 baseEnd_3492593 := by
    simpa [prefixWord, tailWord_3492593, baseEnd_3492593] using wordTrace_append hprefix tailTrace_3492593
  have hstable : (prefixWord ++ tailWord_3492593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492593).length < 2 ^ (prefixWord ++ tailWord_3492593).sum := by decide
  have hdescent : baseEnd_3492593 < baseStart_3492593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492623 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_3492623 : Nat := 118140960795 + 3492623 * 2 ^ 59
def prefixEnd_3492623 : Nat := 4983230072969 + 3 ^ 40 * 3492623 * 2
def baseEnd_3492623 : Nat := 1793394343948193830150225

theorem tailTrace_3492623 : CollatzResearch.WordTrace tailWord_3492623 prefixEnd_3492623 1793394343948193830150225 := by
  unfold tailWord_3492623
  simp only [CollatzResearch.WordTrace]
  refine ⟨127386426025830838364314523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84924284017220558909543015 127386426025830838364314523)
  ·
    refine ⟨191079639038746257546471785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127386426025830838364314523 191079639038746257546471785)
    ·
      refine ⟨143309729279059693159853839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191079639038746257546471785 143309729279059693159853839)
      ·
        refine ⟨214964593918589539739780759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143309729279059693159853839 214964593918589539739780759)
        ·
          refine ⟨322446890877884309609671139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214964593918589539739780759 322446890877884309609671139)
          ·
            refine ⟨483670336316826464414506709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322446890877884309609671139 483670336316826464414506709)
            ·
              refine ⟨11336023507425620259715001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 483670336316826464414506709 11336023507425620259715001)
              ·
                refine ⟨8502017630569215194786251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11336023507425620259715001 8502017630569215194786251)
                ·
                  refine ⟨12753026445853822792179377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502017630569215194786251 12753026445853822792179377)
                  ·
                    refine ⟨9564769834390367094134533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12753026445853822792179377 9564769834390367094134533)
                    ·
                      refine ⟨1793394343948193830150225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9564769834390367094134533 1793394343948193830150225)
                      ·
                        rfl

theorem cell23_3492623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_3492623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492623 prefixEnd_3492623 := by exact prefixLift 3492623
  have htrace : WordTrace (prefixWord ++ tailWord_3492623) baseStart_3492623 baseEnd_3492623 := by
    simpa [prefixWord, tailWord_3492623, baseEnd_3492623] using wordTrace_append hprefix tailTrace_3492623
  have hstable : (prefixWord ++ tailWord_3492623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492623).length < 2 ^ (prefixWord ++ tailWord_3492623).sum := by decide
  have hdescent : baseEnd_3492623 < baseStart_3492623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492643 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 3]
def baseStart_3492643 : Nat := 118140960795 + 3492643 * 2 ^ 59
def prefixEnd_3492643 : Nat := 4983230072969 + 3 ^ 40 * 3492643 * 2
def baseEnd_3492643 : Nat := 1793404613561283751900133

theorem tailTrace_3492643 : CollatzResearch.WordTrace tailWord_3492643 prefixEnd_3492643 1793404613561283751900133 := by
  unfold tailWord_3492643
  simp only [CollatzResearch.WordTrace]
  refine ⟨127387155485758381780042583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84924770323838921186695055 127387155485758381780042583)
  ·
    refine ⟨191080733228637572670063875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127387155485758381780042583 191080733228637572670063875)
    ·
      refine ⟨286621099842956359005095813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191080733228637572670063875 286621099842956359005095813)
      ·
        refine ⟨53741456220554317313455465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286621099842956359005095813 53741456220554317313455465)
        ·
          refine ⟨40306092165415737985091599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53741456220554317313455465 40306092165415737985091599)
          ·
            refine ⟨60459138248123606977637399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40306092165415737985091599 60459138248123606977637399)
            ·
              refine ⟨90688707372185410466456099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60459138248123606977637399 90688707372185410466456099)
              ·
                refine ⟨136033061058278115699684149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90688707372185410466456099 136033061058278115699684149)
                ·
                  refine ⟨12753099474213573346845389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136033061058278115699684149 12753099474213573346845389)
                  ·
                    refine ⟨4782412302830090005067021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12753099474213573346845389 4782412302830090005067021)
                    ·
                      refine ⟨1793404613561283751900133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4782412302830090005067021 1793404613561283751900133)
                      ·
                        rfl

theorem cell23_3492643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_3492643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492643 prefixEnd_3492643 := by exact prefixLift 3492643
  have htrace : WordTrace (prefixWord ++ tailWord_3492643) baseStart_3492643 baseEnd_3492643 := by
    simpa [prefixWord, tailWord_3492643, baseEnd_3492643] using wordTrace_append hprefix tailTrace_3492643
  have hstable : (prefixWord ++ tailWord_3492643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492643).length < 2 ^ (prefixWord ++ tailWord_3492643).sum := by decide
  have hdescent : baseEnd_3492643 < baseStart_3492643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492678 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3492678 : Nat := 118140960795 + 3492678 * 2 ^ 59
def prefixEnd_3492678 : Nat := 4983230072969 + 3 ^ 40 * 3492678 * 2
def baseEnd_3492678 : Nat := 1793422585384191114962473

theorem tailTrace_3492678 : CollatzResearch.WordTrace tailWord_3492678 prefixEnd_3492678 1793422585384191114962473 := by
  unfold tailWord_3492678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980888501269736961173959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84925621360421055171711125 3980888501269736961173959)
  ·
    refine ⟨5971332751904605441760939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3980888501269736961173959 5971332751904605441760939)
    ·
      refine ⟨8956999127856908162641409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971332751904605441760939 8956999127856908162641409)
      ·
        refine ⟨6717749345892681121981057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8956999127856908162641409 6717749345892681121981057)
        ·
          refine ⟨5038312009419510841485793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6717749345892681121981057 5038312009419510841485793)
          ·
            refine ⟨3778734007064633131114345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5038312009419510841485793 3778734007064633131114345)
            ·
              refine ⟨2834050505298474848335759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3778734007064633131114345 2834050505298474848335759)
              ·
                refine ⟨4251075757947712272503639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834050505298474848335759 4251075757947712272503639)
                ·
                  refine ⟨6376613636921568408755459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251075757947712272503639 6376613636921568408755459)
                  ·
                    refine ⟨9564920455382352613133189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6376613636921568408755459 9564920455382352613133189)
                    ·
                      refine ⟨1793422585384191114962473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9564920455382352613133189 1793422585384191114962473)
                      ·
                        rfl

theorem cell23_3492678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3492678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492678 prefixEnd_3492678 := by exact prefixLift 3492678
  have htrace : WordTrace (prefixWord ++ tailWord_3492678) baseStart_3492678 baseEnd_3492678 := by
    simpa [prefixWord, tailWord_3492678, baseEnd_3492678] using wordTrace_append hprefix tailTrace_3492678
  have hstable : (prefixWord ++ tailWord_3492678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492678).length < 2 ^ (prefixWord ++ tailWord_3492678).sum := by decide
  have hdescent : baseEnd_3492678 < baseStart_3492678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492693 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3492693 : Nat := 118140960795 + 3492693 * 2 ^ 59
def prefixEnd_3492693 : Nat := 4983230072969 + 3 ^ 40 * 3492693 * 2
def baseEnd_3492693 : Nat := 597810095864669518758301

theorem tailTrace_3492693 : CollatzResearch.WordTrace tailWord_3492693 prefixEnd_3492693 597810095864669518758301 := by
  unfold tailWord_3492693
  simp only [CollatzResearch.WordTrace]
  refine ⟨127388979135577240319362733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84925986090384826879575155 127388979135577240319362733)
  ·
    refine ⟨47770867175841465119761025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127388979135577240319362733 47770867175841465119761025)
    ·
      refine ⟨35828150381881098839820769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47770867175841465119761025 35828150381881098839820769)
      ·
        refine ⟨26871112786410824129865577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35828150381881098839820769 26871112786410824129865577)
        ·
          refine ⟨20153334589808118097399183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26871112786410824129865577 20153334589808118097399183)
          ·
            refine ⟨30230001884712177146098775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20153334589808118097399183 30230001884712177146098775)
            ·
              refine ⟨45345002827068265719148163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30230001884712177146098775 45345002827068265719148163)
              ·
                refine ⟨68017504240602398578722245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45345002827068265719148163 68017504240602398578722245)
                ·
                  refine ⟨12753282045112949733510421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68017504240602398578722245 12753282045112949733510421)
                  ·
                    refine ⟨597810095864669518758301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12753282045112949733510421 597810095864669518758301)
                    ·
                      rfl

theorem cell23_3492693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3492693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492693 prefixEnd_3492693 := by exact prefixLift 3492693
  have htrace : WordTrace (prefixWord ++ tailWord_3492693) baseStart_3492693 baseEnd_3492693 := by
    simpa [prefixWord, tailWord_3492693, baseEnd_3492693] using wordTrace_append hprefix tailTrace_3492693
  have hstable : (prefixWord ++ tailWord_3492693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492693).length < 2 ^ (prefixWord ++ tailWord_3492693).sum := by decide
  have hdescent : baseEnd_3492693 < baseStart_3492693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492723 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 7]
def baseStart_3492723 : Nat := 118140960795 + 3492723 * 2 ^ 59
def prefixEnd_3492723 : Nat := 4983230072969 + 3 ^ 40 * 3492723 * 2
def baseEnd_3492723 : Nat := 199271743557071493211085

theorem tailTrace_3492723 : CollatzResearch.WordTrace tailWord_3492723 prefixEnd_3492723 199271743557071493211085 := by
  unfold tailWord_3492723
  simp only [CollatzResearch.WordTrace]
  refine ⟨127390073325468555442954823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84926715550312370295303215 127390073325468555442954823)
  ·
    refine ⟨191085109988202833164432235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127390073325468555442954823 191085109988202833164432235)
    ·
      refine ⟨286627664982304249746648353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191085109988202833164432235 286627664982304249746648353)
      ·
        refine ⟨214970748736728187309986265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286627664982304249746648353 214970748736728187309986265)
        ·
          refine ⟨161228061552546140482489699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214970748736728187309986265 161228061552546140482489699)
          ·
            refine ⟨241842092328819210723734549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161228061552546140482489699 241842092328819210723734549)
            ·
              refine ⟨11336348077913400502675057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241842092328819210723734549 11336348077913400502675057)
              ·
                refine ⟨8502261058435050377006293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11336348077913400502675057 8502261058435050377006293)
                ·
                  refine ⟨199271743557071493211085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8502261058435050377006293 199271743557071493211085)
                  ·
                    rfl

theorem cell23_3492723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 7].length) (baseStart_3492723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492723 prefixEnd_3492723 := by exact prefixLift 3492723
  have htrace : WordTrace (prefixWord ++ tailWord_3492723) baseStart_3492723 baseEnd_3492723 := by
    simpa [prefixWord, tailWord_3492723, baseEnd_3492723] using wordTrace_append hprefix tailTrace_3492723
  have hstable : (prefixWord ++ tailWord_3492723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492723).length < 2 ^ (prefixWord ++ tailWord_3492723).sum := by decide
  have hdescent : baseEnd_3492723 < baseStart_3492723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492803 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_3492803 : Nat := 118140960795 + 3492803 * 2 ^ 59
def prefixEnd_3492803 : Nat := 4983230072969 + 3 ^ 40 * 3492803 * 2
def baseEnd_3492803 : Nat := 1793486770466003125899397

theorem tailTrace_3492803 : CollatzResearch.WordTrace tailWord_3492803 prefixEnd_3492803 1793486770466003125899397 := by
  unfold tailWord_3492803
  simp only [CollatzResearch.WordTrace]
  refine ⟨127392991165178729105867063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84928660776785819403911375 127392991165178729105867063)
  ·
    refine ⟨191089486747768093658800595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127392991165178729105867063 191089486747768093658800595)
    ·
      refine ⟨286634230121652140488200893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191089486747768093658800595 286634230121652140488200893)
      ·
        refine ⟨107487836295619552683075335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286634230121652140488200893 107487836295619552683075335)
        ·
          refine ⟨161231754443429329024613003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107487836295619552683075335 161231754443429329024613003)
          ·
            refine ⟨241847631665143993536919505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161231754443429329024613003 241847631665143993536919505)
            ·
              refine ⟨181385723748857995152689629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241847631665143993536919505 181385723748857995152689629)
              ·
                refine ⟨68019646405821748182258611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181385723748857995152689629 68019646405821748182258611)
                ·
                  refine ⟨102029469608732622273387917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68019646405821748182258611 102029469608732622273387917)
                  ·
                    refine ⟨38261051103274733352520469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102029469608732622273387917 38261051103274733352520469)
                    ·
                      refine ⟨1793486770466003125899397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38261051103274733352520469 1793486770466003125899397)
                      ·
                        rfl

theorem cell23_3492803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_3492803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492803 prefixEnd_3492803 := by exact prefixLift 3492803
  have htrace : WordTrace (prefixWord ++ tailWord_3492803) baseStart_3492803 baseEnd_3492803 := by
    simpa [prefixWord, tailWord_3492803, baseEnd_3492803] using wordTrace_append hprefix tailTrace_3492803
  have hstable : (prefixWord ++ tailWord_3492803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492803).length < 2 ^ (prefixWord ++ tailWord_3492803).sum := by decide
  have hdescent : baseEnd_3492803 < baseStart_3492803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492810 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_3492810 : Nat := 118140960795 + 3492810 * 2 ^ 59
def prefixEnd_3492810 : Nat := 4983230072969 + 3 ^ 40 * 3492810 * 2
def baseEnd_3492810 : Nat := 1793490364830584598511865

theorem tailTrace_3492810 : CollatzResearch.WordTrace tailWord_3492810 prefixEnd_3492810 1793490364830584598511865 := by
  unfold tailWord_3492810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31848311619038342325342971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84928830984102246200914589 31848311619038342325342971)
  ·
    refine ⟨47772467428557513488014457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31848311619038342325342971 47772467428557513488014457)
    ·
      refine ⟨35829350571418135116010843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47772467428557513488014457 35829350571418135116010843)
      ·
        refine ⟨53744025857127202674016265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35829350571418135116010843 53744025857127202674016265)
        ·
          refine ⟨40308019392845402005512199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53744025857127202674016265 40308019392845402005512199)
          ·
            refine ⟨60462029089268103008268299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40308019392845402005512199 60462029089268103008268299)
            ·
              refine ⟨90693043633902154512402449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60462029089268103008268299 90693043633902154512402449)
              ·
                refine ⟨68019782725426615884301837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90693043633902154512402449 68019782725426615884301837)
                ·
                  refine ⟨25507418522034980956613189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68019782725426615884301837 25507418522034980956613189)
                  ·
                    refine ⟨4782640972881558929364973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25507418522034980956613189 4782640972881558929364973)
                    ·
                      refine ⟨1793490364830584598511865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4782640972881558929364973 1793490364830584598511865)
                      ·
                        rfl

theorem cell23_3492810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_3492810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492810 prefixEnd_3492810 := by exact prefixLift 3492810
  have htrace : WordTrace (prefixWord ++ tailWord_3492810) baseStart_3492810 baseEnd_3492810 := by
    simpa [prefixWord, tailWord_3492810, baseEnd_3492810] using wordTrace_append hprefix tailTrace_3492810
  have hstable : (prefixWord ++ tailWord_3492810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492810).length < 2 ^ (prefixWord ++ tailWord_3492810).sum := by decide
  have hdescent : baseEnd_3492810 < baseStart_3492810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492834 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3492834 : Nat := 118140960795 + 3492834 * 2 ^ 59
def prefixEnd_3492834 : Nat := 4983230072969 + 3 ^ 40 * 3492834 * 2
def baseEnd_3492834 : Nat := 597834229455430834870585

theorem tailTrace_3492834 : CollatzResearch.WordTrace tailWord_3492834 prefixEnd_3492834 597834229455430834870585 := by
  unfold tailWord_3492834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31848530457016605350061389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84929414552044280933497037 31848530457016605350061389)
  ·
    refine ⟨11943198921381227006273021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31848530457016605350061389 11943198921381227006273021)
    ·
      refine ⟨4478699595517960127352383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11943198921381227006273021 4478699595517960127352383)
      ·
        refine ⟨6718049393276940191028575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478699595517960127352383 6718049393276940191028575)
        ·
          refine ⟨10077074089915410286542863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6718049393276940191028575 10077074089915410286542863)
          ·
            refine ⟨15115611134873115429814295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10077074089915410286542863 15115611134873115429814295)
            ·
              refine ⟨22673416702309673144721443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15115611134873115429814295 22673416702309673144721443)
              ·
                refine ⟨34010125053464509717082165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22673416702309673144721443 34010125053464509717082165)
                ·
                  refine ⟨3188449223762297785976453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34010125053464509717082165 3188449223762297785976453)
                  ·
                    refine ⟨597834229455430834870585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3188449223762297785976453 597834229455430834870585)
                    ·
                      rfl

theorem cell23_3492834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3492834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492834 prefixEnd_3492834 := by exact prefixLift 3492834
  have htrace : WordTrace (prefixWord ++ tailWord_3492834) baseStart_3492834 baseEnd_3492834 := by
    simpa [prefixWord, tailWord_3492834, baseEnd_3492834] using wordTrace_append hprefix tailTrace_3492834
  have hstable : (prefixWord ++ tailWord_3492834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492834).length < 2 ^ (prefixWord ++ tailWord_3492834).sum := by decide
  have hdescent : baseEnd_3492834 < baseStart_3492834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492857 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3492857 : Nat := 118140960795 + 3492857 * 2 ^ 59
def prefixEnd_3492857 : Nat := 4983230072969 + 3 ^ 40 * 3492857 * 2
def baseEnd_3492857 : Nat := 1793514498421345914624149

theorem tailTrace_3492857 : CollatzResearch.WordTrace tailWord_3492857 prefixEnd_3492857 1793514498421345914624149 := by
  unfold tailWord_3492857
  simp only [CollatzResearch.WordTrace]
  refine ⟨127394960706983096328332825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84929973804655397552221883 127394960706983096328332825)
  ·
    refine ⟨95546220530237322246249619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127394960706983096328332825 95546220530237322246249619)
    ·
      refine ⟨143319330795355983369374429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95546220530237322246249619 143319330795355983369374429)
      ·
        refine ⟨53744749048258493763515411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143319330795355983369374429 53744749048258493763515411)
        ·
          refine ⟨80617123572387740645273117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53744749048258493763515411 80617123572387740645273117)
          ·
            refine ⟨30231421339645402741977419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80617123572387740645273117 30231421339645402741977419)
            ·
              refine ⟨45347132009468104112966129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30231421339645402741977419 45347132009468104112966129)
              ·
                refine ⟨34010349007101078084724597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45347132009468104112966129 34010349007101078084724597)
                ·
                  refine ⟨3188470219415726070442931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34010349007101078084724597 3188470219415726070442931)
                  ·
                    refine ⟨4782705329123589105664397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3188470219415726070442931 4782705329123589105664397)
                    ·
                      refine ⟨1793514498421345914624149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4782705329123589105664397 1793514498421345914624149)
                      ·
                        rfl

theorem cell23_3492857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3492857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492857 prefixEnd_3492857 := by exact prefixLift 3492857
  have htrace : WordTrace (prefixWord ++ tailWord_3492857) baseStart_3492857 baseEnd_3492857 := by
    simpa [prefixWord, tailWord_3492857, baseEnd_3492857] using wordTrace_append hprefix tailTrace_3492857
  have hstable : (prefixWord ++ tailWord_3492857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492857).length < 2 ^ (prefixWord ++ tailWord_3492857).sum := by decide
  have hdescent : baseEnd_3492857 < baseStart_3492857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492874 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3492874 : Nat := 118140960795 + 3492874 * 2 ^ 59
def prefixEnd_3492874 : Nat := 4983230072969 + 3 ^ 40 * 3492874 * 2
def baseEnd_3492874 : Nat := 1793523227592472348111571

theorem tailTrace_3492874 : CollatzResearch.WordTrace tailWord_3492874 prefixEnd_3492874 1793523227592472348111571 := by
  unfold tailWord_3492874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31848895186980377057925419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84930387165281005487801117 31848895186980377057925419)
  ·
    refine ⟨47773342780470565586888129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31848895186980377057925419 47773342780470565586888129)
    ·
      refine ⟨35830007085352924190166097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47773342780470565586888129 35830007085352924190166097)
      ·
        refine ⟨26872505314014693142624573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35830007085352924190166097 26872505314014693142624573)
        ·
          refine ⟨10077189492755509928484215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26872505314014693142624573 10077189492755509928484215)
          ·
            refine ⟨15115784239133264892726323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10077189492755509928484215 15115784239133264892726323)
            ·
              refine ⟨22673676358699897339089485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15115784239133264892726323 22673676358699897339089485)
              ·
                refine ⟨8502628634512461502158557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22673676358699897339089485 8502628634512461502158557)
                ·
                  refine ⟨3188485737942173063309459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8502628634512461502158557 3188485737942173063309459)
                  ·
                    refine ⟨4782728606913259594964189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3188485737942173063309459 4782728606913259594964189)
                    ·
                      refine ⟨1793523227592472348111571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4782728606913259594964189 1793523227592472348111571)
                      ·
                        rfl

theorem cell23_3492874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3492874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492874 prefixEnd_3492874 := by exact prefixLift 3492874
  have htrace : WordTrace (prefixWord ++ tailWord_3492874) baseStart_3492874 baseEnd_3492874 := by
    simpa [prefixWord, tailWord_3492874, baseEnd_3492874] using wordTrace_append hprefix tailTrace_3492874
  have hstable : (prefixWord ++ tailWord_3492874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492874).length < 2 ^ (prefixWord ++ tailWord_3492874).sum := by decide
  have hdescent : baseEnd_3492874 < baseStart_3492874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492917 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_3492917 : Nat := 118140960795 + 3492917 * 2 ^ 59
def prefixEnd_3492917 : Nat := 4983230072969 + 3 ^ 40 * 3492917 * 2
def baseEnd_3492917 : Nat := 1793545307260615679873873

theorem tailTrace_3492917 : CollatzResearch.WordTrace tailWord_3492917 prefixEnd_3492917 1793545307260615679873873 := by
  unfold tailWord_3492917
  simp only [CollatzResearch.WordTrace]
  refine ⟨127397149086765726575517005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84931432724510484383678003 127397149086765726575517005)
  ·
    refine ⟨47773930907537147465818877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127397149086765726575517005 47773930907537147465818877)
    ·
      refine ⟨17915224090326430299682079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47773930907537147465818877 17915224090326430299682079)
      ·
        refine ⟨26872836135489645449523119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17915224090326430299682079 26872836135489645449523119)
        ·
          refine ⟨40309254203234468174284679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26872836135489645449523119 40309254203234468174284679)
          ·
            refine ⟨60463881304851702261427019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40309254203234468174284679 60463881304851702261427019)
            ·
              refine ⟨90695821957277553392140529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60463881304851702261427019 90695821957277553392140529)
              ·
                refine ⟨68021866467958165044105397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90695821957277553392140529 68021866467958165044105397)
                ·
                  refine ⟨6377049981371077972884881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68021866467958165044105397 6377049981371077972884881)
                  ·
                    refine ⟨4782787486028308479663661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6377049981371077972884881 4782787486028308479663661)
                    ·
                      refine ⟨1793545307260615679873873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4782787486028308479663661 1793545307260615679873873)
                      ·
                        rfl

theorem cell23_3492917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_3492917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492917 prefixEnd_3492917 := by exact prefixLift 3492917
  have htrace : WordTrace (prefixWord ++ tailWord_3492917) baseStart_3492917 baseEnd_3492917 := by
    simpa [prefixWord, tailWord_3492917, baseEnd_3492917] using wordTrace_append hprefix tailTrace_3492917
  have hstable : (prefixWord ++ tailWord_3492917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492917).length < 2 ^ (prefixWord ++ tailWord_3492917).sum := by decide
  have hdescent : baseEnd_3492917 < baseStart_3492917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492920 : List Nat := [2, 1, 2, 1, 5, 1, 11]
def baseStart_3492920 : Nat := 118140960795 + 3492920 * 2 ^ 59
def prefixEnd_3492920 : Nat := 4983230072969 + 3 ^ 40 * 3492920 * 2
def baseEnd_3492920 : Nat := 22142553675340483557239

theorem tailTrace_3492920 : CollatzResearch.WordTrace tailWord_3492920 prefixEnd_3492920 22142553675340483557239 := by
  unfold tailWord_3492920
  simp only [CollatzResearch.WordTrace]
  refine ⟨63698629252877429043938107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84931505670503238725250809 63698629252877429043938107)
  ·
    refine ⟨95547943879316143565907161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63698629252877429043938107 95547943879316143565907161)
    ·
      refine ⟨71660957909487107674430371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95547943879316143565907161 71660957909487107674430371)
      ·
        refine ⟨107491436864230661511645557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71660957909487107674430371 107491436864230661511645557)
        ·
          refine ⟨10077322206021624516716771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107491436864230661511645557 10077322206021624516716771)
          ·
            refine ⟨15115983309032436775075157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10077322206021624516716771 15115983309032436775075157)
            ·
              refine ⟨22142553675340483557239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15115983309032436775075157 22142553675340483557239)
              ·
                rfl

theorem cell23_3492920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 11].length) (baseStart_3492920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492920 prefixEnd_3492920 := by exact prefixLift 3492920
  have htrace : WordTrace (prefixWord ++ tailWord_3492920) baseStart_3492920 baseEnd_3492920 := by
    simpa [prefixWord, tailWord_3492920, baseEnd_3492920] using wordTrace_append hprefix tailTrace_3492920
  have hstable : (prefixWord ++ tailWord_3492920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492920).length < 2 ^ (prefixWord ++ tailWord_3492920).sum := by decide
  have hdescent : baseEnd_3492920 < baseStart_3492920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492940 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3492940 : Nat := 118140960795 + 3492940 * 2 ^ 59
def prefixEnd_3492940 : Nat := 4983230072969 + 3 ^ 40 * 3492940 * 2
def baseEnd_3492940 : Nat := 1793557117315669089886267

theorem tailTrace_3492940 : CollatzResearch.WordTrace tailWord_3492940 prefixEnd_3492940 1793557117315669089886267 := by
  unfold tailWord_3492940
  simp only [CollatzResearch.WordTrace]
  refine ⟨63698993982841200751802137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84931991977121601002402849 63698993982841200751802137)
  ·
    refine ⟨47774245487130900563851603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63698993982841200751802137 47774245487130900563851603)
    ·
      refine ⟨71661368230696350845777405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47774245487130900563851603 71661368230696350845777405)
      ·
        refine ⟨26873013086511131567166527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71661368230696350845777405 26873013086511131567166527)
        ·
          refine ⟨40309519629766697350749791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26873013086511131567166527 40309519629766697350749791)
          ·
            refine ⟨60464279444650046026124687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40309519629766697350749791 60464279444650046026124687)
            ·
              refine ⟨90696419166975069039187031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60464279444650046026124687 90696419166975069039187031)
              ·
                refine ⟨136044628750462603558780547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90696419166975069039187031 136044628750462603558780547)
                ·
                  refine ⟨204066943125693905338170821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136044628750462603558780547 204066943125693905338170821)
                  ·
                    refine ⟨38262551836067607250907029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204066943125693905338170821 38262551836067607250907029)
                    ·
                      refine ⟨1793557117315669089886267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38262551836067607250907029 1793557117315669089886267)
                      ·
                        rfl

theorem cell23_3492940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3492940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492940 prefixEnd_3492940 := by exact prefixLift 3492940
  have htrace : WordTrace (prefixWord ++ tailWord_3492940) baseStart_3492940 baseEnd_3492940 := by
    simpa [prefixWord, tailWord_3492940, baseEnd_3492940] using wordTrace_append hprefix tailTrace_3492940
  have hstable : (prefixWord ++ tailWord_3492940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492940).length < 2 ^ (prefixWord ++ tailWord_3492940).sum := by decide
  have hdescent : baseEnd_3492940 < baseStart_3492940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492941 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3492941 : Nat := 118140960795 + 3492941 * 2 ^ 59
def prefixEnd_3492941 : Nat := 4983230072969 + 3 ^ 40 * 3492941 * 2
def baseEnd_3492941 : Nat := 597852543598774528657921

theorem tailTrace_3492941 : CollatzResearch.WordTrace tailWord_3492941 prefixEnd_3492941 597852543598774528657921 := by
  unfold tailWord_3492941
  simp only [CollatzResearch.WordTrace]
  refine ⟨127398024438678778674390677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84932016292452519116260451 127398024438678778674390677)
  ·
    refine ⟨5971782395563067750362063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127398024438678778674390677 5971782395563067750362063)
    ·
      refine ⟨8957673593344601625543095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971782395563067750362063 8957673593344601625543095)
      ·
        refine ⟨13436510390016902438314643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8957673593344601625543095 13436510390016902438314643)
        ·
          refine ⟨20154765585025353657471965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13436510390016902438314643 20154765585025353657471965)
          ·
            refine ⟨7558037094384507621551987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20154765585025353657471965 7558037094384507621551987)
            ·
              refine ⟨11337055641576761432327981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558037094384507621551987 11337055641576761432327981)
              ·
                refine ⟨4251395865591285537122993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11337055641576761432327981 4251395865591285537122993)
                ·
                  refine ⟨3188546899193464152842245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4251395865591285537122993 3188546899193464152842245)
                  ·
                    refine ⟨597852543598774528657921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3188546899193464152842245 597852543598774528657921)
                    ·
                      rfl

theorem cell23_3492941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3492941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492941 prefixEnd_3492941 := by exact prefixLift 3492941
  have htrace : WordTrace (prefixWord ++ tailWord_3492941) baseStart_3492941 baseEnd_3492941 := by
    simpa [prefixWord, tailWord_3492941, baseEnd_3492941] using wordTrace_append hprefix tailTrace_3492941
  have hstable : (prefixWord ++ tailWord_3492941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492941).length < 2 ^ (prefixWord ++ tailWord_3492941).sum := by decide
  have hdescent : baseEnd_3492941 < baseStart_3492941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3492968 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3492968 : Nat := 118140960795 + 3492968 * 2 ^ 59
def prefixEnd_3492968 : Nat := 4983230072969 + 3 ^ 40 * 3492968 * 2
def baseEnd_3492968 : Nat := 1793571494773994980336139

theorem tailTrace_3492968 : CollatzResearch.WordTrace tailWord_3492968 prefixEnd_3492968 1793571494773994980336139 := by
  unfold tailWord_3492968
  simp only [CollatzResearch.WordTrace]
  refine ⟨63699504604790481142811779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84932672806387308190415705 63699504604790481142811779)
  ·
    refine ⟨95549256907185721714217669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63699504604790481142811779 95549256907185721714217669)
    ·
      refine ⟨17915485670097322821415813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95549256907185721714217669 17915485670097322821415813)
      ·
        refine ⟨3359153563143248029015465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17915485670097322821415813 3359153563143248029015465)
        ·
          refine ⟨2519365172357436021761599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3359153563143248029015465 2519365172357436021761599)
          ·
            refine ⟨3779047758536154032642399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519365172357436021761599 3779047758536154032642399)
            ·
              refine ⟨5668571637804231048963599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779047758536154032642399 5668571637804231048963599)
              ·
                refine ⟨8502857456706346573445399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668571637804231048963599 8502857456706346573445399)
                ·
                  refine ⟨12754286185059519860168099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502857456706346573445399 12754286185059519860168099)
                  ·
                    refine ⟨19131429277589279790252149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12754286185059519860168099 19131429277589279790252149)
                    ·
                      refine ⟨1793571494773994980336139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19131429277589279790252149 1793571494773994980336139)
                      ·
                        rfl

theorem cell23_3492968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3492968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3492968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3492968 prefixEnd_3492968 := by exact prefixLift 3492968
  have htrace : WordTrace (prefixWord ++ tailWord_3492968) baseStart_3492968 baseEnd_3492968 := by
    simpa [prefixWord, tailWord_3492968, baseEnd_3492968] using wordTrace_append hprefix tailTrace_3492968
  have hstable : (prefixWord ++ tailWord_3492968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3492968).length < 2 ^ (prefixWord ++ tailWord_3492968).sum := by decide
  have hdescent : baseEnd_3492968 < baseStart_3492968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3492968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493021 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_3493021 : Nat := 118140960795 + 3493021 * 2 ^ 59
def prefixEnd_3493021 : Nat := 4983230072969 + 3 ^ 40 * 3493021 * 2
def baseEnd_3493021 : Nat := 1793598709248683272973395

theorem tailTrace_3493021 : CollatzResearch.WordTrace tailWord_3493021 prefixEnd_3493021 1793598709248683272973395 := by
  unfold tailWord_3493021
  simp only [CollatzResearch.WordTrace]
  refine ⟨127400942278388952337302917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84933961518925968224868611 127400942278388952337302917)
  ·
    refine ⟨23887676677197928563244297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127400942278388952337302917 23887676677197928563244297)
    ·
      refine ⟨17915757507898446422433223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23887676677197928563244297 17915757507898446422433223)
      ·
        refine ⟨26873636261847669633649835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17915757507898446422433223 26873636261847669633649835)
        ·
          refine ⟨40310454392771504450474753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26873636261847669633649835 40310454392771504450474753)
          ·
            refine ⟨30232840794578628337856065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40310454392771504450474753 30232840794578628337856065)
            ·
              refine ⟨22674630595933971253392049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30232840794578628337856065 22674630595933971253392049)
              ·
                refine ⟨17005972946950478440044037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22674630595933971253392049 17005972946950478440044037)
                ·
                  refine ⟨3188619927553214707508257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17005972946950478440044037 3188619927553214707508257)
                  ·
                    refine ⟨2391464945664911030631193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3188619927553214707508257 2391464945664911030631193)
                    ·
                      refine ⟨1793598709248683272973395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391464945664911030631193 1793598709248683272973395)
                      ·
                        rfl

theorem cell23_3493021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_3493021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493021 prefixEnd_3493021 := by exact prefixLift 3493021
  have htrace : WordTrace (prefixWord ++ tailWord_3493021) baseStart_3493021 baseEnd_3493021 := by
    simpa [prefixWord, tailWord_3493021, baseEnd_3493021] using wordTrace_append hprefix tailTrace_3493021
  have hstable : (prefixWord ++ tailWord_3493021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493021).length < 2 ^ (prefixWord ++ tailWord_3493021).sum := by decide
  have hdescent : baseEnd_3493021 < baseStart_3493021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493064 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_3493064 : Nat := 118140960795 + 3493064 * 2 ^ 59
def prefixEnd_3493064 : Nat := 4983230072969 + 3 ^ 40 * 3493064 * 2
def baseEnd_3493064 : Nat := 1793620788916826604735697

theorem tailTrace_3493064 : CollatzResearch.WordTrace tailWord_3493064 prefixEnd_3493064 1793620788916826604735697 := by
  unfold tailWord_3493064
  simp only [CollatzResearch.WordTrace]
  refine ⟨63701255308616585340559123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84935007078155447120745497 63701255308616585340559123)
  ·
    refine ⟨95551882962924878010838685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63701255308616585340559123 95551882962924878010838685)
    ·
      refine ⟨35831956111096829254064507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95551882962924878010838685 35831956111096829254064507)
      ·
        refine ⟨53747934166645243881096761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35831956111096829254064507 53747934166645243881096761)
        ·
          refine ⟨40310950624983932910822571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53747934166645243881096761 40310950624983932910822571)
          ·
            refine ⟨60466425937475899366233857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40310950624983932910822571 60466425937475899366233857)
            ·
              refine ⟨45349819453106924524675393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60466425937475899366233857 45349819453106924524675393)
              ·
                refine ⟨34012364589830193393506545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45349819453106924524675393 34012364589830193393506545)
                ·
                  refine ⟨25509273442372645045129909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34012364589830193393506545 25509273442372645045129909)
                  ·
                    refine ⟨2391494385222435472980929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25509273442372645045129909 2391494385222435472980929)
                    ·
                      refine ⟨1793620788916826604735697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391494385222435472980929 1793620788916826604735697)
                      ·
                        rfl

theorem cell23_3493064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_3493064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493064 prefixEnd_3493064 := by exact prefixLift 3493064
  have htrace : WordTrace (prefixWord ++ tailWord_3493064) baseStart_3493064 baseEnd_3493064 := by
    simpa [prefixWord, tailWord_3493064, baseEnd_3493064] using wordTrace_append hprefix tailTrace_3493064
  have hstable : (prefixWord ++ tailWord_3493064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493064).length < 2 ^ (prefixWord ++ tailWord_3493064).sum := by decide
  have hdescent : baseEnd_3493064 < baseStart_3493064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493074 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3493074 : Nat := 118140960795 + 3493074 * 2 ^ 59
def prefixEnd_3493074 : Nat := 4983230072969 + 3 ^ 40 * 3493074 * 2
def baseEnd_3493074 : Nat := 597875307907790521870217

theorem tailTrace_3493074 : CollatzResearch.WordTrace tailWord_3493074 prefixEnd_3493074 597875307907790521870217 := by
  unfold tailWord_3493074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31850718836799235597245569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84935250231464628259321517 31850718836799235597245569)
  ·
    refine ⟨23888039127599426697934177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31850718836799235597245569 23888039127599426697934177)
    ·
      refine ⟨17916029345699570023450633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23888039127599426697934177 17916029345699570023450633)
      ·
        refine ⟨13437022009274677517587975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17916029345699570023450633 13437022009274677517587975)
        ·
          refine ⟨20155533013912016276381963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13437022009274677517587975 20155533013912016276381963)
          ·
            refine ⟨30233299520868024414572945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20155533013912016276381963 30233299520868024414572945)
            ·
              refine ⟨22674974640651018310929709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30233299520868024414572945 22674974640651018310929709)
              ·
                refine ⟨8503115490244131866598641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22674974640651018310929709 8503115490244131866598641)
                ·
                  refine ⟨6377336617683098899948981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8503115490244131866598641 6377336617683098899948981)
                  ·
                    refine ⟨597875307907790521870217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6377336617683098899948981 597875307907790521870217)
                    ·
                      rfl

theorem cell23_3493074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3493074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493074 prefixEnd_3493074 := by exact prefixLift 3493074
  have htrace : WordTrace (prefixWord ++ tailWord_3493074) baseStart_3493074 baseEnd_3493074 := by
    simpa [prefixWord, tailWord_3493074, baseEnd_3493074] using wordTrace_append hprefix tailTrace_3493074
  have hstable : (prefixWord ++ tailWord_3493074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493074).length < 2 ^ (prefixWord ++ tailWord_3493074).sum := by decide
  have hdescent : baseEnd_3493074 < baseStart_3493074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493114 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_3493114 : Nat := 118140960795 + 3493114 * 2 ^ 59
def prefixEnd_3493114 : Nat := 4983230072969 + 3 ^ 40 * 3493114 * 2
def baseEnd_3493114 : Nat := 1793646462949551409110467

theorem tailTrace_3493114 : CollatzResearch.WordTrace tailWord_3493114 prefixEnd_3493114 1793646462949551409110467 := by
  unfold tailWord_3493114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851083566763007305109599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84936222844701352813625597 31851083566763007305109599)
  ·
    refine ⟨47776625350144510957664399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31851083566763007305109599 47776625350144510957664399)
    ·
      refine ⟨71664938025216766436496599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47776625350144510957664399 71664938025216766436496599)
      ·
        refine ⟨107497407037825149654744899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71664938025216766436496599 107497407037825149654744899)
        ·
          refine ⟨161246110556737724482117349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107497407037825149654744899 161246110556737724482117349)
          ·
            refine ⟨30233645729388323340397003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161246110556737724482117349 30233645729388323340397003)
            ·
              refine ⟨45350468594082485010595505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30233645729388323340397003 45350468594082485010595505)
              ·
                refine ⟨34012851445561863757946629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45350468594082485010595505 34012851445561863757946629)
                ·
                  refine ⟨6377409646042849454614993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34012851445561863757946629 6377409646042849454614993)
                  ·
                    refine ⟨4783057234532137090961245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6377409646042849454614993 4783057234532137090961245)
                    ·
                      refine ⟨1793646462949551409110467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783057234532137090961245 1793646462949551409110467)
                      ·
                        rfl

theorem cell23_3493114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_3493114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493114 prefixEnd_3493114 := by exact prefixLift 3493114
  have htrace : WordTrace (prefixWord ++ tailWord_3493114) baseStart_3493114 baseEnd_3493114 := by
    simpa [prefixWord, tailWord_3493114, baseEnd_3493114] using wordTrace_append hprefix tailTrace_3493114
  have hstable : (prefixWord ++ tailWord_3493114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493114).length < 2 ^ (prefixWord ++ tailWord_3493114).sum := by decide
  have hdescent : baseEnd_3493114 < baseStart_3493114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493131 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 3]
def baseStart_3493131 : Nat := 118140960795 + 3493131 * 2 ^ 59
def prefixEnd_3493131 : Nat := 4983230072969 + 3 ^ 40 * 3493131 * 2
def baseEnd_3493131 : Nat := 1793655192120677842597889

theorem tailTrace_3493131 : CollatzResearch.WordTrace tailWord_3493131 prefixEnd_3493131 1793655192120677842597889 := by
  unfold tailWord_3493131
  simp only [CollatzResearch.WordTrace]
  refine ⟨127404954307990441123807247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84936636205326960749204831 127404954307990441123807247)
  ·
    refine ⟨191107431461985661685710871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127404954307990441123807247 191107431461985661685710871)
    ·
      refine ⟨286661147192978492528566307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191107431461985661685710871 286661147192978492528566307)
      ·
        refine ⟨429991720789467738792849461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286661147192978492528566307 429991720789467738792849461)
        ·
          refine ⟨40311723824012600511829637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 429991720789467738792849461 40311723824012600511829637)
          ·
            refine ⟨7558448217002362595968057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40311723824012600511829637 7558448217002362595968057)
            ·
              refine ⟨5668836162751771946976043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7558448217002362595968057 5668836162751771946976043)
              ·
                refine ⟨8503254244127657920464065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668836162751771946976043 8503254244127657920464065)
                ·
                  refine ⟨6377440683095743440348049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8503254244127657920464065 6377440683095743440348049)
                  ·
                    refine ⟨4783080512321807580261037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6377440683095743440348049 4783080512321807580261037)
                    ·
                      refine ⟨1793655192120677842597889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783080512321807580261037 1793655192120677842597889)
                      ·
                        rfl

theorem cell23_3493131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 3].length) (baseStart_3493131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493131 prefixEnd_3493131 := by exact prefixLift 3493131
  have htrace : WordTrace (prefixWord ++ tailWord_3493131) baseStart_3493131 baseEnd_3493131 := by
    simpa [prefixWord, tailWord_3493131, baseEnd_3493131] using wordTrace_append hprefix tailTrace_3493131
  have hstable : (prefixWord ++ tailWord_3493131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493131).length < 2 ^ (prefixWord ++ tailWord_3493131).sum := by decide
  have hdescent : baseEnd_3493131 < baseStart_3493131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493151 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 6]
def baseStart_3493151 : Nat := 118140960795 + 3493151 * 2 ^ 59
def prefixEnd_3493151 : Nat := 4983230072969 + 3 ^ 40 * 3493151 * 2
def baseEnd_3493151 : Nat := 199296162414863084927533

theorem tailTrace_3493151 : CollatzResearch.WordTrace tailWord_3493151 prefixEnd_3493151 199296162414863084927533 := by
  unfold tailWord_3493151
  simp only [CollatzResearch.WordTrace]
  refine ⟨127405683767917984539535307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84937122511945323026356871 127405683767917984539535307)
  ·
    refine ⟨191108525651876976809302961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127405683767917984539535307 191108525651876976809302961)
    ·
      refine ⟨143331394238907732606977221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191108525651876976809302961 143331394238907732606977221)
      ·
        refine ⟨26874636419795199863808229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143331394238907732606977221 26874636419795199863808229)
        ·
          refine ⟨5038994328711599974464043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26874636419795199863808229 5038994328711599974464043)
          ·
            refine ⟨7558491493067399961696065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038994328711599974464043 7558491493067399961696065)
            ·
              refine ⟨5668868619800549971272049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7558491493067399961696065 5668868619800549971272049)
              ·
                refine ⟨4251651464850412478454037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5668868619800549971272049 4251651464850412478454037)
                ·
                  refine ⟨199296162414863084927533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4251651464850412478454037 199296162414863084927533)
                  ·
                    rfl

theorem cell23_3493151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 6].length) (baseStart_3493151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493151 prefixEnd_3493151 := by exact prefixLift 3493151
  have htrace : WordTrace (prefixWord ++ tailWord_3493151) baseStart_3493151 baseEnd_3493151 := by
    simpa [prefixWord, tailWord_3493151, baseEnd_3493151] using wordTrace_append hprefix tailTrace_3493151
  have hstable : (prefixWord ++ tailWord_3493151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493151).length < 2 ^ (prefixWord ++ tailWord_3493151).sum := by decide
  have hdescent : baseEnd_3493151 < baseStart_3493151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493155 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 1, 4]
def baseStart_3493155 : Nat := 118140960795 + 3493155 * 2 ^ 59
def prefixEnd_3493155 : Nat := 4983230072969 + 3 ^ 40 * 3493155 * 2
def baseEnd_3493155 : Nat := 597889171885461916232593

theorem tailTrace_3493155 : CollatzResearch.WordTrace tailWord_3493155 prefixEnd_3493155 597889171885461916232593 := by
  unfold tailWord_3493155
  simp only [CollatzResearch.WordTrace]
  refine ⟨127405829659903493222680919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84937219773268995481787279 127405829659903493222680919)
  ·
    refine ⟨191108744489855239834021379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127405829659903493222680919 191108744489855239834021379)
    ·
      refine ⟨286663116734782859751032069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191108744489855239834021379 286663116734782859751032069)
      ·
        refine ⟨53749334387771786203318513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286663116734782859751032069 53749334387771786203318513)
        ·
          refine ⟨40312000790828839652488885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53749334387771786203318513 40312000790828839652488885)
          ·
            refine ⟨3779250074140203717420833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40312000790828839652488885 3779250074140203717420833)
            ·
              refine ⟨2834437555605152788065625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779250074140203717420833 2834437555605152788065625)
              ·
                refine ⟨2125828166703864591049219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834437555605152788065625 2125828166703864591049219)
                ·
                  refine ⟨3188742250055796886573829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125828166703864591049219 3188742250055796886573829)
                  ·
                    refine ⟨597889171885461916232593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3188742250055796886573829 597889171885461916232593)
                    ·
                      rfl

theorem cell23_3493155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 4].length) (baseStart_3493155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493155 prefixEnd_3493155 := by exact prefixLift 3493155
  have htrace : WordTrace (prefixWord ++ tailWord_3493155) baseStart_3493155 baseEnd_3493155 := by
    simpa [prefixWord, tailWord_3493155, baseEnd_3493155] using wordTrace_append hprefix tailTrace_3493155
  have hstable : (prefixWord ++ tailWord_3493155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493155).length < 2 ^ (prefixWord ++ tailWord_3493155).sum := by decide
  have hdescent : baseEnd_3493155 < baseStart_3493155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493184 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_3493184 : Nat := 118140960795 + 3493184 * 2 ^ 59
def prefixEnd_3493184 : Nat := 4983230072969 + 3 ^ 40 * 3493184 * 2
def baseEnd_3493184 : Nat := 1793682406595366135235145

theorem tailTrace_3493184 : CollatzResearch.WordTrace tailWord_3493184 prefixEnd_3493184 1793682406595366135235145 := by
  unfold tailWord_3493184
  simp only [CollatzResearch.WordTrace]
  refine ⟨63703443688399215587743303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84937924917865620783657737 63703443688399215587743303)
  ·
    refine ⟨95555165532598823381614955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63703443688399215587743303 95555165532598823381614955)
    ·
      refine ⟨143332748298898235072422433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95555165532598823381614955 143332748298898235072422433)
      ·
        refine ⟨107499561224173676304316825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143332748298898235072422433 107499561224173676304316825)
        ·
          refine ⟨80624670918130257228237619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107499561224173676304316825 80624670918130257228237619)
          ·
            refine ⟨120937006377195385842356429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80624670918130257228237619 120937006377195385842356429)
            ·
              refine ⟨45351377391448269690883661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120937006377195385842356429 45351377391448269690883661)
              ·
                refine ⟨17006766521793101134081373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45351377391448269690883661 17006766521793101134081373)
                ·
                  refine ⟨6377537445672412925280515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17006766521793101134081373 6377537445672412925280515)
                  ·
                    refine ⟨9566306168508619387920773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6377537445672412925280515 9566306168508619387920773)
                    ·
                      refine ⟨1793682406595366135235145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9566306168508619387920773 1793682406595366135235145)
                      ·
                        rfl

theorem cell23_3493184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_3493184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493184 prefixEnd_3493184 := by exact prefixLift 3493184
  have htrace : WordTrace (prefixWord ++ tailWord_3493184) baseStart_3493184 baseEnd_3493184 := by
    simpa [prefixWord, tailWord_3493184, baseEnd_3493184] using wordTrace_append hprefix tailTrace_3493184
  have hstable : (prefixWord ++ tailWord_3493184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493184).length < 2 ^ (prefixWord ++ tailWord_3493184).sum := by decide
  have hdescent : baseEnd_3493184 < baseStart_3493184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493201 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_3493201 : Nat := 118140960795 + 3493201 * 2 ^ 59
def prefixEnd_3493201 : Nat := 4983230072969 + 3 ^ 40 * 3493201 * 2
def baseEnd_3493201 : Nat := 1793691135766492568722567

theorem tailTrace_3493201 : CollatzResearch.WordTrace tailWord_3493201 prefixEnd_3493201 1793691135766492568722567 := by
  unfold tailWord_3493201
  simp only [CollatzResearch.WordTrace]
  refine ⟨127407507417736843078855457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84938338278491228719236971 127407507417736843078855457)
  ·
    refine ⟨95555630563302632309141593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127407507417736843078855457 95555630563302632309141593)
    ·
      refine ⟨71666722922476974231856195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95555630563302632309141593 71666722922476974231856195)
      ·
        refine ⟨107500084383715461347784293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71666722922476974231856195 107500084383715461347784293)
        ·
          refine ⟨20156265821946649002709555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107500084383715461347784293 20156265821946649002709555)
          ·
            refine ⟨30234398732919973504064333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20156265821946649002709555 30234398732919973504064333)
            ·
              refine ⟨11337899524844990064024125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30234398732919973504064333 11337899524844990064024125)
              ·
                refine ⟨4251712321816871274009047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11337899524844990064024125 4251712321816871274009047)
                ·
                  refine ⟨6377568482725306911013571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251712321816871274009047 6377568482725306911013571)
                  ·
                    refine ⟨9566352724087960366520357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6377568482725306911013571 9566352724087960366520357)
                    ·
                      refine ⟨1793691135766492568722567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9566352724087960366520357 1793691135766492568722567)
                      ·
                        rfl

theorem cell23_3493201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_3493201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493201 prefixEnd_3493201 := by exact prefixLift 3493201
  have htrace : WordTrace (prefixWord ++ tailWord_3493201) baseStart_3493201 baseEnd_3493201 := by
    simpa [prefixWord, tailWord_3493201, baseEnd_3493201] using wordTrace_append hprefix tailTrace_3493201
  have hstable : (prefixWord ++ tailWord_3493201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493201).length < 2 ^ (prefixWord ++ tailWord_3493201).sum := by decide
  have hdescent : baseEnd_3493201 < baseStart_3493201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493246 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3493246 : Nat := 118140960795 + 3493246 * 2 ^ 59
def prefixEnd_3493246 : Nat := 4983230072969 + 3 ^ 40 * 3493246 * 2
def baseEnd_3493246 : Nat := 1793714242395944892659861

theorem tailTrace_3493246 : CollatzResearch.WordTrace tailWord_3493246 prefixEnd_3493246 1793714242395944892659861 := by
  unfold tailWord_3493246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926143587821726970530449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84939432468382543842829061 15926143587821726970530449)
  ·
    refine ⟨11944607690866295227897837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15926143587821726970530449 11944607690866295227897837)
    ·
      refine ⟨4479227884074860710461689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11944607690866295227897837 4479227884074860710461689)
      ·
        refine ⟨3359420913056145532846267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4479227884074860710461689 3359420913056145532846267)
        ·
          refine ⟨5039131369584218299269401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359420913056145532846267 5039131369584218299269401)
          ·
            refine ⟨3779348527188163724452051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5039131369584218299269401 3779348527188163724452051)
            ·
              refine ⟨5669022790782245586678077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779348527188163724452051 5669022790782245586678077)
              ·
                refine ⟨2125883546543342095004279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5669022790782245586678077 2125883546543342095004279)
                ·
                  refine ⟨3188825319815013142506419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125883546543342095004279 3188825319815013142506419)
                  ·
                    refine ⟨4783237979722519713759629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3188825319815013142506419 4783237979722519713759629)
                    ·
                      refine ⟨1793714242395944892659861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783237979722519713759629 1793714242395944892659861)
                      ·
                        rfl

theorem cell23_3493246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3493246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493246 prefixEnd_3493246 := by exact prefixLift 3493246
  have htrace : WordTrace (prefixWord ++ tailWord_3493246) baseStart_3493246 baseEnd_3493246 := by
    simpa [prefixWord, tailWord_3493246, baseEnd_3493246] using wordTrace_append hprefix tailTrace_3493246
  have hstable : (prefixWord ++ tailWord_3493246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493246).length < 2 ^ (prefixWord ++ tailWord_3493246).sum := by decide
  have hdescent : baseEnd_3493246 < baseStart_3493246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493252 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_3493252 : Nat := 118140960795 + 3493252 * 2 ^ 59
def prefixEnd_3493252 : Nat := 4983230072969 + 3 ^ 40 * 3493252 * 2
def baseEnd_3493252 : Nat := 1793717323279871869184833

theorem tailTrace_3493252 : CollatzResearch.WordTrace tailWord_3493252 prefixEnd_3493252 1793717323279871869184833 := by
  unfold tailWord_3493252
  simp only [CollatzResearch.WordTrace]
  refine ⟨63704683770276039394481005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84939578360368052525974673 63704683770276039394481005)
  ·
    refine ⟨23889256413853514772930377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63704683770276039394481005 23889256413853514772930377)
    ·
      refine ⟨17916942310390136079697783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23889256413853514772930377 17916942310390136079697783)
      ·
        refine ⟨26875413465585204119546675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17916942310390136079697783 26875413465585204119546675)
        ·
          refine ⟨40313120198377806179320013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26875413465585204119546675 40313120198377806179320013)
          ·
            refine ⟨15117420074391677317245005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40313120198377806179320013 15117420074391677317245005)
            ·
              refine ⟨5669032527896878993966877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15117420074391677317245005 5669032527896878993966877)
              ·
                refine ⟨2125887197961329622737579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5669032527896878993966877 2125887197961329622737579)
                ·
                  refine ⟨3188830796941994434106369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125887197961329622737579 3188830796941994434106369)
                  ·
                    refine ⟨2391623097706495825579777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3188830796941994434106369 2391623097706495825579777)
                    ·
                      refine ⟨1793717323279871869184833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391623097706495825579777 1793717323279871869184833)
                      ·
                        rfl

theorem cell23_3493252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_3493252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493252 prefixEnd_3493252 := by exact prefixLift 3493252
  have htrace : WordTrace (prefixWord ++ tailWord_3493252) baseStart_3493252 baseEnd_3493252 := by
    simpa [prefixWord, tailWord_3493252, baseEnd_3493252] using wordTrace_append hprefix tailTrace_3493252
  have hstable : (prefixWord ++ tailWord_3493252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493252).length < 2 ^ (prefixWord ++ tailWord_3493252).sum := by decide
  have hdescent : baseEnd_3493252 < baseStart_3493252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493284 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_3493284 : Nat := 118140960795 + 3493284 * 2 ^ 59
def prefixEnd_3493284 : Nat := 4983230072969 + 3 ^ 40 * 3493284 * 2
def baseEnd_3493284 : Nat := 597911251553605247994895

theorem tailTrace_3493284 : CollatzResearch.WordTrace tailWord_3493284 prefixEnd_3493284 597911251553605247994895 := by
  unfold tailWord_3493284
  simp only [CollatzResearch.WordTrace]
  refine ⟨63705267338218074127063453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84940356450957432169417937 63705267338218074127063453)
  ·
    refine ⟨23889475251831777797648795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63705267338218074127063453 23889475251831777797648795)
    ·
      refine ⟨35834212877747666696473193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23889475251831777797648795 35834212877747666696473193)
      ·
        refine ⟨26875659658310750022354895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35834212877747666696473193 26875659658310750022354895)
        ·
          refine ⟨40313489487466125033532343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26875659658310750022354895 40313489487466125033532343)
          ·
            refine ⟨60470234231199187550298515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40313489487466125033532343 60470234231199187550298515)
            ·
              refine ⟨90705351346798781325447773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60470234231199187550298515 90705351346798781325447773)
              ·
                refine ⟨34014506755049542997042915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90705351346798781325447773 34014506755049542997042915)
                ·
                  refine ⟨51021760132574314495564373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34014506755049542997042915 51021760132574314495564373)
                  ·
                    refine ⟨597911251553605247994895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51021760132574314495564373 597911251553605247994895)
                    ·
                      rfl

theorem cell23_3493284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_3493284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493284 prefixEnd_3493284 := by exact prefixLift 3493284
  have htrace : WordTrace (prefixWord ++ tailWord_3493284) baseStart_3493284 baseEnd_3493284 := by
    simpa [prefixWord, tailWord_3493284, baseEnd_3493284] using wordTrace_append hprefix tailTrace_3493284
  have hstable : (prefixWord ++ tailWord_3493284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493284).length < 2 ^ (prefixWord ++ tailWord_3493284).sum := by decide
  have hdescent : baseEnd_3493284 < baseStart_3493284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493361 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_3493361 : Nat := 118140960795 + 3493361 * 2 ^ 59
def prefixEnd_3493361 : Nat := 4983230072969 + 3 ^ 40 * 3493361 * 2
def baseEnd_3493361 : Nat := 597924430890403980907277

theorem tailTrace_3493361 : CollatzResearch.WordTrace tailWord_3493361 prefixEnd_3493361 597924430890403980907277 := by
  unfold tailWord_3493361
  simp only [CollatzResearch.WordTrace]
  refine ⟨127413343097157190404679937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84942228731438126936453291 127413343097157190404679937)
  ·
    refine ⟨95560007322867892803509953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127413343097157190404679937 95560007322867892803509953)
    ·
      refine ⟨71670005492150919602632465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95560007322867892803509953 71670005492150919602632465)
      ·
        refine ⟨53752504119113189701974349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71670005492150919602632465 53752504119113189701974349)
        ·
          refine ⟨20157189044667446138240381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53752504119113189701974349 20157189044667446138240381)
          ·
            refine ⟨7558945891750292301840143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20157189044667446138240381 7558945891750292301840143)
            ·
              refine ⟨11338418837625438452760215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558945891750292301840143 11338418837625438452760215)
              ·
                refine ⟨17007628256438157679140323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11338418837625438452760215 17007628256438157679140323)
                ·
                  refine ⟨25511442384657236518710485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17007628256438157679140323 25511442384657236518710485)
                  ·
                    refine ⟨597924430890403980907277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25511442384657236518710485 597924430890403980907277)
                    ·
                      rfl

theorem cell23_3493361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_3493361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493361 prefixEnd_3493361 := by exact prefixLift 3493361
  have htrace : WordTrace (prefixWord ++ tailWord_3493361) baseStart_3493361 baseEnd_3493361 := by
    simpa [prefixWord, tailWord_3493361, baseEnd_3493361] using wordTrace_append hprefix tailTrace_3493361
  have hstable : (prefixWord ++ tailWord_3493361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493361).length < 2 ^ (prefixWord ++ tailWord_3493361).sum := by decide
  have hdescent : baseEnd_3493361 < baseStart_3493361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493365 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 5]
def baseStart_3493365 : Nat := 118140960795 + 3493365 * 2 ^ 59
def prefixEnd_3493365 : Nat := 4983230072969 + 3 ^ 40 * 3493365 * 2
def baseEnd_3493365 : Nat := 199308371843758880785757

theorem tailTrace_3493365 : CollatzResearch.WordTrace tailWord_3493365 prefixEnd_3493365 199308371843758880785757 := by
  unfold tailWord_3493365
  simp only [CollatzResearch.WordTrace]
  refine ⟨127413488989142699087825549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84942325992761799391883699 127413488989142699087825549)
  ·
    refine ⟨47780058370928512157934581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127413488989142699087825549 47780058370928512157934581)
    ·
      refine ⟨4479380472274548014806367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47780058370928512157934581 4479380472274548014806367)
      ·
        refine ⟨6719070708411822022209551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479380472274548014806367 6719070708411822022209551)
        ·
          refine ⟨10078606062617733033314327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719070708411822022209551 10078606062617733033314327)
          ·
            refine ⟨15117909093926599549971491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10078606062617733033314327 15117909093926599549971491)
            ·
              refine ⟨22676863640889899324957237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15117909093926599549971491 22676863640889899324957237)
              ·
                refine ⟨2125955966333428061714741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22676863640889899324957237 2125955966333428061714741)
                ·
                  refine ⟨199308371843758880785757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2125955966333428061714741 199308371843758880785757)
                  ·
                    rfl

theorem cell23_3493365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_3493365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493365 prefixEnd_3493365 := by exact prefixLift 3493365
  have htrace : WordTrace (prefixWord ++ tailWord_3493365) baseStart_3493365 baseEnd_3493365 := by
    simpa [prefixWord, tailWord_3493365, baseEnd_3493365] using wordTrace_append hprefix tailTrace_3493365
  have hstable : (prefixWord ++ tailWord_3493365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493365).length < 2 ^ (prefixWord ++ tailWord_3493365).sum := by decide
  have hdescent : baseEnd_3493365 < baseStart_3493365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493381 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_3493381 : Nat := 118140960795 + 3493381 * 2 ^ 59
def prefixEnd_3493381 : Nat := 4983230072969 + 3 ^ 40 * 3493381 * 2
def baseEnd_3493381 : Nat := 1793783562284301864471739

theorem tailTrace_3493381 : CollatzResearch.WordTrace tailWord_3493381 prefixEnd_3493381 1793783562284301864471739 := by
  unfold tailWord_3493381
  simp only [CollatzResearch.WordTrace]
  refine ⟨127414072557084733820407997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84942715038056489213605331 127414072557084733820407997)
  ·
    refine ⟨47780277208906775182652999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127414072557084733820407997 47780277208906775182652999)
    ·
      refine ⟨71670415813360162773979499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47780277208906775182652999 71670415813360162773979499)
      ·
        refine ⟨107505623720040244160969249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71670415813360162773979499 107505623720040244160969249)
        ·
          refine ⟨80629217790030183120726937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107505623720040244160969249 80629217790030183120726937)
          ·
            refine ⟨60471913342522637340545203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80629217790030183120726937 60471913342522637340545203)
            ·
              refine ⟨90707870013783956010817805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60471913342522637340545203 90707870013783956010817805)
              ·
                refine ⟨34015451255168983504056677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90707870013783956010817805 34015451255168983504056677)
                ·
                  refine ⟨6377897110344184407010627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34015451255168983504056677 6377897110344184407010627)
                  ·
                    refine ⟨9566845665516276610515941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6377897110344184407010627 9566845665516276610515941)
                    ·
                      refine ⟨1793783562284301864471739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9566845665516276610515941 1793783562284301864471739)
                      ·
                        rfl

theorem cell23_3493381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_3493381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493381 prefixEnd_3493381 := by exact prefixLift 3493381
  have htrace : WordTrace (prefixWord ++ tailWord_3493381) baseStart_3493381 baseEnd_3493381 := by
    simpa [prefixWord, tailWord_3493381, baseEnd_3493381] using wordTrace_append hprefix tailTrace_3493381
  have hstable : (prefixWord ++ tailWord_3493381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493381).length < 2 ^ (prefixWord ++ tailWord_3493381).sum := by decide
  have hdescent : baseEnd_3493381 < baseStart_3493381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493418 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3493418 : Nat := 118140960795 + 3493418 * 2 ^ 59
def prefixEnd_3493418 : Nat := 4983230072969 + 3 ^ 40 * 3493418 * 2
def baseEnd_3493418 : Nat := 1793802561068518219709069

theorem tailTrace_3493418 : CollatzResearch.WordTrace tailWord_3493418 prefixEnd_3493418 1793802561068518219709069 := by
  unfold tailWord_3493418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31853855514487672284876227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84943614705300459426336605 31853855514487672284876227)
  ·
    refine ⟨47780783271731508427314341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31853855514487672284876227 47780783271731508427314341)
    ·
      refine ⟨8958896863449657830121439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47780783271731508427314341 8958896863449657830121439)
      ·
        refine ⟨13438345295174486745182159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958896863449657830121439 13438345295174486745182159)
        ·
          refine ⟨20157517942761730117773239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438345295174486745182159 20157517942761730117773239)
          ·
            refine ⟨30236276914142595176659859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20157517942761730117773239 30236276914142595176659859)
            ·
              refine ⟨45354415371213892764989789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30236276914142595176659859 45354415371213892764989789)
              ·
                refine ⟨17007905764205209786871171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45354415371213892764989789 17007905764205209786871171)
                ·
                  refine ⟨25511858646307814680306757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17007905764205209786871171 25511858646307814680306757)
                  ·
                    refine ⟨4783473496182715252557517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25511858646307814680306757 4783473496182715252557517)
                    ·
                      refine ⟨1793802561068518219709069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783473496182715252557517 1793802561068518219709069)
                      ·
                        rfl

theorem cell23_3493418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3493418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493418 prefixEnd_3493418 := by exact prefixLift 3493418
  have htrace : WordTrace (prefixWord ++ tailWord_3493418) baseStart_3493418 baseEnd_3493418 := by
    simpa [prefixWord, tailWord_3493418, baseEnd_3493418] using wordTrace_append hprefix tailTrace_3493418
  have hstable : (prefixWord ++ tailWord_3493418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493418).length < 2 ^ (prefixWord ++ tailWord_3493418).sum := by decide
  have hdescent : baseEnd_3493418 < baseStart_3493418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493451 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 3, 5]
def baseStart_3493451 : Nat := 118140960795 + 3493451 * 2 ^ 59
def prefixEnd_3493451 : Nat := 4983230072969 + 3 ^ 40 * 3493451 * 2
def baseEnd_3493451 : Nat := 597939835310038863532139

theorem tailTrace_3493451 : CollatzResearch.WordTrace tailWord_3493451 prefixEnd_3493451 597939835310038863532139 := by
  unfold tailWord_3493451
  simp only [CollatzResearch.WordTrace]
  refine ⟨127416625666831135775456207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84944417111220757183637471 127416625666831135775456207)
  ·
    refine ⟨191124938500246703663184311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127416625666831135775456207 191124938500246703663184311)
    ·
      refine ⟨286687407750370055494776467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191124938500246703663184311 286687407750370055494776467)
      ·
        refine ⟨430031111625555083242164701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286687407750370055494776467 430031111625555083242164701)
        ·
          refine ⟨161261666859583156215811763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430031111625555083242164701 161261666859583156215811763)
          ·
            refine ⟨241892500289374734323717645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161261666859583156215811763 241892500289374734323717645)
            ·
              refine ⟨90709687608515525371394117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241892500289374734323717645 90709687608515525371394117)
              ·
                refine ⟨17008066426596661007136397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90709687608515525371394117 17008066426596661007136397)
                ·
                  refine ⟨6378024909973747877676149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17008066426596661007136397 6378024909973747877676149)
                  ·
                    refine ⟨597939835310038863532139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6378024909973747877676149 597939835310038863532139)
                    ·
                      rfl

theorem cell23_3493451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 5].length) (baseStart_3493451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493451 prefixEnd_3493451 := by exact prefixLift 3493451
  have htrace : WordTrace (prefixWord ++ tailWord_3493451) baseStart_3493451 baseEnd_3493451 := by
    simpa [prefixWord, tailWord_3493451, baseEnd_3493451] using wordTrace_append hprefix tailTrace_3493451
  have hstable : (prefixWord ++ tailWord_3493451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493451).length < 2 ^ (prefixWord ++ tailWord_3493451).sum := by decide
  have hdescent : baseEnd_3493451 < baseStart_3493451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493469 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3493469 : Nat := 118140960795 + 3493469 * 2 ^ 59
def prefixEnd_3493469 : Nat := 4983230072969 + 3 ^ 40 * 3493469 * 2
def baseEnd_3493469 : Nat := 1793828748581897520171335

theorem tailTrace_3493469 : CollatzResearch.WordTrace tailWord_3493469 prefixEnd_3493469 1793828748581897520171335 := by
  unfold tailWord_3493469
  simp only [CollatzResearch.WordTrace]
  refine ⟨127417282180765924849611461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84944854787177283233074307 127417282180765924849611461)
  ·
    refine ⟨23890740408893610909302149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127417282180765924849611461 23890740408893610909302149)
    ·
      refine ⟨4479513826667552045494153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23890740408893610909302149 4479513826667552045494153)
      ·
        refine ⟨3359635370000664034120615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4479513826667552045494153 3359635370000664034120615)
        ·
          refine ⟨5039453055000996051180923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359635370000664034120615 5039453055000996051180923)
          ·
            refine ⟨7559179582501494076771385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039453055000996051180923 7559179582501494076771385)
            ·
              refine ⟨5669384686876120557578539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559179582501494076771385 5669384686876120557578539)
              ·
                refine ⟨8504077030314180836367809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669384686876120557578539 8504077030314180836367809)
                ·
                  refine ⟨6378057772735635627275857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8504077030314180836367809 6378057772735635627275857)
                  ·
                    refine ⟨4783543329551726720456893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6378057772735635627275857 4783543329551726720456893)
                    ·
                      refine ⟨1793828748581897520171335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783543329551726720456893 1793828748581897520171335)
                      ·
                        rfl

theorem cell23_3493469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3493469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493469 prefixEnd_3493469 := by exact prefixLift 3493469
  have htrace : WordTrace (prefixWord ++ tailWord_3493469) baseStart_3493469 baseEnd_3493469 := by
    simpa [prefixWord, tailWord_3493469, baseEnd_3493469] using wordTrace_append hprefix tailTrace_3493469
  have hstable : (prefixWord ++ tailWord_3493469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493469).length < 2 ^ (prefixWord ++ tailWord_3493469).sum := by decide
  have hdescent : baseEnd_3493469 < baseStart_3493469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493475 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 2, 3, 2]
def baseStart_3493475 : Nat := 118140960795 + 3493475 * 2 ^ 59
def prefixEnd_3493475 : Nat := 4983230072969 + 3 ^ 40 * 3493475 * 2
def baseEnd_3493475 : Nat := 1793831829465824496696307

theorem tailTrace_3493475 : CollatzResearch.WordTrace tailWord_3493475 prefixEnd_3493475 1793831829465824496696307 := by
  unfold tailWord_3493475
  simp only [CollatzResearch.WordTrace]
  refine ⟨127417501018744187874329879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84945000679162791916219919 127417501018744187874329879)
  ·
    refine ⟨191126251528116281811494819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127417501018744187874329879 191126251528116281811494819)
    ·
      refine ⟨286689377292174422717242229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191126251528116281811494819 286689377292174422717242229)
      ·
        refine ⟨26877129121141352129741459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 286689377292174422717242229 26877129121141352129741459)
        ·
          refine ⟨40315693681712028194612189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26877129121141352129741459 40315693681712028194612189)
          ·
            refine ⟨15118385130642010572979571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40315693681712028194612189 15118385130642010572979571)
            ·
              refine ⟨22677577695963015859469357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15118385130642010572979571 22677577695963015859469357)
              ·
                refine ⟨8504091635986130947301009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22677577695963015859469357 8504091635986130947301009)
                ·
                  refine ⟨6378068726989598210475757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8504091635986130947301009 6378068726989598210475757)
                  ·
                    refine ⟨2391775772621099328928409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6378068726989598210475757 2391775772621099328928409)
                    ·
                      refine ⟨1793831829465824496696307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391775772621099328928409 1793831829465824496696307)
                      ·
                        rfl

theorem cell23_3493475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_3493475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493475 prefixEnd_3493475 := by exact prefixLift 3493475
  have htrace : WordTrace (prefixWord ++ tailWord_3493475) baseStart_3493475 baseEnd_3493475 := by
    simpa [prefixWord, tailWord_3493475, baseEnd_3493475] using wordTrace_append hprefix tailTrace_3493475
  have hstable : (prefixWord ++ tailWord_3493475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493475).length < 2 ^ (prefixWord ++ tailWord_3493475).sum := by decide
  have hdescent : baseEnd_3493475 < baseStart_3493475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493481 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_3493481 : Nat := 118140960795 + 3493481 * 2 ^ 59
def prefixEnd_3493481 : Nat := 4983230072969 + 3 ^ 40 * 3493481 * 2
def baseEnd_3493481 : Nat := 597944970116583824407093

theorem tailTrace_3493481 : CollatzResearch.WordTrace tailWord_3493481 prefixEnd_3493481 597944970116583824407093 := by
  unfold tailWord_3493481
  simp only [CollatzResearch.WordTrace]
  refine ⟨127417719856722450899048297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84945146571148300599365531 127417719856722450899048297)
  ·
    refine ⟨95563289892541838174286223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127417719856722450899048297 95563289892541838174286223)
    ·
      refine ⟨143344934838812757261429335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95563289892541838174286223 143344934838812757261429335)
      ·
        refine ⟨215017402258219135892144003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143344934838812757261429335 215017402258219135892144003)
        ·
          refine ⟨322526103387328703838216005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215017402258219135892144003 322526103387328703838216005)
          ·
            refine ⟨60473644385124131969665501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322526103387328703838216005 60473644385124131969665501)
            ·
              refine ⟨22677616644421549488624563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60473644385124131969665501 22677616644421549488624563)
              ·
                refine ⟨34016424966632324232936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22677616644421549488624563 34016424966632324232936845)
                ·
                  refine ⟨12756159362487121587351317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34016424966632324232936845 12756159362487121587351317)
                  ·
                    refine ⟨597944970116583824407093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12756159362487121587351317 597944970116583824407093)
                    ·
                      rfl

theorem cell23_3493481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_3493481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493481 prefixEnd_3493481 := by exact prefixLift 3493481
  have htrace : WordTrace (prefixWord ++ tailWord_3493481) baseStart_3493481 baseEnd_3493481 := by
    simpa [prefixWord, tailWord_3493481, baseEnd_3493481] using wordTrace_append hprefix tailTrace_3493481
  have hstable : (prefixWord ++ tailWord_3493481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493481).length < 2 ^ (prefixWord ++ tailWord_3493481).sum := by decide
  have hdescent : baseEnd_3493481 < baseStart_3493481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493539 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 1, 2, 2]
def baseStart_3493539 : Nat := 118140960795 + 3493539 * 2 ^ 59
def prefixEnd_3493539 : Nat := 4983230072969 + 3 ^ 40 * 3493539 * 2
def baseEnd_3493539 : Nat := 1793864692227712246296013

theorem tailTrace_3493539 : CollatzResearch.WordTrace tailWord_3493539 prefixEnd_3493539 1793864692227712246296013 := by
  unfold tailWord_3493539
  simp only [CollatzResearch.WordTrace]
  refine ⟨127419835290512326804659671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84946556860341551203106447 127419835290512326804659671)
  ·
    refine ⟨191129752935768490206989507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127419835290512326804659671 191129752935768490206989507)
    ·
      refine ⟨286694629403652735310484261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191129752935768490206989507 286694629403652735310484261)
      ·
        refine ⟨53755243013184887870715799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286694629403652735310484261 53755243013184887870715799)
        ·
          refine ⟨80632864519777331806073699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53755243013184887870715799 80632864519777331806073699)
          ·
            refine ⟨120949296779665997709110549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80632864519777331806073699 120949296779665997709110549)
            ·
              refine ⟨5669498286546843642614557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120949296779665997709110549 5669498286546843642614557)
              ·
                refine ⟨2126061857455066365980459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5669498286546843642614557 2126061857455066365980459)
                ·
                  refine ⟨3189092786182599548970689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126061857455066365980459 3189092786182599548970689)
                  ·
                    refine ⟨2391819589636949661728017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189092786182599548970689 2391819589636949661728017)
                    ·
                      refine ⟨1793864692227712246296013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391819589636949661728017 1793864692227712246296013)
                      ·
                        rfl

theorem cell23_3493539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_3493539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493539 prefixEnd_3493539 := by exact prefixLift 3493539
  have htrace : WordTrace (prefixWord ++ tailWord_3493539) baseStart_3493539 baseEnd_3493539 := by
    simpa [prefixWord, tailWord_3493539, baseEnd_3493539] using wordTrace_append hprefix tailTrace_3493539
  have hstable : (prefixWord ++ tailWord_3493539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493539).length < 2 ^ (prefixWord ++ tailWord_3493539).sum := by decide
  have hdescent : baseEnd_3493539 < baseStart_3493539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493555 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 3]
def baseStart_3493555 : Nat := 118140960795 + 3493555 * 2 ^ 59
def prefixEnd_3493555 : Nat := 4983230072969 + 3 ^ 40 * 3493555 * 2
def baseEnd_3493555 : Nat := 1793872907918184183695939

theorem tailTrace_3493555 : CollatzResearch.WordTrace tailWord_3493555 prefixEnd_3493555 1793872907918184183695939 := by
  unfold tailWord_3493555
  simp only [CollatzResearch.WordTrace]
  refine ⟨127420418858454361537242119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84946945905636241024828079 127420418858454361537242119)
  ·
    refine ⟨191130628287681542305863179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127420418858454361537242119 191130628287681542305863179)
    ·
      refine ⟨286695942431522313458794769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191130628287681542305863179 286695942431522313458794769)
      ·
        refine ⟨215021956823641735094096077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286695942431522313458794769 215021956823641735094096077)
        ·
          refine ⟨80633233808865650660286029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215021956823641735094096077 80633233808865650660286029)
          ·
            refine ⟨30237462678324618997607261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80633233808865650660286029 30237462678324618997607261)
            ·
              refine ⟨11339048504371732124102723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30237462678324618997607261 11339048504371732124102723)
              ·
                refine ⟨17008572756557598186154085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11339048504371732124102723 17008572756557598186154085)
                ·
                  refine ⟨3189107391854549659903891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17008572756557598186154085 3189107391854549659903891)
                  ·
                    refine ⟨4783661087781824489855837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189107391854549659903891 4783661087781824489855837)
                    ·
                      refine ⟨1793872907918184183695939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783661087781824489855837 1793872907918184183695939)
                      ·
                        rfl

theorem cell23_3493555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_3493555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493555 prefixEnd_3493555 := by exact prefixLift 3493555
  have htrace : WordTrace (prefixWord ++ tailWord_3493555) baseStart_3493555 baseEnd_3493555 := by
    simpa [prefixWord, tailWord_3493555, baseEnd_3493555] using wordTrace_append hprefix tailTrace_3493555
  have hstable : (prefixWord ++ tailWord_3493555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493555).length < 2 ^ (prefixWord ++ tailWord_3493555).sum := by decide
  have hdescent : baseEnd_3493555 < baseStart_3493555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493612 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 4, 2, 2]
def baseStart_3493612 : Nat := 118140960795 + 3493612 * 2 ^ 59
def prefixEnd_3493612 : Nat := 4983230072969 + 3 ^ 40 * 3493612 * 2
def baseEnd_3493612 : Nat := 1793902176315490460683177

theorem tailTrace_3493612 : CollatzResearch.WordTrace tailWord_3493612 prefixEnd_3493612 1793902176315490460683177 := by
  unfold tailWord_3493612
  simp only [CollatzResearch.WordTrace]
  refine ⟨63711248909623930136033545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84948331879498573514711393 63711248909623930136033545)
  ·
    refine ⟨47783436682217947602025159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63711248909623930136033545 47783436682217947602025159)
    ·
      refine ⟨71675155023326921403037739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47783436682217947602025159 71675155023326921403037739)
      ·
        refine ⟨107512732534990382104556609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71675155023326921403037739 107512732534990382104556609)
        ·
          refine ⟨80634549401242786578417457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107512732534990382104556609 80634549401242786578417457)
          ·
            refine ⟨60475912050932089933813093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80634549401242786578417457 60475912050932089933813093)
            ·
              refine ⟨11339233509549766862589955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60475912050932089933813093 11339233509549766862589955)
              ·
                refine ⟨17008850264324650293884933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11339233509549766862589955 17008850264324650293884933)
                ·
                  refine ⟨3189159424560871930103425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17008850264324650293884933 3189159424560871930103425)
                  ·
                    refine ⟨2391869568420653947577569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189159424560871930103425 2391869568420653947577569)
                    ·
                      refine ⟨1793902176315490460683177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391869568420653947577569 1793902176315490460683177)
                      ·
                        rfl

theorem cell23_3493612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_3493612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493612 prefixEnd_3493612 := by exact prefixLift 3493612
  have htrace : WordTrace (prefixWord ++ tailWord_3493612) baseStart_3493612 baseEnd_3493612 := by
    simpa [prefixWord, tailWord_3493612, baseEnd_3493612] using wordTrace_append hprefix tailTrace_3493612
  have hstable : (prefixWord ++ tailWord_3493612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493612).length < 2 ^ (prefixWord ++ tailWord_3493612).sum := by decide
  have hdescent : baseEnd_3493612 < baseStart_3493612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493665 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3493665 : Nat := 118140960795 + 3493665 * 2 ^ 59
def prefixEnd_3493665 : Nat := 4983230072969 + 3 ^ 40 * 3493665 * 2
def baseEnd_3493665 : Nat := 597976463596726251106811

theorem tailTrace_3493665 : CollatzResearch.WordTrace tailWord_3493665 prefixEnd_3493665 597976463596726251106811 := by
  unfold tailWord_3493665
  simp only [CollatzResearch.WordTrace]
  refine ⟨127424430888055850323746449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84949620592037233549164299 127424430888055850323746449)
  ·
    refine ⟨95568323166041887742809837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127424430888055850323746449 95568323166041887742809837)
    ·
      refine ⟨35838121187265707903553689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95568323166041887742809837 35838121187265707903553689)
      ·
        refine ⟨26878590890449280927665267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35838121187265707903553689 26878590890449280927665267)
        ·
          refine ⟨40317886335673921391497901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26878590890449280927665267 40317886335673921391497901)
          ·
            refine ⟨15119207375877720521811713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40317886335673921391497901 15119207375877720521811713)
            ·
              refine ⟨11339405531908290391358785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15119207375877720521811713 11339405531908290391358785)
              ·
                refine ⟨8504554148931217793519089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11339405531908290391358785 8504554148931217793519089)
                ·
                  refine ⟨6378415611698413345139317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8504554148931217793519089 6378415611698413345139317)
                  ·
                    refine ⟨597976463596726251106811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6378415611698413345139317 597976463596726251106811)
                    ·
                      rfl

theorem cell23_3493665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3493665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493665 prefixEnd_3493665 := by exact prefixLift 3493665
  have htrace : WordTrace (prefixWord ++ tailWord_3493665) baseStart_3493665 baseEnd_3493665 := by
    simpa [prefixWord, tailWord_3493665, baseEnd_3493665] using wordTrace_append hprefix tailTrace_3493665
  have hstable : (prefixWord ++ tailWord_3493665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493665).length < 2 ^ (prefixWord ++ tailWord_3493665).sum := by decide
  have hdescent : baseEnd_3493665 < baseStart_3493665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493669 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 5]
def baseStart_3493669 : Nat := 118140960795 + 3493669 * 2 ^ 59
def prefixEnd_3493669 : Nat := 4983230072969 + 3 ^ 40 * 3493669 * 2
def baseEnd_3493669 : Nat := 199325716079199637518935

theorem tailTrace_3493669 : CollatzResearch.WordTrace tailWord_3493669 prefixEnd_3493669 199325716079199637518935 := by
  unfold tailWord_3493669
  simp only [CollatzResearch.WordTrace]
  refine ⟨127424576780041359006892061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84949717853360906004594707 127424576780041359006892061)
  ·
    refine ⟨47784216292515509627584523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127424576780041359006892061 47784216292515509627584523)
    ·
      refine ⟨71676324438773264441376785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47784216292515509627584523 71676324438773264441376785)
      ·
        refine ⟨53757243329079948331032589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71676324438773264441376785 53757243329079948331032589)
        ·
          refine ⟨20158966248404980624137221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53757243329079948331032589 20158966248404980624137221)
          ·
            refine ⟨3779806171575933867025729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20158966248404980624137221 3779806171575933867025729)
            ·
              refine ⟨2834854628681950400269297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779806171575933867025729 2834854628681950400269297)
              ·
                refine ⟨2126140971511462800201973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834854628681950400269297 2126140971511462800201973)
                ·
                  refine ⟨199325716079199637518935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2126140971511462800201973 199325716079199637518935)
                  ·
                    rfl

theorem cell23_3493669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_3493669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493669 prefixEnd_3493669 := by exact prefixLift 3493669
  have htrace : WordTrace (prefixWord ++ tailWord_3493669) baseStart_3493669 baseEnd_3493669 := by
    simpa [prefixWord, tailWord_3493669, baseEnd_3493669] using wordTrace_append hprefix tailTrace_3493669
  have hstable : (prefixWord ++ tailWord_3493669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493669).length < 2 ^ (prefixWord ++ tailWord_3493669).sum := by decide
  have hdescent : baseEnd_3493669 < baseStart_3493669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493672 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_3493672 : Nat := 118140960795 + 3493672 * 2 ^ 59
def prefixEnd_3493672 : Nat := 4983230072969 + 3 ^ 40 * 3493672 * 2
def baseEnd_3493672 : Nat := 1793932985154760225932901

theorem tailTrace_3493672 : CollatzResearch.WordTrace tailWord_3493672 prefixEnd_3493672 1793932985154760225932901 := by
  unfold tailWord_3493672
  simp only [CollatzResearch.WordTrace]
  refine ⟨63712343099515245259625635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84949790799353660346167513 63712343099515245259625635)
  ·
    refine ⟨95568514649272867889438453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63712343099515245259625635 95568514649272867889438453)
    ·
      refine ⟨8959548248369331364634855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95568514649272867889438453 8959548248369331364634855)
      ·
        refine ⟨13439322372553997046952283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8959548248369331364634855 13439322372553997046952283)
        ·
          refine ⟨20158983558830995570428425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13439322372553997046952283 20158983558830995570428425)
          ·
            refine ⟨15119237669123246677821319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20158983558830995570428425 15119237669123246677821319)
            ·
              refine ⟨22678856503684870016731979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15119237669123246677821319 22678856503684870016731979)
              ·
                refine ⟨34018284755527305025097969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22678856503684870016731979 34018284755527305025097969)
                ·
                  refine ⟨25513713566645478768823477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34018284755527305025097969 25513713566645478768823477)
                  ·
                    refine ⟨2391910646873013634577201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25513713566645478768823477 2391910646873013634577201)
                    ·
                      refine ⟨1793932985154760225932901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2391910646873013634577201 1793932985154760225932901)
                      ·
                        rfl

theorem cell23_3493672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_3493672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493672 prefixEnd_3493672 := by exact prefixLift 3493672
  have htrace : WordTrace (prefixWord ++ tailWord_3493672) baseStart_3493672 baseEnd_3493672 := by
    simpa [prefixWord, tailWord_3493672, baseEnd_3493672] using wordTrace_append hprefix tailTrace_3493672
  have hstable : (prefixWord ++ tailWord_3493672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493672).length < 2 ^ (prefixWord ++ tailWord_3493672).sum := by decide
  have hdescent : baseEnd_3493672 < baseStart_3493672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493705 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_3493705 : Nat := 118140960795 + 3493705 * 2 ^ 59
def prefixEnd_3493705 : Nat := 4983230072969 + 3 ^ 40 * 3493705 * 2
def baseEnd_3493705 : Nat := 1793949930016358596820249

theorem tailTrace_3493705 : CollatzResearch.WordTrace tailWord_3493705 prefixEnd_3493705 1793949930016358596820249 := by
  unfold tailWord_3493705
  simp only [CollatzResearch.WordTrace]
  refine ⟨127425889807910937155202569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84950593205273958103468379 127425889807910937155202569)
  ·
    refine ⟨95569417355933202866401927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127425889807910937155202569 95569417355933202866401927)
    ·
      refine ⟨143354126033899804299602891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95569417355933202866401927 143354126033899804299602891)
      ·
        refine ⟨215031189050849706449404337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143354126033899804299602891 215031189050849706449404337)
        ·
          refine ⟨161273391788137279837053253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215031189050849706449404337 161273391788137279837053253)
          ·
            refine ⟨30238760960275739969447485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161273391788137279837053253 30238760960275739969447485)
            ·
              refine ⟨11339535360103402488542807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30238760960275739969447485 11339535360103402488542807)
              ·
                refine ⟨17009303040155103732814211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11339535360103402488542807 17009303040155103732814211)
                ·
                  refine ⟨25513954560232655599221317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17009303040155103732814211 25513954560232655599221317)
                  ·
                    refine ⟨4783866480043622924853997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25513954560232655599221317 4783866480043622924853997)
                    ·
                      refine ⟨1793949930016358596820249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783866480043622924853997 1793949930016358596820249)
                      ·
                        rfl

theorem cell23_3493705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_3493705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493705 prefixEnd_3493705 := by exact prefixLift 3493705
  have htrace : WordTrace (prefixWord ++ tailWord_3493705) baseStart_3493705 baseEnd_3493705 := by
    simpa [prefixWord, tailWord_3493705, baseEnd_3493705] using wordTrace_append hprefix tailTrace_3493705
  have hstable : (prefixWord ++ tailWord_3493705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493705).length < 2 ^ (prefixWord ++ tailWord_3493705).sum := by decide
  have hdescent : baseEnd_3493705 < baseStart_3493705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493786 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3493786 : Nat := 118140960795 + 3493786 * 2 ^ 59
def prefixEnd_3493786 : Nat := 4983230072969 + 3 ^ 40 * 3493786 * 2
def baseEnd_3493786 : Nat := 1793991521949372779907377

theorem tailTrace_3493786 : CollatzResearch.WordTrace tailWord_3493786 prefixEnd_3493786 1793991521949372779907377 := by
  unfold tailWord_3493786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31857211030154371997225303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84952562747078325325934141 31857211030154371997225303)
  ·
    refine ⟨47785816545231557995837955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31857211030154371997225303 47785816545231557995837955)
    ·
      refine ⟨71678724817847336993756933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47785816545231557995837955 71678724817847336993756933)
      ·
        refine ⟨13439760903346375686329425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71678724817847336993756933 13439760903346375686329425)
        ·
          refine ⟨10079820677509781764747069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13439760903346375686329425 10079820677509781764747069)
          ·
            refine ⟨3779932754066168161780151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10079820677509781764747069 3779932754066168161780151)
            ·
              refine ⟨5669899131099252242670227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779932754066168161780151 5669899131099252242670227)
              ·
                refine ⟨8504848696648878364005341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669899131099252242670227 8504848696648878364005341)
                ·
                  refine ⟨3189318261243329386502003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8504848696648878364005341 3189318261243329386502003)
                  ·
                    refine ⟨4783977391864994079753005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189318261243329386502003 4783977391864994079753005)
                    ·
                      refine ⟨1793991521949372779907377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783977391864994079753005 1793991521949372779907377)
                      ·
                        rfl

theorem cell23_3493786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3493786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493786 prefixEnd_3493786 := by exact prefixLift 3493786
  have htrace : WordTrace (prefixWord ++ tailWord_3493786) baseStart_3493786 baseEnd_3493786 := by
    simpa [prefixWord, tailWord_3493786, baseEnd_3493786] using wordTrace_append hprefix tailTrace_3493786
  have hstable : (prefixWord ++ tailWord_3493786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493786).length < 2 ^ (prefixWord ++ tailWord_3493786).sum := by decide
  have hdescent : baseEnd_3493786 < baseStart_3493786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493795 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 3]
def baseStart_3493795 : Nat := 118140960795 + 3493795 * 2 ^ 59
def prefixEnd_3493795 : Nat := 4983230072969 + 3 ^ 40 * 3493795 * 2
def baseEnd_3493795 : Nat := 1793996143275263244694835

theorem tailTrace_3493795 : CollatzResearch.WordTrace tailWord_3493795 prefixEnd_3493795 1793996143275263244694835 := by
  unfold tailWord_3493795
  simp only [CollatzResearch.WordTrace]
  refine ⟨127429172377584882525978839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84952781585056588350652559 127429172377584882525978839)
  ·
    refine ⟨191143758566377323788968259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127429172377584882525978839 191143758566377323788968259)
    ·
      refine ⟨286715637849565985683452389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191143758566377323788968259 286715637849565985683452389)
      ·
        refine ⟨53759182096793622315647323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286715637849565985683452389 53759182096793622315647323)
        ·
          refine ⟨80638773145190433473470985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53759182096793622315647323 80638773145190433473470985)
          ·
            refine ⟨60479079858892825105103239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80638773145190433473470985 60479079858892825105103239)
            ·
              refine ⟨90718619788339237657654859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60479079858892825105103239 90718619788339237657654859)
              ·
                refine ⟨136077929682508856486482289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90718619788339237657654859 136077929682508856486482289)
                ·
                  refine ⟨102058447261881642364861717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136077929682508856486482289 102058447261881642364861717)
                  ·
                    refine ⟨4783989715400701985852893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102058447261881642364861717 4783989715400701985852893)
                    ·
                      refine ⟨1793996143275263244694835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4783989715400701985852893 1793996143275263244694835)
                      ·
                        rfl

theorem cell23_3493795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_3493795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493795 prefixEnd_3493795 := by exact prefixLift 3493795
  have htrace : WordTrace (prefixWord ++ tailWord_3493795) baseStart_3493795 baseEnd_3493795 := by
    simpa [prefixWord, tailWord_3493795, baseEnd_3493795] using wordTrace_append hprefix tailTrace_3493795
  have hstable : (prefixWord ++ tailWord_3493795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493795).length < 2 ^ (prefixWord ++ tailWord_3493795).sum := by decide
  have hdescent : baseEnd_3493795 < baseStart_3493795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493809 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3493809 : Nat := 118140960795 + 3493809 * 2 ^ 59
def prefixEnd_3493809 : Nat := 4983230072969 + 3 ^ 40 * 3493809 * 2
def baseEnd_3493809 : Nat := 1794003332004426189919771

theorem tailTrace_3493809 : CollatzResearch.WordTrace tailWord_3493809 prefixEnd_3493809 1794003332004426189919771 := by
  unfold tailWord_3493809
  simp only [CollatzResearch.WordTrace]
  refine ⟨127429682999534162916988481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84953121999689441944658987 127429682999534162916988481)
  ·
    refine ⟨95572262249650622187741361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127429682999534162916988481 95572262249650622187741361)
    ·
      refine ⟨71679196687237966640806021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95572262249650622187741361 71679196687237966640806021)
      ·
        refine ⟨13439849378857118745151129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71679196687237966640806021 13439849378857118745151129)
        ·
          refine ⟨10079887034142839058863347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13439849378857118745151129 10079887034142839058863347)
          ·
            refine ⟨15119830551214258588295021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10079887034142839058863347 15119830551214258588295021)
            ·
              refine ⟨5669936456705346970610633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15119830551214258588295021 5669936456705346970610633)
              ·
                refine ⟨4252452342529010227957975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5669936456705346970610633 4252452342529010227957975)
                ·
                  refine ⟨6378678513793515341936963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252452342529010227957975 6378678513793515341936963)
                  ·
                    refine ⟨9568017770690273012905445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6378678513793515341936963 9568017770690273012905445)
                    ·
                      refine ⟨1794003332004426189919771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9568017770690273012905445 1794003332004426189919771)
                      ·
                        rfl

theorem cell23_3493809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3493809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493809 prefixEnd_3493809 := by exact prefixLift 3493809
  have htrace : WordTrace (prefixWord ++ tailWord_3493809) baseStart_3493809 baseEnd_3493809 := by
    simpa [prefixWord, tailWord_3493809, baseEnd_3493809] using wordTrace_append hprefix tailTrace_3493809
  have hstable : (prefixWord ++ tailWord_3493809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493809).length < 2 ^ (prefixWord ++ tailWord_3493809).sum := by decide
  have hdescent : baseEnd_3493809 < baseStart_3493809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493822 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3493822 : Nat := 118140960795 + 3493822 * 2 ^ 59
def prefixEnd_3493822 : Nat := 4983230072969 + 3 ^ 40 * 3493822 * 2
def baseEnd_3493822 : Nat := 1794010007252934639057211

theorem tailTrace_3493822 : CollatzResearch.WordTrace tailWord_3493822 prefixEnd_3493822 1794010007252934639057211 := by
  unfold tailWord_3493822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928769643560883267151465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84953438098991377424807813 15928769643560883267151465)
  ·
    refine ⟨11946577232670662450363599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15928769643560883267151465 11946577232670662450363599)
    ·
      refine ⟨17919865849005993675545399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11946577232670662450363599 17919865849005993675545399)
      ·
        refine ⟨26879798773508990513318099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17919865849005993675545399 26879798773508990513318099)
        ·
          refine ⟨40319698160263485769977149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26879798773508990513318099 40319698160263485769977149)
          ·
            refine ⟨15119886810098807163741431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40319698160263485769977149 15119886810098807163741431)
            ·
              refine ⟨22679830215148210745612147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15119886810098807163741431 22679830215148210745612147)
              ·
                refine ⟨34019745322722316118418221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22679830215148210745612147 34019745322722316118418221)
                ·
                  refine ⟨12757404496020868544406833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34019745322722316118418221 12757404496020868544406833)
                  ·
                    refine ⟨9568053372015651408305125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12757404496020868544406833 9568053372015651408305125)
                    ·
                      refine ⟨1794010007252934639057211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9568053372015651408305125 1794010007252934639057211)
                      ·
                        rfl

theorem cell23_3493822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3493822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493822 prefixEnd_3493822 := by exact prefixLift 3493822
  have htrace : WordTrace (prefixWord ++ tailWord_3493822) baseStart_3493822 baseEnd_3493822 := by
    simpa [prefixWord, tailWord_3493822, baseEnd_3493822] using wordTrace_append hprefix tailTrace_3493822
  have hstable : (prefixWord ++ tailWord_3493822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493822).length < 2 ^ (prefixWord ++ tailWord_3493822).sum := by decide
  have hdescent : baseEnd_3493822 < baseStart_3493822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493849 : List Nat := [1, 2, 1, 2, 7, 1, 1, 8]
def baseStart_3493849 : Nat := 118140960795 + 3493849 * 2 ^ 59
def prefixEnd_3493849 : Nat := 4983230072969 + 3 ^ 40 * 3493849 * 2
def baseEnd_3493849 : Nat := 66445328564096519756281

theorem tailTrace_3493849 : CollatzResearch.WordTrace tailWord_3493849 prefixEnd_3493849 66445328564096519756281 := by
  unfold tailWord_3493849
  simp only [CollatzResearch.WordTrace]
  refine ⟨127431141919389249748444601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84954094612926166498963067 127431141919389249748444601)
  ·
    refine ⟨95573356439541937311333451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127431141919389249748444601 95573356439541937311333451)
    ·
      refine ⟨143360034659312905967000177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95573356439541937311333451 143360034659312905967000177)
      ·
        refine ⟨107520025994484679475250133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143360034659312905967000177 107520025994484679475250133)
        ·
          refine ⟨2520000609245734675201175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107520025994484679475250133 2520000609245734675201175)
          ·
            refine ⟨3780000913868602012801763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520000609245734675201175 3780000913868602012801763)
            ·
              refine ⟨5670001370802903019202645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780000913868602012801763 5670001370802903019202645)
              ·
                refine ⟨66445328564096519756281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5670001370802903019202645 66445328564096519756281)
                ·
                  rfl

theorem cell23_3493849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 8].length) (baseStart_3493849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493849 prefixEnd_3493849 := by exact prefixLift 3493849
  have htrace : WordTrace (prefixWord ++ tailWord_3493849) baseStart_3493849 baseEnd_3493849 := by
    simpa [prefixWord, tailWord_3493849, baseEnd_3493849] using wordTrace_append hprefix tailTrace_3493849
  have hstable : (prefixWord ++ tailWord_3493849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493849).length < 2 ^ (prefixWord ++ tailWord_3493849).sum := by decide
  have hdescent : baseEnd_3493849 < baseStart_3493849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493859 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3493859 : Nat := 118140960795 + 3493859 * 2 ^ 59
def prefixEnd_3493859 : Nat := 4983230072969 + 3 ^ 40 * 3493859 * 2
def baseEnd_3493859 : Nat := 1794029006037150994294541

theorem tailTrace_3493859 : CollatzResearch.WordTrace tailWord_3493859 prefixEnd_3493859 1794029006037150994294541 := by
  unfold tailWord_3493859
  simp only [CollatzResearch.WordTrace]
  refine ⟨127431506649353021456308631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84954337766235347637539087 127431506649353021456308631)
  ·
    refine ⟨191147259974029532184462947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127431506649353021456308631 191147259974029532184462947)
    ·
      refine ⟨286720889961044298276694421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191147259974029532184462947 286720889961044298276694421)
      ·
        refine ⟨13440041716923951481720051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286720889961044298276694421 13440041716923951481720051)
        ·
          refine ⟨20160062575385927222580077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13440041716923951481720051 20160062575385927222580077)
          ·
            refine ⟨7560023465769722708467529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20160062575385927222580077 7560023465769722708467529)
            ·
              refine ⟨5670017599327292031350647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7560023465769722708467529 5670017599327292031350647)
              ·
                refine ⟨8505026398990938047025971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670017599327292031350647 8505026398990938047025971)
                ·
                  refine ⟨12757539598486407070538957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505026398990938047025971 12757539598486407070538957)
                  ·
                    refine ⟨4784077349432402651452109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12757539598486407070538957 4784077349432402651452109)
                    ·
                      refine ⟨1794029006037150994294541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4784077349432402651452109 1794029006037150994294541)
                      ·
                        rfl

theorem cell23_3493859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3493859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493859 prefixEnd_3493859 := by exact prefixLift 3493859
  have htrace : WordTrace (prefixWord ++ tailWord_3493859) baseStart_3493859 baseEnd_3493859 := by
    simpa [prefixWord, tailWord_3493859, baseEnd_3493859] using wordTrace_append hprefix tailTrace_3493859
  have hstable : (prefixWord ++ tailWord_3493859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493859).length < 2 ^ (prefixWord ++ tailWord_3493859).sum := by decide
  have hdescent : baseEnd_3493859 < baseStart_3493859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493894 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3493894 : Nat := 118140960795 + 3493894 * 2 ^ 59
def prefixEnd_3493894 : Nat := 4983230072969 + 3 ^ 40 * 3493894 * 2
def baseEnd_3493894 : Nat := 1794046977860058357356881

theorem tailTrace_3493894 : CollatzResearch.WordTrace tailWord_3493894 prefixEnd_3493894 1794046977860058357356881 := by
  unfold tailWord_3493894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982274475132069451057273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84955188802817481622555157 3982274475132069451057273)
  ·
    refine ⟨2986705856349052088292955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3982274475132069451057273 2986705856349052088292955)
    ·
      refine ⟨4480058784523578132439433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986705856349052088292955 4480058784523578132439433)
      ·
        refine ⟨3360044088392683599329575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480058784523578132439433 3360044088392683599329575)
        ·
          refine ⟨5040066132589025398994363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360044088392683599329575 5040066132589025398994363)
          ·
            refine ⟨7560099198883538098491545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040066132589025398994363 7560099198883538098491545)
            ·
              refine ⟨5670074399162653573868659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7560099198883538098491545 5670074399162653573868659)
              ·
                refine ⟨8505111598743980360802989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670074399162653573868659 8505111598743980360802989)
                ·
                  refine ⟨3189416849528992635301121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8505111598743980360802989 3189416849528992635301121)
                  ·
                    refine ⟨2392062637146744476475841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189416849528992635301121 2392062637146744476475841)
                    ·
                      refine ⟨1794046977860058357356881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392062637146744476475841 1794046977860058357356881)
                      ·
                        rfl

theorem cell23_3493894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3493894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493894 prefixEnd_3493894 := by exact prefixLift 3493894
  have htrace : WordTrace (prefixWord ++ tailWord_3493894) baseStart_3493894 baseEnd_3493894 := by
    simpa [prefixWord, tailWord_3493894, baseEnd_3493894] using wordTrace_append hprefix tailTrace_3493894
  have hstable : (prefixWord ++ tailWord_3493894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493894).length < 2 ^ (prefixWord ++ tailWord_3493894).sum := by decide
  have hdescent : baseEnd_3493894 < baseStart_3493894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493912 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3493912 : Nat := 118140960795 + 3493912 * 2 ^ 59
def prefixEnd_3493912 : Nat := 4983230072969 + 3 ^ 40 * 3493912 * 2
def baseEnd_3493912 : Nat := 1794056220511839286931797

theorem tailTrace_3493912 : CollatzResearch.WordTrace tailWord_3493912 prefixEnd_3493912 1794056220511839286931797 := by
  unfold tailWord_3493912
  simp only [CollatzResearch.WordTrace]
  refine ⟨63716719859080505753993995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84955626478774007671991993 63716719859080505753993995)
  ·
    refine ⟨95575079788620758630990993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63716719859080505753993995 95575079788620758630990993)
    ·
      refine ⟨71681309841465568973243245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95575079788620758630990993 71681309841465568973243245)
      ·
        refine ⟨26880491190549588364966217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71681309841465568973243245 26880491190549588364966217)
        ·
          refine ⟨20160368392912191273724663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26880491190549588364966217 20160368392912191273724663)
          ·
            refine ⟨30240552589368286910586995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20160368392912191273724663 30240552589368286910586995)
            ·
              refine ⟨45360828884052430365880493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30240552589368286910586995 45360828884052430365880493)
              ·
                refine ⟨17010310831519661387205185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45360828884052430365880493 17010310831519661387205185)
                ·
                  refine ⟨12757733123639746040403889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17010310831519661387205185 12757733123639746040403889)
                  ·
                    refine ⟨9568299842729809530302917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12757733123639746040403889 9568299842729809530302917)
                    ·
                      refine ⟨1794056220511839286931797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9568299842729809530302917 1794056220511839286931797)
                      ·
                        rfl

theorem cell23_3493912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3493912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493912 prefixEnd_3493912 := by exact prefixLift 3493912
  have htrace : WordTrace (prefixWord ++ tailWord_3493912) baseStart_3493912 baseEnd_3493912 := by
    simpa [prefixWord, tailWord_3493912, baseEnd_3493912] using wordTrace_append hprefix tailTrace_3493912
  have hstable : (prefixWord ++ tailWord_3493912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493912).length < 2 ^ (prefixWord ++ tailWord_3493912).sum := by decide
  have hdescent : baseEnd_3493912 < baseStart_3493912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493916 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_3493916 : Nat := 118140960795 + 3493916 * 2 ^ 59
def prefixEnd_3493916 : Nat := 4983230072969 + 3 ^ 40 * 3493916 * 2
def baseEnd_3493916 : Nat := 1794058274434457271281779

theorem tailTrace_3493916 : CollatzResearch.WordTrace tailWord_3493916 prefixEnd_3493916 1794058274434457271281779 := by
  unfold tailWord_3493916
  simp only [CollatzResearch.WordTrace]
  refine ⟨63716792805073260095566801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84955723740097680127422401 63716792805073260095566801)
  ·
    refine ⟨47787594603804945071675101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63716792805073260095566801 47787594603804945071675101)
    ·
      refine ⟨17920347976426854401878163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47787594603804945071675101 17920347976426854401878163)
      ·
        refine ⟨26880521964640281602817245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17920347976426854401878163 26880521964640281602817245)
        ·
          refine ⟨10080195736740105601056467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26880521964640281602817245 10080195736740105601056467)
          ·
            refine ⟨15120293605110158401584701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10080195736740105601056467 15120293605110158401584701)
            ·
              refine ⟨5670110101916309400594263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15120293605110158401584701 5670110101916309400594263)
              ·
                refine ⟨8505165152874464100891395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670110101916309400594263 8505165152874464100891395)
                ·
                  refine ⟨12757747729311696151337093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505165152874464100891395 12757747729311696151337093)
                  ·
                    refine ⟨2392077699245943028375705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12757747729311696151337093 2392077699245943028375705)
                    ·
                      refine ⟨1794058274434457271281779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392077699245943028375705 1794058274434457271281779)
                      ·
                        rfl

theorem cell23_3493916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_3493916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493916 prefixEnd_3493916 := by exact prefixLift 3493916
  have htrace : WordTrace (prefixWord ++ tailWord_3493916) baseStart_3493916 baseEnd_3493916 := by
    simpa [prefixWord, tailWord_3493916, baseEnd_3493916] using wordTrace_append hprefix tailTrace_3493916
  have hstable : (prefixWord ++ tailWord_3493916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493916).length < 2 ^ (prefixWord ++ tailWord_3493916).sum := by decide
  have hdescent : baseEnd_3493916 < baseStart_3493916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493922 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_3493922 : Nat := 118140960795 + 3493922 * 2 ^ 59
def prefixEnd_3493922 : Nat := 4983230072969 + 3 ^ 40 * 3493922 * 2
def baseEnd_3493922 : Nat := 199340150590931583089639

theorem tailTrace_3493922 : CollatzResearch.WordTrace tailWord_3493922 prefixEnd_3493922 199340150590931583089639 := by
  unfold tailWord_3493922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31858451112031195803963005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84955869632083188810568013 31858451112031195803963005)
  ·
    refine ⟨11946919167011698426486127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31858451112031195803963005 11946919167011698426486127)
    ·
      refine ⟨17920378750517547639729191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11946919167011698426486127 17920378750517547639729191)
      ·
        refine ⟨26880568125776321459593787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17920378750517547639729191 26880568125776321459593787)
        ·
          refine ⟨40320852188664482189390681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26880568125776321459593787 40320852188664482189390681)
          ·
            refine ⟨30240639141498361642043011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40320852188664482189390681 30240639141498361642043011)
            ·
              refine ⟨45360958712247542463064517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30240639141498361642043011 45360958712247542463064517)
              ·
                refine ⟨8505179758546414211824597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45360958712247542463064517 8505179758546414211824597)
                ·
                  refine ⟨199340150590931583089639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8505179758546414211824597 199340150590931583089639)
                  ·
                    rfl

theorem cell23_3493922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_3493922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493922 prefixEnd_3493922 := by exact prefixLift 3493922
  have htrace : WordTrace (prefixWord ++ tailWord_3493922) baseStart_3493922 baseEnd_3493922 := by
    simpa [prefixWord, tailWord_3493922, baseEnd_3493922] using wordTrace_append hprefix tailTrace_3493922
  have hstable : (prefixWord ++ tailWord_3493922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493922).length < 2 ^ (prefixWord ++ tailWord_3493922).sum := by decide
  have hdescent : baseEnd_3493922 < baseStart_3493922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493932 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_3493932 : Nat := 118140960795 + 3493932 * 2 ^ 59
def prefixEnd_3493932 : Nat := 4983230072969 + 3 ^ 40 * 3493932 * 2
def baseEnd_3493932 : Nat := 1794066490124929208681705

theorem tailTrace_3493932 : CollatzResearch.WordTrace tailWord_3493932 prefixEnd_3493932 1794066490124929208681705 := by
  unfold tailWord_3493932
  simp only [CollatzResearch.WordTrace]
  refine ⟨63717084589044277461858025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84956112785392369949144033 63717084589044277461858025)
  ·
    refine ⟨47787813441783208096393519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63717084589044277461858025 47787813441783208096393519)
    ·
      refine ⟨71681720162674812144590279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47787813441783208096393519 71681720162674812144590279)
      ·
        refine ⟨107522580244012218216885419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71681720162674812144590279 107522580244012218216885419)
        ·
          refine ⟨161283870366018327325328129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107522580244012218216885419 161283870366018327325328129)
          ·
            refine ⟨120962902774513745493996097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161283870366018327325328129 120962902774513745493996097)
            ·
              refine ⟨90722177080885309120497073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120962902774513745493996097 90722177080885309120497073)
              ·
                refine ⟨68041632810663981840372805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90722177080885309120497073 68041632810663981840372805)
                ·
                  refine ⟨12757806151999496595069901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68041632810663981840372805 12757806151999496595069901)
                  ·
                    refine ⟨4784177306999811223151213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12757806151999496595069901 4784177306999811223151213)
                    ·
                      refine ⟨1794066490124929208681705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4784177306999811223151213 1794066490124929208681705)
                      ·
                        rfl

theorem cell23_3493932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_3493932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493932 prefixEnd_3493932 := by exact prefixLift 3493932
  have htrace : WordTrace (prefixWord ++ tailWord_3493932) baseStart_3493932 baseEnd_3493932 := by
    simpa [prefixWord, tailWord_3493932, baseEnd_3493932] using wordTrace_append hprefix tailTrace_3493932
  have hstable : (prefixWord ++ tailWord_3493932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493932).length < 2 ^ (prefixWord ++ tailWord_3493932).sum := by decide
  have hdescent : baseEnd_3493932 < baseStart_3493932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493939 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 5]
def baseStart_3493939 : Nat := 118140960795 + 3493939 * 2 ^ 59
def prefixEnd_3493939 : Nat := 4983230072969 + 3 ^ 40 * 3493939 * 2
def baseEnd_3493939 : Nat := 199341120498834520143797

theorem tailTrace_3493939 : CollatzResearch.WordTrace tailWord_3493939 prefixEnd_3493939 199341120498834520143797 := by
  unfold tailWord_3493939
  simp only [CollatzResearch.WordTrace]
  refine ⟨127434424489063195119220871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84956282992708796746147247 127434424489063195119220871)
  ·
    refine ⟨191151636733594792678831307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127434424489063195119220871 191151636733594792678831307)
    ·
      refine ⟨286727455100392189018246961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191151636733594792678831307 286727455100392189018246961)
      ·
        refine ⟨215045591325294141763685221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286727455100392189018246961 215045591325294141763685221)
        ·
          refine ⟨40321048373492651580690979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215045591325294141763685221 40321048373492651580690979)
          ·
            refine ⟨60481572560238977371036469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40321048373492651580690979 60481572560238977371036469)
            ·
              refine ⟨5670147427522404128534669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60481572560238977371036469 5670147427522404128534669)
              ·
                refine ⟨2126305285320901548200501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5670147427522404128534669 2126305285320901548200501)
                ·
                  refine ⟨199341120498834520143797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2126305285320901548200501 199341120498834520143797)
                  ·
                    rfl

theorem cell23_3493939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 5].length) (baseStart_3493939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493939 prefixEnd_3493939 := by exact prefixLift 3493939
  have htrace : WordTrace (prefixWord ++ tailWord_3493939) baseStart_3493939 baseEnd_3493939 := by
    simpa [prefixWord, tailWord_3493939, baseEnd_3493939] using wordTrace_append hprefix tailTrace_3493939
  have hstable : (prefixWord ++ tailWord_3493939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493939).length < 2 ^ (prefixWord ++ tailWord_3493939).sum := by decide
  have hdescent : baseEnd_3493939 < baseStart_3493939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493952 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_3493952 : Nat := 118140960795 + 3493952 * 2 ^ 59
def prefixEnd_3493952 : Nat := 4983230072969 + 3 ^ 40 * 3493952 * 2
def baseEnd_3493952 : Nat := 598025586579339710143871

theorem tailTrace_3493952 : CollatzResearch.WordTrace tailWord_3493952 prefixEnd_3493952 598025586579339710143871 := by
  unfold tailWord_3493952
  simp only [CollatzResearch.WordTrace]
  refine ⟨63717449319008049169722055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84956599092010732226296073 63717449319008049169722055)
  ·
    refine ⟨95576173978512073754583083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63717449319008049169722055 95576173978512073754583083)
    ·
      refine ⟨143364260967768110631874625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95576173978512073754583083 143364260967768110631874625)
      ·
        refine ⟨107523195725826082973905969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143364260967768110631874625 107523195725826082973905969)
        ·
          refine ⟨80642396794369562230429477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107523195725826082973905969 80642396794369562230429477)
          ·
            refine ⟨15120449398944292918205527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80642396794369562230429477 15120449398944292918205527)
            ·
              refine ⟨22680674098416439377308291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15120449398944292918205527 22680674098416439377308291)
              ·
                refine ⟨34021011147624659065962437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22680674098416439377308291 34021011147624659065962437)
                ·
                  refine ⟨6378939590179623574867957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34021011147624659065962437 6378939590179623574867957)
                  ·
                    refine ⟨598025586579339710143871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6378939590179623574867957 598025586579339710143871)
                    ·
                      rfl

theorem cell23_3493952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_3493952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493952 prefixEnd_3493952 := by exact prefixLift 3493952
  have htrace : WordTrace (prefixWord ++ tailWord_3493952) baseStart_3493952 baseEnd_3493952 := by
    simpa [prefixWord, tailWord_3493952, baseEnd_3493952] using wordTrace_append hprefix tailTrace_3493952
  have hstable : (prefixWord ++ tailWord_3493952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493952).length < 2 ^ (prefixWord ++ tailWord_3493952).sum := by decide
  have hdescent : baseEnd_3493952 < baseStart_3493952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493959 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_3493959 : Nat := 118140960795 + 3493959 * 2 ^ 59
def prefixEnd_3493959 : Nat := 4983230072969 + 3 ^ 40 * 3493959 * 2
def baseEnd_3493959 : Nat := 1794080354102600603044081

theorem tailTrace_3493959 : CollatzResearch.WordTrace tailWord_3493959 prefixEnd_3493959 1794080354102600603044081 := by
  unfold tailWord_3493959
  simp only [CollatzResearch.WordTrace]
  refine ⟨127435153948990738534948931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84956769299327159023299287 127435153948990738534948931)
  ·
    refine ⟨191152730923486107802423397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127435153948990738534948931 191152730923486107802423397)
    ·
      refine ⟨35841137048153645212954387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191152730923486107802423397 35841137048153645212954387)
      ·
        refine ⟨53761705572230467819431581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35841137048153645212954387 53761705572230467819431581)
        ·
          refine ⟨20160639589586425432286843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53761705572230467819431581 20160639589586425432286843)
          ·
            refine ⟨30240959384379638148430265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20160639589586425432286843 30240959384379638148430265)
            ·
              refine ⟨22680719538284728611322699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30240959384379638148430265 22680719538284728611322699)
              ·
                refine ⟨34021079307427092916984049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22680719538284728611322699 34021079307427092916984049)
                ·
                  refine ⟨25515809480570319687738037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34021079307427092916984049 25515809480570319687738037)
                  ·
                    refine ⟨2392107138803467470725441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25515809480570319687738037 2392107138803467470725441)
                    ·
                      refine ⟨1794080354102600603044081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392107138803467470725441 1794080354102600603044081)
                      ·
                        rfl

theorem cell23_3493959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_3493959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493959 prefixEnd_3493959 := by exact prefixLift 3493959
  have htrace : WordTrace (prefixWord ++ tailWord_3493959) baseStart_3493959 baseEnd_3493959 := by
    simpa [prefixWord, tailWord_3493959, baseEnd_3493959] using wordTrace_append hprefix tailTrace_3493959
  have hstable : (prefixWord ++ tailWord_3493959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493959).length < 2 ^ (prefixWord ++ tailWord_3493959).sum := by decide
  have hdescent : baseEnd_3493959 < baseStart_3493959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3493989 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3493989 : Nat := 118140960795 + 3493989 * 2 ^ 59
def prefixEnd_3493989 : Nat := 4983230072969 + 3 ^ 40 * 3493989 * 2
def baseEnd_3493989 : Nat := 1794095758522235485668943

theorem tailTrace_3493989 : CollatzResearch.WordTrace tailWord_3493989 prefixEnd_3493989 1794095758522235485668943 := by
  unfold tailWord_3493989
  simp only [CollatzResearch.WordTrace]
  refine ⟨127436248138882053658541021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84957498759254702439027347 127436248138882053658541021)
  ·
    refine ⟨47788593052080770121952883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127436248138882053658541021 47788593052080770121952883)
    ·
      refine ⟨71682889578121155182929325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47788593052080770121952883 71682889578121155182929325)
      ·
        refine ⟨26881083591795433193598497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71682889578121155182929325 26881083591795433193598497)
        ·
          refine ⟨20160812693846574895198873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26881083591795433193598497 20160812693846574895198873)
          ·
            refine ⟨15120609520384931171399155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20160812693846574895198873 15120609520384931171399155)
            ·
              refine ⟨22680914280577396757098733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15120609520384931171399155 22680914280577396757098733)
              ·
                refine ⟨8505342855216523783912025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22680914280577396757098733 8505342855216523783912025)
                ·
                  refine ⟨6379007141412392837934019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8505342855216523783912025 6379007141412392837934019)
                  ·
                    refine ⟨9568510712118589256901029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6379007141412392837934019 9568510712118589256901029)
                    ·
                      refine ⟨1794095758522235485668943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9568510712118589256901029 1794095758522235485668943)
                      ·
                        rfl

theorem cell23_3493989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3493989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3493989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3493989 prefixEnd_3493989 := by exact prefixLift 3493989
  have htrace : WordTrace (prefixWord ++ tailWord_3493989) baseStart_3493989 baseEnd_3493989 := by
    simpa [prefixWord, tailWord_3493989, baseEnd_3493989] using wordTrace_append hprefix tailTrace_3493989
  have hstable : (prefixWord ++ tailWord_3493989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3493989).length < 2 ^ (prefixWord ++ tailWord_3493989).sum := by decide
  have hdescent : baseEnd_3493989 < baseStart_3493989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3493989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494006 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3494006 : Nat := 118140960795 + 3494006 * 2 ^ 59
def prefixEnd_3494006 : Nat := 4983230072969 + 3 ^ 40 * 3494006 * 2
def baseEnd_3494006 : Nat := 1794104487693361919156365

theorem tailTrace_3494006 : CollatzResearch.WordTrace tailWord_3494006 prefixEnd_3494006 1794104487693361919156365 := by
  unfold tailWord_3494006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964804261238779097619367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84957912119880310374606581 7964804261238779097619367)
  ·
    refine ⟨11947206391858168646429051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7964804261238779097619367 11947206391858168646429051)
    ·
      refine ⟨17920809587787252969643577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11947206391858168646429051 17920809587787252969643577)
      ·
        refine ⟨13440607190840439727232683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17920809587787252969643577 13440607190840439727232683)
        ·
          refine ⟨20160910786260659590849025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13440607190840439727232683 20160910786260659590849025)
          ·
            refine ⟨15120683089695494693136769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20160910786260659590849025 15120683089695494693136769)
            ·
              refine ⟨11340512317271621019852577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15120683089695494693136769 11340512317271621019852577)
              ·
                refine ⟨8505384237953715764889433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11340512317271621019852577 8505384237953715764889433)
                ·
                  refine ⟨6379038178465286823667075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8505384237953715764889433 6379038178465286823667075)
                  ·
                    refine ⟨9568557267697930235500613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6379038178465286823667075 9568557267697930235500613)
                    ·
                      refine ⟨1794104487693361919156365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9568557267697930235500613 1794104487693361919156365)
                      ·
                        rfl

theorem cell23_3494006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3494006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494006 prefixEnd_3494006 := by exact prefixLift 3494006
  have htrace : WordTrace (prefixWord ++ tailWord_3494006) baseStart_3494006 baseEnd_3494006 := by
    simpa [prefixWord, tailWord_3494006, baseEnd_3494006] using wordTrace_append hprefix tailTrace_3494006
  have hstable : (prefixWord ++ tailWord_3494006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494006).length < 2 ^ (prefixWord ++ tailWord_3494006).sum := by decide
  have hdescent : baseEnd_3494006 < baseStart_3494006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494050 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3494050 : Nat := 118140960795 + 3494050 * 2 ^ 59
def prefixEnd_3494050 : Nat := 4983230072969 + 3 ^ 40 * 3494050 * 2
def baseEnd_3494050 : Nat := 598042360280719915668721

theorem tailTrace_3494050 : CollatzResearch.WordTrace tailWord_3494050 prefixEnd_3494050 598042360280719915668721 := by
  unfold tailWord_3494050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31859618247915265269127901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84958981994440707384341069 31859618247915265269127901)
  ·
    refine ⟨11947356842968224475922963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31859618247915265269127901 11947356842968224475922963)
    ·
      refine ⟨17921035264452336713884445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11947356842968224475922963 17921035264452336713884445)
      ·
        refine ⟨6720388224169626267706667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17921035264452336713884445 6720388224169626267706667)
        ·
          refine ⟨10080582336254439401560001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6720388224169626267706667 10080582336254439401560001)
          ·
            refine ⟨7560436752190829551170001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10080582336254439401560001 7560436752190829551170001)
            ·
              refine ⟨5670327564143122163377501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7560436752190829551170001 5670327564143122163377501)
              ·
                refine ⟨2126372836553670811266563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5670327564143122163377501 2126372836553670811266563)
                ·
                  refine ⟨3189559254830506216899845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126372836553670811266563 3189559254830506216899845)
                  ·
                    refine ⟨598042360280719915668721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3189559254830506216899845 598042360280719915668721)
                    ·
                      rfl

theorem cell23_3494050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3494050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494050 prefixEnd_3494050 := by exact prefixLift 3494050
  have htrace : WordTrace (prefixWord ++ tailWord_3494050) baseStart_3494050 baseEnd_3494050 := by
    simpa [prefixWord, tailWord_3494050, baseEnd_3494050] using wordTrace_append hprefix tailTrace_3494050
  have hstable : (prefixWord ++ tailWord_3494050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494050).length < 2 ^ (prefixWord ++ tailWord_3494050).sum := by decide
  have hdescent : baseEnd_3494050 < baseStart_3494050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494066 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_3494066 : Nat := 118140960795 + 3494066 * 2 ^ 59
def prefixEnd_3494066 : Nat := 4983230072969 + 3 ^ 40 * 3494066 * 2
def baseEnd_3494066 : Nat := 1794135296532631684406089

theorem tailTrace_3494066 : CollatzResearch.WordTrace tailWord_3494066 prefixEnd_3494066 1794135296532631684406089 := by
  unfold tailWord_3494066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31859764139900773952273513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84959371039735397206062701 31859764139900773952273513)
  ·
    refine ⟨23894823104925580464205135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31859764139900773952273513 23894823104925580464205135)
    ·
      refine ⟨35842234657388370696307703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23894823104925580464205135 35842234657388370696307703)
      ·
        refine ⟨53763351986082556044461555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35842234657388370696307703 53763351986082556044461555)
        ·
          refine ⟨80645027979123834066692333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53763351986082556044461555 80645027979123834066692333)
          ·
            refine ⟨30241885492171437775009625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80645027979123834066692333 30241885492171437775009625)
            ·
              refine ⟨22681414119128578331257219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30241885492171437775009625 22681414119128578331257219)
              ·
                refine ⟨34022121178692867496885829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22681414119128578331257219 34022121178692867496885829)
                ·
                  refine ⟨6379147721004912655666093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34022121178692867496885829 6379147721004912655666093)
                  ·
                    refine ⟨2392180395376842245874785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6379147721004912655666093 2392180395376842245874785)
                    ·
                      refine ⟨1794135296532631684406089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392180395376842245874785 1794135296532631684406089)
                      ·
                        rfl

theorem cell23_3494066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_3494066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494066 prefixEnd_3494066 := by exact prefixLift 3494066
  have htrace : WordTrace (prefixWord ++ tailWord_3494066) baseStart_3494066 baseEnd_3494066 := by
    simpa [prefixWord, tailWord_3494066, baseEnd_3494066] using wordTrace_append hprefix tailTrace_3494066
  have hstable : (prefixWord ++ tailWord_3494066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494066).length < 2 ^ (prefixWord ++ tailWord_3494066).sum := by decide
  have hdescent : baseEnd_3494066 < baseStart_3494066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494073 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3494073 : Nat := 118140960795 + 3494073 * 2 ^ 59
def prefixEnd_3494073 : Nat := 4983230072969 + 3 ^ 40 * 3494073 * 2
def baseEnd_3494073 : Nat := 1794138890897213157018557

theorem tailTrace_3494073 : CollatzResearch.WordTrace tailWord_3494073 prefixEnd_3494073 1794138890897213157018557 := by
  unfold tailWord_3494073
  simp only [CollatzResearch.WordTrace]
  refine ⟨127439311870577736004598873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84959541247051824003065915 127439311870577736004598873)
  ·
    refine ⟨95579483902933302003449155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127439311870577736004598873 95579483902933302003449155)
    ·
      refine ⟨143369225854399953005173733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95579483902933302003449155 143369225854399953005173733)
      ·
        refine ⟨26881729847699991188470075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143369225854399953005173733 26881729847699991188470075)
        ·
          refine ⟨40322594771549986782705113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26881729847699991188470075 40322594771549986782705113)
          ·
            refine ⟨30241946078662490087028835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40322594771549986782705113 30241946078662490087028835)
            ·
              refine ⟨45362919117993735130543253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30241946078662490087028835 45362919117993735130543253)
              ·
                refine ⟨2126386833655956334244215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45362919117993735130543253 2126386833655956334244215)
                ·
                  refine ⟨3189580250483934501366323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126386833655956334244215 3189580250483934501366323)
                  ·
                    refine ⟨4784370375725901752049485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189580250483934501366323 4784370375725901752049485)
                    ·
                      refine ⟨1794138890897213157018557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4784370375725901752049485 1794138890897213157018557)
                      ·
                        rfl

theorem cell23_3494073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3494073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494073 prefixEnd_3494073 := by exact prefixLift 3494073
  have htrace : WordTrace (prefixWord ++ tailWord_3494073) baseStart_3494073 baseEnd_3494073 := by
    simpa [prefixWord, tailWord_3494073, baseEnd_3494073] using wordTrace_append hprefix tailTrace_3494073
  have hstable : (prefixWord ++ tailWord_3494073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494073).length < 2 ^ (prefixWord ++ tailWord_3494073).sum := by decide
  have hdescent : baseEnd_3494073 < baseStart_3494073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494119 : List Nat := [1, 1, 5, 3, 1, 1, 11]
def baseStart_3494119 : Nat := 118140960795 + 3494119 * 2 ^ 59
def prefixEnd_3494119 : Nat := 4983230072969 + 3 ^ 40 * 3494119 * 2
def baseEnd_3494119 : Nat := 22150154456880493543745

theorem tailTrace_3494119 : CollatzResearch.WordTrace tailWord_3494119 prefixEnd_3494119 22150154456880493543745 := by
  unfold tailWord_3494119
  simp only [CollatzResearch.WordTrace]
  refine ⟨127440989628411085860773411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84960659752274057240515607 127440989628411085860773411)
  ·
    refine ⟨191161484442616628791160117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127440989628411085860773411 191161484442616628791160117)
    ·
      refine ⟨17921389166495308949171261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191161484442616628791160117 17921389166495308949171261)
      ·
        refine ⟨6720520937435740855939223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17921389166495308949171261 6720520937435740855939223)
        ·
          refine ⟨10080781406153611283908835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6720520937435740855939223 10080781406153611283908835)
          ·
            refine ⟨15121172109230416925863253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10080781406153611283908835 15121172109230416925863253)
            ·
              refine ⟨22150154456880493543745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15121172109230416925863253 22150154456880493543745)
              ·
                rfl

theorem cell23_3494119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 11].length) (baseStart_3494119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494119 prefixEnd_3494119 := by exact prefixLift 3494119
  have htrace : WordTrace (prefixWord ++ tailWord_3494119) baseStart_3494119 baseEnd_3494119 := by
    simpa [prefixWord, tailWord_3494119, baseEnd_3494119] using wordTrace_append hprefix tailTrace_3494119
  have hstable : (prefixWord ++ tailWord_3494119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494119).length < 2 ^ (prefixWord ++ tailWord_3494119).sum := by decide
  have hdescent : baseEnd_3494119 < baseStart_3494119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494130 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_3494130 : Nat := 118140960795 + 3494130 * 2 ^ 59
def prefixEnd_3494130 : Nat := 4983230072969 + 3 ^ 40 * 3494130 * 2
def baseEnd_3494130 : Nat := 1794168159294519434005795

theorem tailTrace_3494130 : CollatzResearch.WordTrace tailWord_3494130 prefixEnd_3494130 1794168159294519434005795 := by
  unfold tailWord_3494130
  simp only [CollatzResearch.WordTrace]
  refine ⟨31860347707842808684855961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84960927220914156492949229 31860347707842808684855961)
  ·
    refine ⟨23895260780882106513641971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31860347707842808684855961 23895260780882106513641971)
    ·
      refine ⟨35842891171323159770462957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23895260780882106513641971 35842891171323159770462957)
      ·
        refine ⟨13441084189246184913923609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35842891171323159770462957 13441084189246184913923609)
        ·
          refine ⟨10080813141934638685442707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13441084189246184913923609 10080813141934638685442707)
          ·
            refine ⟨15121219712901958028164061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10080813141934638685442707 15121219712901958028164061)
            ·
              refine ⟨5670457392338234260561523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15121219712901958028164061 5670457392338234260561523)
              ·
                refine ⟨8505686088507351390842285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670457392338234260561523 8505686088507351390842285)
                ·
                  refine ⟨3189632283190256771565857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8505686088507351390842285 3189632283190256771565857)
                  ·
                    refine ⟨2392224212392692578674393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189632283190256771565857 2392224212392692578674393)
                    ·
                      refine ⟨1794168159294519434005795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392224212392692578674393 1794168159294519434005795)
                      ·
                        rfl

theorem cell23_3494130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_3494130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494130 prefixEnd_3494130 := by exact prefixLift 3494130
  have htrace : WordTrace (prefixWord ++ tailWord_3494130) baseStart_3494130 baseEnd_3494130 := by
    simpa [prefixWord, tailWord_3494130, baseEnd_3494130] using wordTrace_append hprefix tailTrace_3494130
  have hstable : (prefixWord ++ tailWord_3494130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494130).length < 2 ^ (prefixWord ++ tailWord_3494130).sum := by decide
  have hdescent : baseEnd_3494130 < baseStart_3494130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494140 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_3494140 : Nat := 118140960795 + 3494140 * 2 ^ 59
def prefixEnd_3494140 : Nat := 4983230072969 + 3 ^ 40 * 3494140 * 2
def baseEnd_3494140 : Nat := 598057764700354798293583

theorem tailTrace_3494140 : CollatzResearch.WordTrace tailWord_3494140 prefixEnd_3494140 598057764700354798293583 := by
  unfold tailWord_3494140
  simp only [CollatzResearch.WordTrace]
  refine ⟨63720877780667503223643937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84961170374223337631525249 63720877780667503223643937)
  ·
    refine ⟨47790658335500627417732953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63720877780667503223643937 47790658335500627417732953)
    ·
      refine ⟨35842993751625470563299715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47790658335500627417732953 35842993751625470563299715)
      ·
        refine ⟨53764490627438205844949573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35842993751625470563299715 53764490627438205844949573)
        ·
          refine ⟨10080841992644663595928045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53764490627438205844949573 10080841992644663595928045)
          ·
            refine ⟨3780315747241748848473017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10080841992644663595928045 3780315747241748848473017)
            ·
              refine ⟨2835236810431311636354763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780315747241748848473017 2835236810431311636354763)
              ·
                refine ⟨4252855215646967454532145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835236810431311636354763 4252855215646967454532145)
                ·
                  refine ⟨3189641411735225590899109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4252855215646967454532145 3189641411735225590899109)
                  ·
                    refine ⟨598057764700354798293583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3189641411735225590899109 598057764700354798293583)
                    ·
                      rfl

theorem cell23_3494140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_3494140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494140 prefixEnd_3494140 := by exact prefixLift 3494140
  have htrace : WordTrace (prefixWord ++ tailWord_3494140) baseStart_3494140 baseEnd_3494140 := by
    simpa [prefixWord, tailWord_3494140, baseEnd_3494140] using wordTrace_append hprefix tailTrace_3494140
  have hstable : (prefixWord ++ tailWord_3494140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494140).length < 2 ^ (prefixWord ++ tailWord_3494140).sum := by decide
  have hdescent : baseEnd_3494140 < baseStart_3494140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494179 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 2, 6]
def baseStart_3494179 : Nat := 118140960795 + 3494179 * 2 ^ 59
def prefixEnd_3494179 : Nat := 4983230072969 + 3 ^ 40 * 3494179 * 2
def baseEnd_3494179 : Nat := 598064439948863247431023

theorem tailTrace_3494179 : CollatzResearch.WordTrace tailWord_3494179 prefixEnd_3494179 598064439948863247431023 := by
  unfold tailWord_3494179
  simp only [CollatzResearch.WordTrace]
  refine ⟨127443178008193716107957591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84962118672129144071971727 127443178008193716107957591)
  ·
    refine ⟨191164767012290574161936387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127443178008193716107957591 191164767012290574161936387)
    ·
      refine ⟨286747150518435861242904581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191164767012290574161936387 286747150518435861242904581)
      ·
        refine ⟨53765090722206723983044609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286747150518435861242904581 53765090722206723983044609)
        ·
          refine ⟨40323818041655042987283457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53765090722206723983044609 40323818041655042987283457)
          ·
            refine ⟨30242863531241282240462593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40323818041655042987283457 30242863531241282240462593)
            ·
              refine ⟨22682147648430961680346945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30242863531241282240462593 22682147648430961680346945)
              ·
                refine ⟨17011610736323221260260209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22682147648430961680346945 17011610736323221260260209)
                ·
                  refine ⟨12758708052242415945195157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17011610736323221260260209 12758708052242415945195157)
                  ·
                    refine ⟨598064439948863247431023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12758708052242415945195157 598064439948863247431023)
                    ·
                      rfl

theorem cell23_3494179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 6].length) (baseStart_3494179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494179 prefixEnd_3494179 := by exact prefixLift 3494179
  have htrace : WordTrace (prefixWord ++ tailWord_3494179) baseStart_3494179 baseEnd_3494179 := by
    simpa [prefixWord, tailWord_3494179, baseEnd_3494179] using wordTrace_append hprefix tailTrace_3494179
  have hstable : (prefixWord ++ tailWord_3494179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494179).length < 2 ^ (prefixWord ++ tailWord_3494179).sum := by decide
  have hdescent : baseEnd_3494179 < baseStart_3494179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494180 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_3494180 : Nat := 118140960795 + 3494180 * 2 ^ 59
def prefixEnd_3494180 : Nat := 4983230072969 + 3 ^ 40 * 3494180 * 2
def baseEnd_3494180 : Nat := 1794193833327244238380565

theorem tailTrace_3494180 : CollatzResearch.WordTrace tailWord_3494180 prefixEnd_3494180 1794193833327244238380565 := by
  unfold tailWord_3494180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721607240595046639371997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84962142987460062185829329 63721607240595046639371997)
  ·
    refine ⟨23895602715223142489764499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63721607240595046639371997 23895602715223142489764499)
    ·
      refine ⟨35843404072834713734646749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23895602715223142489764499 35843404072834713734646749)
      ·
        refine ⟨13441276527313017650492531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35843404072834713734646749 13441276527313017650492531)
        ·
          refine ⟨20161914790969526475738797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13441276527313017650492531 20161914790969526475738797)
          ·
            refine ⟨7560718046613572428402049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20161914790969526475738797 7560718046613572428402049)
            ·
              refine ⟨5670538534960179321301537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7560718046613572428402049 5670538534960179321301537)
              ·
                refine ⟨4252903901220134490976153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5670538534960179321301537 4252903901220134490976153)
                ·
                  refine ⟨3189677925915100868232115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4252903901220134490976153 3189677925915100868232115)
                  ·
                    refine ⟨4784516888872651302348173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189677925915100868232115 4784516888872651302348173)
                    ·
                      refine ⟨1794193833327244238380565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4784516888872651302348173 1794193833327244238380565)
                      ·
                        rfl

theorem cell23_3494180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_3494180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494180 prefixEnd_3494180 := by exact prefixLift 3494180
  have htrace : WordTrace (prefixWord ++ tailWord_3494180) baseStart_3494180 baseEnd_3494180 := by
    simpa [prefixWord, tailWord_3494180, baseEnd_3494180] using wordTrace_append hprefix tailTrace_3494180
  have hstable : (prefixWord ++ tailWord_3494180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494180).length < 2 ^ (prefixWord ++ tailWord_3494180).sum := by decide
  have hdescent : baseEnd_3494180 < baseStart_3494180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494181 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 1, 2, 2]
def baseStart_3494181 : Nat := 118140960795 + 3494181 * 2 ^ 59
def prefixEnd_3494181 : Nat := 4983230072969 + 3 ^ 40 * 3494181 * 2
def baseEnd_3494181 : Nat := 1794194346807898734468061

theorem tailTrace_3494181 : CollatzResearch.WordTrace tailWord_3494181 prefixEnd_3494181 1794194346807898734468061 := by
  unfold tailWord_3494181
  simp only [CollatzResearch.WordTrace]
  refine ⟨127443250954186470449530397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84962167302790980299686931 127443250954186470449530397)
  ·
    refine ⟨47791219107819926418573899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127443250954186470449530397 47791219107819926418573899)
    ·
      refine ⟨71686828661729889627860849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47791219107819926418573899 71686828661729889627860849)
      ·
        refine ⟨53765121496297417220895637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71686828661729889627860849 53765121496297417220895637)
        ·
          refine ⟨2520240070138941432229483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53765121496297417220895637 2520240070138941432229483)
          ·
            refine ⟨3780360105208412148344225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520240070138941432229483 3780360105208412148344225)
            ·
              refine ⟨2835270078906309111258169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780360105208412148344225 2835270078906309111258169)
              ·
                refine ⟨2126452559179731833443627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835270078906309111258169 2126452559179731833443627)
                ·
                  refine ⟨3189678838769597750165441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126452559179731833443627 3189678838769597750165441)
                  ·
                    refine ⟨2392259129077198312624081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3189678838769597750165441 2392259129077198312624081)
                    ·
                      refine ⟨1794194346807898734468061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392259129077198312624081 1794194346807898734468061)
                      ·
                        rfl

theorem cell23_3494181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_3494181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494181 prefixEnd_3494181 := by exact prefixLift 3494181
  have htrace : WordTrace (prefixWord ++ tailWord_3494181) baseStart_3494181 baseEnd_3494181 := by
    simpa [prefixWord, tailWord_3494181, baseEnd_3494181] using wordTrace_append hprefix tailTrace_3494181
  have hstable : (prefixWord ++ tailWord_3494181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494181).length < 2 ^ (prefixWord ++ tailWord_3494181).sum := by decide
  have hdescent : baseEnd_3494181 < baseStart_3494181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494196 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3494196 : Nat := 118140960795 + 3494196 * 2 ^ 59
def prefixEnd_3494196 : Nat := 4983230072969 + 3 ^ 40 * 3494196 * 2
def baseEnd_3494196 : Nat := 598067349672572058593497

theorem tailTrace_3494196 : CollatzResearch.WordTrace tailWord_3494196 prefixEnd_3494196 598067349672572058593497 := by
  unfold tailWord_3494196
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721899024566064005663221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84962532032754752007550961 63721899024566064005663221)
  ·
    refine ⟨5973928033553068500530927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63721899024566064005663221 5973928033553068500530927)
    ·
      refine ⟨8960892050329602750796391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5973928033553068500530927 8960892050329602750796391)
      ·
        refine ⟨13441338075494404126194587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8960892050329602750796391 13441338075494404126194587)
        ·
          refine ⟨20162007113241606189291881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13441338075494404126194587 20162007113241606189291881)
          ·
            refine ⟨15121505334931204641968911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20162007113241606189291881 15121505334931204641968911)
            ·
              refine ⟨22682258002396806962953367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15121505334931204641968911 22682258002396806962953367)
              ·
                refine ⟨34023387003595210444430051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22682258002396806962953367 34023387003595210444430051)
                ·
                  refine ⟨51035080505392815666645077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34023387003595210444430051 51035080505392815666645077)
                  ·
                    refine ⟨598067349672572058593497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51035080505392815666645077 598067349672572058593497)
                    ·
                      rfl

theorem cell23_3494196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3494196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494196 prefixEnd_3494196 := by exact prefixLift 3494196
  have htrace : WordTrace (prefixWord ++ tailWord_3494196) baseStart_3494196 baseEnd_3494196 := by
    simpa [prefixWord, tailWord_3494196, baseEnd_3494196] using wordTrace_append hprefix tailTrace_3494196
  have hstable : (prefixWord ++ tailWord_3494196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494196).length < 2 ^ (prefixWord ++ tailWord_3494196).sum := by decide
  have hdescent : baseEnd_3494196 < baseStart_3494196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494249 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_3494249 : Nat := 118140960795 + 3494249 * 2 ^ 59
def prefixEnd_3494249 : Nat := 4983230072969 + 3 ^ 40 * 3494249 * 2
def baseEnd_3494249 : Nat := 1794229263492404468417747

theorem tailTrace_3494249 : CollatzResearch.WordTrace tailWord_3494249 prefixEnd_3494249 1794229263492404468417747 := by
  unfold tailWord_3494249
  simp only [CollatzResearch.WordTrace]
  refine ⟨127445731117940118063005801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84963820745293412042003867 127445731117940118063005801)
  ·
    refine ⟨95584298338455088547254351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127445731117940118063005801 95584298338455088547254351)
    ·
      refine ⟨143376447507682632820881527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95584298338455088547254351 143376447507682632820881527)
      ·
        refine ⟨215064671261523949231322291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143376447507682632820881527 215064671261523949231322291)
        ·
          refine ⟨322597006892285923846983437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215064671261523949231322291 322597006892285923846983437)
          ·
            refine ⟨120973877584607221442618789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322597006892285923846983437 120973877584607221442618789)
            ·
              refine ⟨22682602047113854020491023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120973877584607221442618789 22682602047113854020491023)
              ·
                refine ⟨34023903070670781030736535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22682602047113854020491023 34023903070670781030736535)
                ·
                  refine ⟨51035854606006171546104803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34023903070670781030736535 51035854606006171546104803)
                  ·
                    refine ⟨76553781909009257319157205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51035854606006171546104803 76553781909009257319157205)
                    ·
                      refine ⟨1794229263492404468417747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76553781909009257319157205 1794229263492404468417747)
                      ·
                        rfl

theorem cell23_3494249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_3494249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494249 prefixEnd_3494249 := by exact prefixLift 3494249
  have htrace : WordTrace (prefixWord ++ tailWord_3494249) baseStart_3494249 baseEnd_3494249 := by
    simpa [prefixWord, tailWord_3494249, baseEnd_3494249] using wordTrace_append hprefix tailTrace_3494249
  have hstable : (prefixWord ++ tailWord_3494249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494249).length < 2 ^ (prefixWord ++ tailWord_3494249).sum := by decide
  have hdescent : baseEnd_3494249 < baseStart_3494249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494276 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3494276 : Nat := 118140960795 + 3494276 * 2 ^ 59
def prefixEnd_3494276 : Nat := 4983230072969 + 3 ^ 40 * 3494276 * 2
def baseEnd_3494276 : Nat := 1794243127470075862780123

theorem tailTrace_3494276 : CollatzResearch.WordTrace tailWord_3494276 prefixEnd_3494276 1794243127470075862780123 := by
  unfold tailWord_3494276
  simp only [CollatzResearch.WordTrace]
  refine ⟨63723357944421150837119341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84964477259228201116159121 63723357944421150837119341)
  ·
    refine ⟨23896259229157931563919753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63723357944421150837119341 23896259229157931563919753)
    ·
      refine ⟨17922194421868448672939815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23896259229157931563919753 17922194421868448672939815)
      ·
        refine ⟨26883291632802673009409723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17922194421868448672939815 26883291632802673009409723)
        ·
          refine ⟨40324937449204009514114585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26883291632802673009409723 40324937449204009514114585)
          ·
            refine ⟨30243703086903007135585939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40324937449204009514114585 30243703086903007135585939)
            ·
              refine ⟨45365554630354510703378909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30243703086903007135585939 45365554630354510703378909)
              ·
                refine ⟨17012082986382941513767091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45365554630354510703378909 17012082986382941513767091)
                ·
                  refine ⟨25518124479574412270650637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17012082986382941513767091 25518124479574412270650637)
                  ·
                    refine ⟨9569296679840404601493989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25518124479574412270650637 9569296679840404601493989)
                    ·
                      refine ⟨1794243127470075862780123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9569296679840404601493989 1794243127470075862780123)
                      ·
                        rfl

theorem cell23_3494276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3494276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494276 prefixEnd_3494276 := by exact prefixLift 3494276
  have htrace : WordTrace (prefixWord ++ tailWord_3494276) baseStart_3494276 baseEnd_3494276 := by
    simpa [prefixWord, tailWord_3494276, baseEnd_3494276] using wordTrace_append hprefix tailTrace_3494276
  have hstable : (prefixWord ++ tailWord_3494276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494276).length < 2 ^ (prefixWord ++ tailWord_3494276).sum := by decide
  have hdescent : baseEnd_3494276 < baseStart_3494276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494294 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3494294 : Nat := 118140960795 + 3494294 * 2 ^ 59
def prefixEnd_3494294 : Nat := 4983230072969 + 3 ^ 40 * 3494294 * 2
def baseEnd_3494294 : Nat := 199361374457984088039449

theorem tailTrace_3494294 : CollatzResearch.WordTrace tailWord_3494294 prefixEnd_3494294 199361374457984088039449 := by
  unfold tailWord_3494294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965460775173568171774621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84964914935184727165595957 7965460775173568171774621)
  ·
    refine ⟨2987047790690088064415483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7965460775173568171774621 2987047790690088064415483)
    ·
      refine ⟨4480571686035132096623225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987047790690088064415483 4480571686035132096623225)
      ·
        refine ⟨3360428764526349072467419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480571686035132096623225 3360428764526349072467419)
        ·
          refine ⟨5040643146789523608701129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360428764526349072467419 5040643146789523608701129)
          ·
            refine ⟨3780482360092142706525847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040643146789523608701129 3780482360092142706525847)
            ·
              refine ⟨5670723540138214059788771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780482360092142706525847 5670723540138214059788771)
              ·
                refine ⟨8506085310207321089683157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670723540138214059788771 8506085310207321089683157)
                ·
                  refine ⟨199361374457984088039449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8506085310207321089683157 199361374457984088039449)
                  ·
                    rfl

theorem cell23_3494294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3494294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494294 prefixEnd_3494294 := by exact prefixLift 3494294
  have htrace : WordTrace (prefixWord ++ tailWord_3494294) baseStart_3494294 baseEnd_3494294 := by
    simpa [prefixWord, tailWord_3494294, baseEnd_3494294] using wordTrace_append hprefix tailTrace_3494294
  have hstable : (prefixWord ++ tailWord_3494294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494294).length < 2 ^ (prefixWord ++ tailWord_3494294).sum := by decide
  have hdescent : baseEnd_3494294 < baseStart_3494294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494354 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3494354 : Nat := 118140960795 + 3494354 * 2 ^ 59
def prefixEnd_3494354 : Nat := 4983230072969 + 3 ^ 40 * 3494354 * 2
def baseEnd_3494354 : Nat := 598094392987042185868255

theorem tailTrace_3494354 : CollatzResearch.WordTrace tailWord_3494354 prefixEnd_3494354 598094392987042185868255 := by
  unfold tailWord_3494354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31862390195639930248894529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84966373855039813997052077 31862390195639930248894529)
  ·
    refine ⟨23896792646729947686670897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31862390195639930248894529 23896792646729947686670897)
    ·
      refine ⟨17922594485047460765003173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23896792646729947686670897 17922594485047460765003173)
      ·
        refine ⟨3360486465946398893438095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17922594485047460765003173 3360486465946398893438095)
        ·
          refine ⟨5040729698919598340157143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360486465946398893438095 5040729698919598340157143)
          ·
            refine ⟨7561094548379397510235715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040729698919598340157143 7561094548379397510235715)
            ·
              refine ⟨11341641822569096265353573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561094548379397510235715 11341641822569096265353573)
              ·
                refine ⟨2126557841731705549753795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11341641822569096265353573 2126557841731705549753795)
                ·
                  refine ⟨3189836762597558324630693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126557841731705549753795 3189836762597558324630693)
                  ·
                    refine ⟨598094392987042185868255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3189836762597558324630693 598094392987042185868255)
                    ·
                      rfl

theorem cell23_3494354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3494354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494354 prefixEnd_3494354 := by exact prefixLift 3494354
  have htrace : WordTrace (prefixWord ++ tailWord_3494354) baseStart_3494354 baseEnd_3494354 := by
    simpa [prefixWord, tailWord_3494354, baseEnd_3494354] using wordTrace_append hprefix tailTrace_3494354
  have hstable : (prefixWord ++ tailWord_3494354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494354).length < 2 ^ (prefixWord ++ tailWord_3494354).sum := by decide
  have hdescent : baseEnd_3494354 < baseStart_3494354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494383 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 4]
def baseStart_3494383 : Nat := 118140960795 + 3494383 * 2 ^ 59
def prefixEnd_3494383 : Nat := 4983230072969 + 3 ^ 40 * 3494383 * 2
def baseEnd_3494383 : Nat := 1794298069900106944142131

theorem tailTrace_3494383 : CollatzResearch.WordTrace tailWord_3494383 prefixEnd_3494383 1794298069900106944142131 := by
  unfold tailWord_3494383
  simp only [CollatzResearch.WordTrace]
  refine ⟨127450618499454658948383803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84967078999636439298922535 127450618499454658948383803)
  ·
    refine ⟨191175927749181988422575705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127450618499454658948383803 191175927749181988422575705)
    ·
      refine ⟨143381945811886491316931779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191175927749181988422575705 143381945811886491316931779)
      ·
        refine ⟨215072918717829736975397669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143381945811886491316931779 215072918717829736975397669)
        ·
          refine ⟨40326172259593075682887063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215072918717829736975397669 40326172259593075682887063)
          ·
            refine ⟨60489258389389613524330595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40326172259593075682887063 60489258389389613524330595)
            ·
              refine ⟨90733887584084420286495893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60489258389389613524330595 90733887584084420286495893)
              ·
                refine ⟨4253150980503957200929495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90733887584084420286495893 4253150980503957200929495)
                ·
                  refine ⟨6379726470755935801394243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253150980503957200929495 6379726470755935801394243)
                  ·
                    refine ⟨9569589706133903702091365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6379726470755935801394243 9569589706133903702091365)
                    ·
                      refine ⟨1794298069900106944142131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9569589706133903702091365 1794298069900106944142131)
                      ·
                        rfl

theorem cell23_3494383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_3494383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494383 prefixEnd_3494383 := by exact prefixLift 3494383
  have htrace : WordTrace (prefixWord ++ tailWord_3494383) baseStart_3494383 baseEnd_3494383 := by
    simpa [prefixWord, tailWord_3494383, baseEnd_3494383] using wordTrace_append hprefix tailTrace_3494383
  have hstable : (prefixWord ++ tailWord_3494383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494383).length < 2 ^ (prefixWord ++ tailWord_3494383).sum := by decide
  have hdescent : baseEnd_3494383 < baseStart_3494383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494396 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3494396 : Nat := 118140960795 + 3494396 * 2 ^ 59
def prefixEnd_3494396 : Nat := 4983230072969 + 3 ^ 40 * 3494396 * 2
def baseEnd_3494396 : Nat := 1794304745148615393279571

theorem tailTrace_3494396 : CollatzResearch.WordTrace tailWord_3494396 prefixEnd_3494396 1794304745148615393279571 := by
  unfold tailWord_3494396
  simp only [CollatzResearch.WordTrace]
  refine ⟨63725546324203781084303521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84967395098938374779071361 63725546324203781084303521)
  ·
    refine ⟨47794159743152835813227641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63725546324203781084303521 47794159743152835813227641)
    ·
      refine ⟨35845619807364626859920731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47794159743152835813227641 35845619807364626859920731)
      ·
        refine ⟨53768429711046940289881097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35845619807364626859920731 53768429711046940289881097)
        ·
          refine ⟨40326322283285205217410823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53768429711046940289881097 40326322283285205217410823)
          ·
            refine ⟨60489483424927807826116235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40326322283285205217410823 60489483424927807826116235)
            ·
              refine ⟨90734225137391711739174353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60489483424927807826116235 90734225137391711739174353)
              ·
                refine ⟨68050668853043783804380765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90734225137391711739174353 68050668853043783804380765)
                ·
                  refine ⟨25519000819891418926642787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68050668853043783804380765 25519000819891418926642787)
                  ·
                    refine ⟨38278501229837128389964181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25519000819891418926642787 38278501229837128389964181)
                    ·
                      refine ⟨1794304745148615393279571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38278501229837128389964181 1794304745148615393279571)
                      ·
                        rfl

theorem cell23_3494396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3494396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494396 prefixEnd_3494396 := by exact prefixLift 3494396
  have htrace : WordTrace (prefixWord ++ tailWord_3494396) baseStart_3494396 baseEnd_3494396 := by
    simpa [prefixWord, tailWord_3494396, baseEnd_3494396] using wordTrace_append hprefix tailTrace_3494396
  have hstable : (prefixWord ++ tailWord_3494396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494396).length < 2 ^ (prefixWord ++ tailWord_3494396).sum := by decide
  have hdescent : baseEnd_3494396 < baseStart_3494396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494420 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3494420 : Nat := 118140960795 + 3494420 * 2 ^ 59
def prefixEnd_3494420 : Nat := 4983230072969 + 3 ^ 40 * 3494420 * 2
def baseEnd_3494420 : Nat := 1794317068684323299379461

theorem tailTrace_3494420 : CollatzResearch.WordTrace tailWord_3494420 prefixEnd_3494420 1794317068684323299379461 := by
  unfold tailWord_3494420
  simp only [CollatzResearch.WordTrace]
  refine ⟨63725984000160307133740357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84967978666880409511653809 63725984000160307133740357)
  ·
    refine ⟨11948622000030057587576317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63725984000160307133740357 11948622000030057587576317)
    ·
      refine ⟨4480733250011271595341119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11948622000030057587576317 4480733250011271595341119)
      ·
        refine ⟨6721099875016907393011679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480733250011271595341119 6721099875016907393011679)
        ·
          refine ⟨10081649812525361089517519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721099875016907393011679 10081649812525361089517519)
          ·
            refine ⟨15122474718788041634276279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081649812525361089517519 15122474718788041634276279)
            ·
              refine ⟨22683712078182062451414419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122474718788041634276279 22683712078182062451414419)
              ·
                refine ⟨34025568117273093677121629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22683712078182062451414419 34025568117273093677121629)
                ·
                  refine ⟨12759588043977410128920611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34025568117273093677121629 12759588043977410128920611)
                  ·
                    refine ⟨19139382065966115193380917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12759588043977410128920611 19139382065966115193380917)
                    ·
                      refine ⟨1794317068684323299379461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19139382065966115193380917 1794317068684323299379461)
                      ·
                        rfl

theorem cell23_3494420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3494420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494420 prefixEnd_3494420 := by exact prefixLift 3494420
  have htrace : WordTrace (prefixWord ++ tailWord_3494420) baseStart_3494420 baseEnd_3494420 := by
    simpa [prefixWord, tailWord_3494420, baseEnd_3494420] using wordTrace_append hprefix tailTrace_3494420
  have hstable : (prefixWord ++ tailWord_3494420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494420).length < 2 ^ (prefixWord ++ tailWord_3494420).sum := by decide
  have hdescent : baseEnd_3494420 < baseStart_3494420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494440 : List Nat := [2, 1, 5, 2, 1, 1, 4, 7]
def baseStart_3494440 : Nat := 118140960795 + 3494440 * 2 ^ 59
def prefixEnd_3494440 : Nat := 4983230072969 + 3 ^ 40 * 3494440 * 2
def baseEnd_3494440 : Nat := 66456568085089378560347

theorem tailTrace_3494440 : CollatzResearch.WordTrace tailWord_3494440 prefixEnd_3494440 66456568085089378560347 := by
  unfold tailWord_3494440
  simp only [CollatzResearch.WordTrace]
  refine ⟨63726348730124078841604387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84968464973498771788805849 63726348730124078841604387)
  ·
    refine ⟨95589523095186118262406581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63726348730124078841604387 95589523095186118262406581)
    ·
      refine ⟨8961517790173698587100617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95589523095186118262406581 8961517790173698587100617)
      ·
        refine ⟨6721138342630273940325463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8961517790173698587100617 6721138342630273940325463)
        ·
          refine ⟨10081707513945410910488195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721138342630273940325463 10081707513945410910488195)
          ·
            refine ⟨15122561270918116365732293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081707513945410910488195 15122561270918116365732293)
            ·
              refine ⟨2835480238297146818574805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15122561270918116365732293 2835480238297146818574805)
              ·
                refine ⟨66456568085089378560347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2835480238297146818574805 66456568085089378560347)
                ·
                  rfl

theorem cell23_3494440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 7].length) (baseStart_3494440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494440 prefixEnd_3494440 := by exact prefixLift 3494440
  have htrace : WordTrace (prefixWord ++ tailWord_3494440) baseStart_3494440 baseEnd_3494440 := by
    simpa [prefixWord, tailWord_3494440, baseEnd_3494440] using wordTrace_append hprefix tailTrace_3494440
  have hstable : (prefixWord ++ tailWord_3494440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494440).length < 2 ^ (prefixWord ++ tailWord_3494440).sum := by decide
  have hdescent : baseEnd_3494440 < baseStart_3494440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494443 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 7, 2]
def baseStart_3494443 : Nat := 118140960795 + 3494443 * 2 ^ 59
def prefixEnd_3494443 : Nat := 4983230072969 + 3 ^ 40 * 3494443 * 2
def baseEnd_3494443 : Nat := 1794328878739376709391855

theorem tailTrace_3494443 : CollatzResearch.WordTrace tailWord_3494443 prefixEnd_3494443 1794328878739376709391855 := by
  unfold tailWord_3494443
  simp only [CollatzResearch.WordTrace]
  refine ⟨127452806879237289195567983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84968537919491526130378655 127452806879237289195567983)
  ·
    refine ⟨191179210318855933793351975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127452806879237289195567983 191179210318855933793351975)
    ·
      refine ⟨286768815478283900690027963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191179210318855933793351975 286768815478283900690027963)
      ·
        refine ⟨430153223217425851035041945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286768815478283900690027963 430153223217425851035041945)
        ·
          refine ⟨322614917413069388276281459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430153223217425851035041945 322614917413069388276281459)
          ·
            refine ⟨483922376119604082414422189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322614917413069388276281459 483922376119604082414422189)
            ·
              refine ⟨181470891044851530905408321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483922376119604082414422189 181470891044851530905408321)
              ·
                refine ⟨136103168283638648179056241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181470891044851530905408321 136103168283638648179056241)
                ·
                  refine ⟨102077376212728986134292181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136103168283638648179056241 102077376212728986134292181)
                  ·
                    refine ⟨2392438504985835612522473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102077376212728986134292181 2392438504985835612522473)
                    ·
                      refine ⟨1794328878739376709391855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392438504985835612522473 1794328878739376709391855)
                      ·
                        rfl

theorem cell23_3494443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7, 2].length) (baseStart_3494443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494443 prefixEnd_3494443 := by exact prefixLift 3494443
  have htrace : WordTrace (prefixWord ++ tailWord_3494443) baseStart_3494443 baseEnd_3494443 := by
    simpa [prefixWord, tailWord_3494443, baseEnd_3494443] using wordTrace_append hprefix tailTrace_3494443
  have hstable : (prefixWord ++ tailWord_3494443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494443).length < 2 ^ (prefixWord ++ tailWord_3494443).sum := by decide
  have hdescent : baseEnd_3494443 < baseStart_3494443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494445 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3494445 : Nat := 118140960795 + 3494445 * 2 ^ 59
def prefixEnd_3494445 : Nat := 4983230072969 + 3 ^ 40 * 3494445 * 2
def baseEnd_3494445 : Nat := 1794329905700685701566847

theorem tailTrace_3494445 : CollatzResearch.WordTrace tailWord_3494445 prefixEnd_3494445 1794329905700685701566847 := by
  unfold tailWord_3494445
  simp only [CollatzResearch.WordTrace]
  refine ⟨127452879825230043537140789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84968586550153362358093859 127452879825230043537140789)
  ·
    refine ⟨11948707483615316581606949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127452879825230043537140789 11948707483615316581606949)
    ·
      refine ⟨2240382653177871859051303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11948707483615316581606949 2240382653177871859051303)
      ·
        refine ⟨3360573979766807788576955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240382653177871859051303 3360573979766807788576955)
        ·
          refine ⟨5040860969650211682865433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360573979766807788576955 5040860969650211682865433)
          ·
            refine ⟨3780645727237658762149075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040860969650211682865433 3780645727237658762149075)
            ·
              refine ⟨5670968590856488143223613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780645727237658762149075 5670968590856488143223613)
              ·
                refine ⟨2126613221571183053708855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5670968590856488143223613 2126613221571183053708855)
                ·
                  refine ⟨3189919832356774580563283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126613221571183053708855 3189919832356774580563283)
                  ·
                    refine ⟨4784879748535161870844925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189919832356774580563283 4784879748535161870844925)
                    ·
                      refine ⟨1794329905700685701566847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4784879748535161870844925 1794329905700685701566847)
                      ·
                        rfl

theorem cell23_3494445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3494445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494445 prefixEnd_3494445 := by exact prefixLift 3494445
  have htrace : WordTrace (prefixWord ++ tailWord_3494445) baseStart_3494445 baseEnd_3494445 := by
    simpa [prefixWord, tailWord_3494445, baseEnd_3494445] using wordTrace_append hprefix tailTrace_3494445
  have hstable : (prefixWord ++ tailWord_3494445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494445).length < 2 ^ (prefixWord ++ tailWord_3494445).sum := by decide
  have hdescent : baseEnd_3494445 < baseStart_3494445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494450 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_3494450 : Nat := 118140960795 + 3494450 * 2 ^ 59
def prefixEnd_3494450 : Nat := 4983230072969 + 3 ^ 40 * 3494450 * 2
def baseEnd_3494450 : Nat := 1794332473103958182004323

theorem tailTrace_3494450 : CollatzResearch.WordTrace tailWord_3494450 prefixEnd_3494450 1794332473103958182004323 := by
  unfold tailWord_3494450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31863265547552982347768201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84968708126807952927381869 31863265547552982347768201)
  ·
    refine ⟨23897449160664736760826151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31863265547552982347768201 23897449160664736760826151)
    ·
      refine ⟨35846173740997105141239227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23897449160664736760826151 35846173740997105141239227)
      ·
        refine ⟨53769260611495657711858841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35846173740997105141239227 53769260611495657711858841)
        ·
          refine ⟨40326945458621743283894131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53769260611495657711858841 40326945458621743283894131)
          ·
            refine ⟨60490418187932614925841197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40326945458621743283894131 60490418187932614925841197)
            ·
              refine ⟨22683906820474730597190449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60490418187932614925841197 22683906820474730597190449)
              ·
                refine ⟨17012930115356047947892837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22683906820474730597190449 17012930115356047947892837)
                ·
                  refine ⟨3189924396629258990229907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17012930115356047947892837 3189924396629258990229907)
                  ·
                    refine ⟨4784886594943888485344861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189924396629258990229907 4784886594943888485344861)
                    ·
                      refine ⟨1794332473103958182004323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4784886594943888485344861 1794332473103958182004323)
                      ·
                        rfl

theorem cell23_3494450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_3494450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494450 prefixEnd_3494450 := by exact prefixLift 3494450
  have htrace : WordTrace (prefixWord ++ tailWord_3494450) baseStart_3494450 baseEnd_3494450 := by
    simpa [prefixWord, tailWord_3494450, baseEnd_3494450] using wordTrace_append hprefix tailTrace_3494450
  have hstable : (prefixWord ++ tailWord_3494450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494450).length < 2 ^ (prefixWord ++ tailWord_3494450).sum := by decide
  have hdescent : baseEnd_3494450 < baseStart_3494450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494484 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_3494484 : Nat := 118140960795 + 3494484 * 2 ^ 59
def prefixEnd_3494484 : Nat := 4983230072969 + 3 ^ 40 * 3494484 * 2
def baseEnd_3494484 : Nat := 1794349931446211048979167

theorem tailTrace_3494484 : CollatzResearch.WordTrace tailWord_3494484 prefixEnd_3494484 1794349931446211048979167 := by
  unfold tailWord_3494484
  simp only [CollatzResearch.WordTrace]
  refine ⟨63727151136044376598905253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84969534848059168798540337 63727151136044376598905253)
  ·
    refine ⟨11948840838008320612294735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63727151136044376598905253 11948840838008320612294735)
    ·
      refine ⟨17923261257012480918442103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11948840838008320612294735 17923261257012480918442103)
      ·
        refine ⟨26884891885518721377663155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17923261257012480918442103 26884891885518721377663155)
        ·
          refine ⟨40327337828278082066494733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26884891885518721377663155 40327337828278082066494733)
          ·
            refine ⟨15122751685604280774935525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40327337828278082066494733 15122751685604280774935525)
            ·
              refine ⟨2835515941050802645300411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15122751685604280774935525 2835515941050802645300411)
              ·
                refine ⟨4253273911576203967950617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835515941050802645300411 4253273911576203967950617)
                ·
                  refine ⟨3189955433682152975962963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4253273911576203967950617 3189955433682152975962963)
                  ·
                    refine ⟨4784933150523229463944445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189955433682152975962963 4784933150523229463944445)
                    ·
                      refine ⟨1794349931446211048979167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4784933150523229463944445 1794349931446211048979167)
                      ·
                        rfl

theorem cell23_3494484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_3494484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494484 prefixEnd_3494484 := by exact prefixLift 3494484
  have htrace : WordTrace (prefixWord ++ tailWord_3494484) baseStart_3494484 baseEnd_3494484 := by
    simpa [prefixWord, tailWord_3494484, baseEnd_3494484] using wordTrace_append hprefix tailTrace_3494484
  have hstable : (prefixWord ++ tailWord_3494484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494484).length < 2 ^ (prefixWord ++ tailWord_3494484).sum := by decide
  have hdescent : baseEnd_3494484 < baseStart_3494484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494503 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3494503 : Nat := 118140960795 + 3494503 * 2 ^ 59
def prefixEnd_3494503 : Nat := 4983230072969 + 3 ^ 40 * 3494503 * 2
def baseEnd_3494503 : Nat := 1794359687578646474641579

theorem tailTrace_3494503 : CollatzResearch.WordTrace tailWord_3494503 prefixEnd_3494503 1794359687578646474641579 := by
  unfold tailWord_3494503
  simp only [CollatzResearch.WordTrace]
  refine ⟨127454995259019919442752163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84969996839346612961834775 127454995259019919442752163)
  ·
    refine ⟨191182492888529879164128245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127454995259019919442752163 191182492888529879164128245)
    ·
      refine ⟨17923358708299676171637023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191182492888529879164128245 17923358708299676171637023)
      ·
        refine ⟨26885038062449514257455535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17923358708299676171637023 26885038062449514257455535)
        ·
          refine ⟨40327557093674271386183303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26885038062449514257455535 40327557093674271386183303)
          ·
            refine ⟨60491335640511407079274955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40327557093674271386183303 60491335640511407079274955)
            ·
              refine ⟨90737003460767110618912433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60491335640511407079274955 90737003460767110618912433)
              ·
                refine ⟨68052752595575332964184325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90737003460767110618912433 68052752595575332964184325)
                ·
                  refine ⟨12759891111670374930784561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68052752595575332964184325 12759891111670374930784561)
                  ·
                    refine ⟨9569918333752781198088421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12759891111670374930784561 9569918333752781198088421)
                    ·
                      refine ⟨1794359687578646474641579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9569918333752781198088421 1794359687578646474641579)
                      ·
                        rfl

theorem cell23_3494503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3494503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494503 prefixEnd_3494503 := by exact prefixLift 3494503
  have htrace : WordTrace (prefixWord ++ tailWord_3494503) baseStart_3494503 baseEnd_3494503 := by
    simpa [prefixWord, tailWord_3494503, baseEnd_3494503] using wordTrace_append hprefix tailTrace_3494503
  have hstable : (prefixWord ++ tailWord_3494503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494503).length < 2 ^ (prefixWord ++ tailWord_3494503).sum := by decide
  have hdescent : baseEnd_3494503 < baseStart_3494503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494510 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3494510 : Nat := 118140960795 + 3494510 * 2 ^ 59
def prefixEnd_3494510 : Nat := 4983230072969 + 3 ^ 40 * 3494510 * 2
def baseEnd_3494510 : Nat := 1794363281943227947254047

theorem tailTrace_3494510 : CollatzResearch.WordTrace tailWord_3494510 prefixEnd_3494510 1794363281943227947254047 := by
  unfold tailWord_3494510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931906321249319954782123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84970167046663039758837989 15931906321249319954782123)
  ·
    refine ⟨23897859481873979932173185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931906321249319954782123 23897859481873979932173185)
    ·
      refine ⟨17923394611405484949129889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23897859481873979932173185 17923394611405484949129889)
      ·
        refine ⟨13442545958554113711847417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17923394611405484949129889 13442545958554113711847417)
        ·
          refine ⟨10081909468915585283885563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13442545958554113711847417 10081909468915585283885563)
          ·
            refine ⟨15122864203373377925828345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081909468915585283885563 15122864203373377925828345)
            ·
              refine ⟨11342148152530033444371259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15122864203373377925828345 11342148152530033444371259)
              ·
                refine ⟨17013222228795050166556889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342148152530033444371259 17013222228795050166556889)
                ·
                  refine ⟨12759916671596287624917667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17013222228795050166556889 12759916671596287624917667)
                  ·
                    refine ⟨19139875007394431437376501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12759916671596287624917667 19139875007394431437376501)
                    ·
                      refine ⟨1794363281943227947254047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19139875007394431437376501 1794363281943227947254047)
                      ·
                        rfl

theorem cell23_3494510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3494510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494510 prefixEnd_3494510 := by exact prefixLift 3494510
  have htrace : WordTrace (prefixWord ++ tailWord_3494510) baseStart_3494510 baseEnd_3494510 := by
    simpa [prefixWord, tailWord_3494510, baseEnd_3494510] using wordTrace_append hprefix tailTrace_3494510
  have hstable : (prefixWord ++ tailWord_3494510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494510).length < 2 ^ (prefixWord ++ tailWord_3494510).sum := by decide
  have hdescent : baseEnd_3494510 < baseStart_3494510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494560 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 1, 7]
def baseStart_3494560 : Nat := 118140960795 + 3494560 * 2 ^ 59
def prefixEnd_3494560 : Nat := 4983230072969 + 3 ^ 40 * 3494560 * 2
def baseEnd_3494560 : Nat := 598129651991984250542939

theorem tailTrace_3494560 : CollatzResearch.WordTrace tailWord_3494560 prefixEnd_3494560 598129651991984250542939 := by
  unfold tailWord_3494560
  simp only [CollatzResearch.WordTrace]
  refine ⟨63728537109906709088788567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84971382813208945451718089 63728537109906709088788567)
  ·
    refine ⟨95592805664860063633182851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63728537109906709088788567 95592805664860063633182851)
    ·
      refine ⟨143389208497290095449774277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95592805664860063633182851 143389208497290095449774277)
      ·
        refine ⟨26885476593241892896832677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143389208497290095449774277 26885476593241892896832677)
        ·
          refine ⟨5041026861232854918156127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26885476593241892896832677 5041026861232854918156127)
          ·
            refine ⟨7561540291849282377234191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5041026861232854918156127 7561540291849282377234191)
            ·
              refine ⟨11342310437773923565851287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561540291849282377234191 11342310437773923565851287)
              ·
                refine ⟨17013465656660885348776931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342310437773923565851287 17013465656660885348776931)
                ·
                  refine ⟨25520198484991328023165397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17013465656660885348776931 25520198484991328023165397)
                  ·
                    refine ⟨598129651991984250542939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25520198484991328023165397 598129651991984250542939)
                    ·
                      rfl

theorem cell23_3494560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_3494560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494560 prefixEnd_3494560 := by exact prefixLift 3494560
  have htrace : WordTrace (prefixWord ++ tailWord_3494560) baseStart_3494560 baseEnd_3494560 := by
    simpa [prefixWord, tailWord_3494560, baseEnd_3494560] using wordTrace_append hprefix tailTrace_3494560
  have hstable : (prefixWord ++ tailWord_3494560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494560).length < 2 ^ (prefixWord ++ tailWord_3494560).sum := by decide
  have hdescent : baseEnd_3494560 < baseStart_3494560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494600 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_3494600 : Nat := 118140960795 + 3494600 * 2 ^ 59
def prefixEnd_3494600 : Nat := 4983230072969 + 3 ^ 40 * 3494600 * 2
def baseEnd_3494600 : Nat := 1794409495202132595128633

theorem tailTrace_3494600 : CollatzResearch.WordTrace tailWord_3494600 prefixEnd_3494600 1794409495202132595128633 := by
  unfold tailWord_3494600
  simp only [CollatzResearch.WordTrace]
  refine ⟨63729266569834252504516627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84972355426445670006022169 63729266569834252504516627)
  ·
    refine ⟨95593899854751378756774941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63729266569834252504516627 95593899854751378756774941)
    ·
      refine ⟨35847712445531767033790603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95593899854751378756774941 35847712445531767033790603)
      ·
        refine ⟨53771568668297650550685905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35847712445531767033790603 53771568668297650550685905)
        ·
          refine ⟨40328676501223237913014429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53771568668297650550685905 40328676501223237913014429)
          ·
            refine ⟨15123253687958714217380411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40328676501223237913014429 15123253687958714217380411)
            ·
              refine ⟨22684880531938071326070617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123253687958714217380411 22684880531938071326070617)
              ·
                refine ⟨17013660398953553494552963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22684880531938071326070617 17013660398953553494552963)
                ·
                  refine ⟨25520490598430330241829445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17013660398953553494552963 25520490598430330241829445)
                  ·
                    refine ⟨4785091987205686920343021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25520490598430330241829445 4785091987205686920343021)
                    ·
                      refine ⟨1794409495202132595128633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4785091987205686920343021 1794409495202132595128633)
                      ·
                        rfl

theorem cell23_3494600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_3494600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494600 prefixEnd_3494600 := by exact prefixLift 3494600
  have htrace : WordTrace (prefixWord ++ tailWord_3494600) baseStart_3494600 baseEnd_3494600 := by
    simpa [prefixWord, tailWord_3494600, baseEnd_3494600] using wordTrace_append hprefix tailTrace_3494600
  have hstable : (prefixWord ++ tailWord_3494600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494600).length < 2 ^ (prefixWord ++ tailWord_3494600).sum := by decide
  have hdescent : baseEnd_3494600 < baseStart_3494600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494643 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_3494643 : Nat := 118140960795 + 3494643 * 2 ^ 59
def prefixEnd_3494643 : Nat := 4983230072969 + 3 ^ 40 * 3494643 * 2
def baseEnd_3494643 : Nat := 1794431574870275926890935

theorem tailTrace_3494643 : CollatzResearch.WordTrace tailWord_3494643 prefixEnd_3494643 1794431574870275926890935 := by
  unfold tailWord_3494643
  simp only [CollatzResearch.WordTrace]
  refine ⟨127460101478512723352848583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84973400985675148901899055 127460101478512723352848583)
  ·
    refine ⟨191190152217769085029272875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127460101478512723352848583 191190152217769085029272875)
    ·
      refine ⟨286785228326653627543909313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191190152217769085029272875 286785228326653627543909313)
      ·
        refine ⟨215088921244990220657931985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286785228326653627543909313 215088921244990220657931985)
        ·
          refine ⟨161316690933742665493448989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215088921244990220657931985 161316690933742665493448989)
          ·
            refine ⟨60493759100153499560043371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161316690933742665493448989 60493759100153499560043371)
            ·
              refine ⟨90740638650230249340065057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60493759100153499560043371 90740638650230249340065057)
              ·
                refine ⟨68055478987672687005048793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90740638650230249340065057 68055478987672687005048793)
                ·
                  refine ⟨51041609240754515253786595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68055478987672687005048793 51041609240754515253786595)
                  ·
                    refine ⟨76562413861131772880679893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51041609240754515253786595 76562413861131772880679893)
                    ·
                      refine ⟨1794431574870275926890935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76562413861131772880679893 1794431574870275926890935)
                      ·
                        rfl

theorem cell23_3494643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_3494643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494643 prefixEnd_3494643 := by exact prefixLift 3494643
  have htrace : WordTrace (prefixWord ++ tailWord_3494643) baseStart_3494643 baseEnd_3494643 := by
    simpa [prefixWord, tailWord_3494643, baseEnd_3494643] using wordTrace_append hprefix tailTrace_3494643
  have hstable : (prefixWord ++ tailWord_3494643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494643).length < 2 ^ (prefixWord ++ tailWord_3494643).sum := by decide
  have hdescent : baseEnd_3494643 < baseStart_3494643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
