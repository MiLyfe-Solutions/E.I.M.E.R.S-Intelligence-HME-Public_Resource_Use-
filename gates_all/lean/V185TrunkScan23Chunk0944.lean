import V185TrunkScan23Chunk0943

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5587681 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 3, 4]
def baseStart_5587681 : Nat := 118140960795 + 5587681 * 2 ^ 59
def prefixEnd_5587681 : Nat := 4983230072969 + 3 ^ 40 * 5587681 * 2
def baseEnd_5587681 : Nat := 956388698998485968696743

theorem tailTrace_5587681 : CollatzResearch.WordTrace tailWord_5587681 prefixEnd_5587681 956388698998485968696743 := by
  unfold tailWord_5587681
  simp only [CollatzResearch.WordTrace]
  refine ⟨203799468869793511784210897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135866312579862341189473931 203799468869793511784210897)
  ·
    refine ⟨152849601652345133838158173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203799468869793511784210897 152849601652345133838158173)
    ·
      refine ⟨57318600619629425189309315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152849601652345133838158173 57318600619629425189309315)
      ·
        refine ⟨85977900929444137783963973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57318600619629425189309315 85977900929444137783963973)
        ·
          refine ⟨16120856424270775834493245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85977900929444137783963973 16120856424270775834493245)
          ·
            refine ⟨6045321159101540937934967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16120856424270775834493245 6045321159101540937934967)
            ·
              refine ⟨9067981738652311406902451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045321159101540937934967 9067981738652311406902451)
              ·
                refine ⟨13601972607978467110353677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067981738652311406902451 13601972607978467110353677)
                ·
                  refine ⟨5100739727991925166382629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13601972607978467110353677 5100739727991925166382629)
                  ·
                    refine ⟨956388698998485968696743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5100739727991925166382629 956388698998485968696743)
                    ·
                      rfl

theorem cell23_5587681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_5587681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587681 prefixEnd_5587681 := by exact prefixLift 5587681
  have htrace : WordTrace (prefixWord ++ tailWord_5587681) baseStart_5587681 baseEnd_5587681 := by
    simpa [prefixWord, tailWord_5587681, baseEnd_5587681] using wordTrace_append hprefix tailTrace_5587681
  have hstable : (prefixWord ++ tailWord_5587681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587681).length < 2 ^ (prefixWord ++ tailWord_5587681).sum := by decide
  have hdescent : baseEnd_5587681 < baseStart_5587681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587694 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_5587694 : Nat := 118140960795 + 5587694 * 2 ^ 59
def prefixEnd_5587694 : Nat := 4983230072969 + 3 ^ 40 * 5587694 * 2
def baseEnd_5587694 : Nat := 318796974693774039469741

theorem tailTrace_5587694 : CollatzResearch.WordTrace tailWord_5587694 prefixEnd_5587694 318796974693774039469741 := by
  unfold tailWord_5587694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25474992877343301875554267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135866628679164276669622757 25474992877343301875554267)
  ·
    refine ⟨38212489316014952813331401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25474992877343301875554267 38212489316014952813331401)
    ·
      refine ⟨28659366987011214609998551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38212489316014952813331401 28659366987011214609998551)
      ·
        refine ⟨42989050480516821914997827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28659366987011214609998551 42989050480516821914997827)
        ·
          refine ⟨64483575720775232872496741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42989050480516821914997827 64483575720775232872496741)
          ·
            refine ⟨12090670447645356163593139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64483575720775232872496741 12090670447645356163593139)
            ·
              refine ⟨18136005671468034245389709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12090670447645356163593139 18136005671468034245389709)
              ·
                refine ⟨6801002126800512842021141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18136005671468034245389709 6801002126800512842021141)
                ·
                  refine ⟨318796974693774039469741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6801002126800512842021141 318796974693774039469741)
                  ·
                    rfl

theorem cell23_5587694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_5587694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587694 prefixEnd_5587694 := by exact prefixLift 5587694
  have htrace : WordTrace (prefixWord ++ tailWord_5587694) baseStart_5587694 baseEnd_5587694 := by
    simpa [prefixWord, tailWord_5587694, baseEnd_5587694] using wordTrace_append hprefix tailTrace_5587694
  have hstable : (prefixWord ++ tailWord_5587694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587694).length < 2 ^ (prefixWord ++ tailWord_5587694).sum := by decide
  have hdescent : baseEnd_5587694 < baseStart_5587694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587704 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_5587704 : Nat := 118140960795 + 5587704 * 2 ^ 59
def prefixEnd_5587704 : Nat := 4983230072969 + 3 ^ 40 * 5587704 * 2
def baseEnd_5587704 : Nat := 2869177907050511316102623

theorem tailTrace_5587704 : CollatzResearch.WordTrace tailWord_5587704 prefixEnd_5587704 2869177907050511316102623 := by
  unfold tailWord_5587704
  simp only [CollatzResearch.WordTrace]
  refine ⟨101900153874355093356149083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135866871832473457808198777 101900153874355093356149083)
  ·
    refine ⟨152850230811532640034223625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101900153874355093356149083 152850230811532640034223625)
    ·
      refine ⟨114637673108649480025667719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152850230811532640034223625 114637673108649480025667719)
      ·
        refine ⟨171956509662974220038501579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114637673108649480025667719 171956509662974220038501579)
        ·
          refine ⟨257934764494461330057752369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171956509662974220038501579 257934764494461330057752369)
          ·
            refine ⟨193451073370845997543314277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257934764494461330057752369 193451073370845997543314277)
            ·
              refine ⟨36272076257033624539371427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193451073370845997543314277 36272076257033624539371427)
              ·
                refine ⟨54408114385550436809057141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36272076257033624539371427 54408114385550436809057141)
                ·
                  refine ⟨5100760723645353450849107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54408114385550436809057141 5100760723645353450849107)
                  ·
                    refine ⟨7651141085468030176273661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100760723645353450849107 7651141085468030176273661)
                    ·
                      refine ⟨2869177907050511316102623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651141085468030176273661 2869177907050511316102623)
                      ·
                        rfl

theorem cell23_5587704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_5587704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587704 prefixEnd_5587704 := by exact prefixLift 5587704
  have htrace : WordTrace (prefixWord ++ tailWord_5587704) baseStart_5587704 baseEnd_5587704 := by
    simpa [prefixWord, tailWord_5587704, baseEnd_5587704] using wordTrace_append hprefix tailTrace_5587704
  have hstable : (prefixWord ++ tailWord_5587704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587704).length < 2 ^ (prefixWord ++ tailWord_5587704).sum := by decide
  have hdescent : baseEnd_5587704 < baseStart_5587704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587738 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3]
def baseStart_5587738 : Nat := 118140960795 + 5587738 * 2 ^ 59
def prefixEnd_5587738 : Nat := 4983230072969 + 3 ^ 40 * 5587738 * 2
def baseEnd_5587738 : Nat := 2869195365392764183077467

theorem tailTrace_5587738 : CollatzResearch.WordTrace tailWord_5587738 prefixEnd_5587738 2869195365392764183077467 := by
  unfold tailWord_5587738
  simp only [CollatzResearch.WordTrace]
  refine ⟨50950386957646752629758967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135867698553724673679357245 50950386957646752629758967)
  ·
    refine ⟨76425580436470128944638451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50950386957646752629758967 76425580436470128944638451)
    ·
      refine ⟨114638370654705193416957677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76425580436470128944638451 114638370654705193416957677)
      ·
        refine ⟨42989388995514447531359129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114638370654705193416957677 42989388995514447531359129)
        ·
          refine ⟨32242041746635835648519347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42989388995514447531359129 32242041746635835648519347)
          ·
            refine ⟨48363062619953753472779021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32242041746635835648519347 48363062619953753472779021)
            ·
              refine ⟨18136148482482657552292133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48363062619953753472779021 18136148482482657552292133)
              ·
                refine ⟨3400527840465498291054775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18136148482482657552292133 3400527840465498291054775)
                ·
                  refine ⟨5100791760698247436582163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400527840465498291054775 5100791760698247436582163)
                  ·
                    refine ⟨7651187641047371154873245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100791760698247436582163 7651187641047371154873245)
                    ·
                      refine ⟨2869195365392764183077467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651187641047371154873245 2869195365392764183077467)
                      ·
                        rfl

theorem cell23_5587738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_5587738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587738 prefixEnd_5587738 := by exact prefixLift 5587738
  have htrace : WordTrace (prefixWord ++ tailWord_5587738) baseStart_5587738 baseEnd_5587738 := by
    simpa [prefixWord, tailWord_5587738, baseEnd_5587738] using wordTrace_append hprefix tailTrace_5587738
  have hstable : (prefixWord ++ tailWord_5587738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587738).length < 2 ^ (prefixWord ++ tailWord_5587738).sum := by decide
  have hdescent : baseEnd_5587738 < baseStart_5587738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587744 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5587744 : Nat := 118140960795 + 5587744 * 2 ^ 59
def prefixEnd_5587744 : Nat := 4983230072969 + 3 ^ 40 * 5587744 * 2
def baseEnd_5587744 : Nat := 2869198446276691159602439

theorem tailTrace_5587744 : CollatzResearch.WordTrace tailWord_5587744 prefixEnd_5587744 2869198446276691159602439 := by
  unfold tailWord_5587744
  simp only [CollatzResearch.WordTrace]
  refine ⟨101900883334282636771877143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135867844445710182362502857 101900883334282636771877143)
  ·
    refine ⟨152851325001423955157815715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101900883334282636771877143 152851325001423955157815715)
    ·
      refine ⟨229276987502135932736723573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152851325001423955157815715 229276987502135932736723573)
      ·
        refine ⟨21494717578325243694067835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229276987502135932736723573 21494717578325243694067835)
        ·
          refine ⟨32242076367487865541101753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21494717578325243694067835 32242076367487865541101753)
          ·
            refine ⟨24181557275615899155826315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32242076367487865541101753 24181557275615899155826315)
            ·
              refine ⟨36272335913423848733739473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24181557275615899155826315 36272335913423848733739473)
              ·
                refine ⟨27204251935067886550304605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36272335913423848733739473 27204251935067886550304605)
                ·
                  refine ⟨10201594475650457456364227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27204251935067886550304605 10201594475650457456364227)
                  ·
                    refine ⟨15302391713475686184546341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10201594475650457456364227 15302391713475686184546341)
                    ·
                      refine ⟨2869198446276691159602439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15302391713475686184546341 2869198446276691159602439)
                      ·
                        rfl

theorem cell23_5587744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5587744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587744 prefixEnd_5587744 := by exact prefixLift 5587744
  have htrace : WordTrace (prefixWord ++ tailWord_5587744) baseStart_5587744 baseEnd_5587744 := by
    simpa [prefixWord, tailWord_5587744, baseEnd_5587744] using wordTrace_append hprefix tailTrace_5587744
  have hstable : (prefixWord ++ tailWord_5587744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587744).length < 2 ^ (prefixWord ++ tailWord_5587744).sum := by decide
  have hdescent : baseEnd_5587744 < baseStart_5587744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587747 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5]
def baseStart_5587747 : Nat := 118140960795 + 5587747 * 2 ^ 59
def prefixEnd_5587747 : Nat := 4983230072969 + 3 ^ 40 * 5587747 * 2
def baseEnd_5587747 : Nat := 2869199986718654647864925

theorem tailTrace_5587747 : CollatzResearch.WordTrace tailWord_5587747 prefixEnd_5587747 2869199986718654647864925 := by
  unfold tailWord_5587747
  simp only [CollatzResearch.WordTrace]
  refine ⟨203801876087554405056113495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135867917391702936704075663 203801876087554405056113495)
  ·
    refine ⟨305702814131331607584170243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203801876087554405056113495 305702814131331607584170243)
    ·
      refine ⟨458554221196997411376255365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305702814131331607584170243 458554221196997411376255365)
      ·
        refine ⟨85978916474437014633047881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 458554221196997411376255365 85978916474437014633047881)
        ·
          refine ⟨64484187355827760974785911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85978916474437014633047881 64484187355827760974785911)
          ·
            refine ⟨96726281033741641462178867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64484187355827760974785911 96726281033741641462178867)
            ·
              refine ⟨145089421550612462193268301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96726281033741641462178867 145089421550612462193268301)
              ·
                refine ⟨54408533081479673322475613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145089421550612462193268301 54408533081479673322475613)
                ·
                  refine ⟨20403199905554877495928355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54408533081479673322475613 20403199905554877495928355)
                  ·
                    refine ⟨30604799858332316243892533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20403199905554877495928355 30604799858332316243892533)
                    ·
                      refine ⟨2869199986718654647864925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30604799858332316243892533 2869199986718654647864925)
                      ·
                        rfl

theorem cell23_5587747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_5587747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587747 prefixEnd_5587747 := by exact prefixLift 5587747
  have htrace : WordTrace (prefixWord ++ tailWord_5587747) baseStart_5587747 baseEnd_5587747 := by
    simpa [prefixWord, tailWord_5587747, baseEnd_5587747] using wordTrace_append hprefix tailTrace_5587747
  have hstable : (prefixWord ++ tailWord_5587747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587747).length < 2 ^ (prefixWord ++ tailWord_5587747).sum := by decide
  have hdescent : baseEnd_5587747 < baseStart_5587747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587788 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_5587788 : Nat := 118140960795 + 5587788 * 2 ^ 59
def prefixEnd_5587788 : Nat := 4983230072969 + 3 ^ 40 * 5587788 * 2
def baseEnd_5587788 : Nat := 956407013141829662484079

theorem tailTrace_5587788 : CollatzResearch.WordTrace tailWord_5587788 prefixEnd_5587788 956407013141829662484079 := by
  unfold tailWord_5587788
  simp only [CollatzResearch.WordTrace]
  refine ⟨101901685740202934529178009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135868914320270579372237345 101901685740202934529178009)
  ·
    refine ⟨76426264305152200896883507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101901685740202934529178009 76426264305152200896883507)
    ·
      refine ⟨114639396457728301345325261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76426264305152200896883507 114639396457728301345325261)
      ·
        refine ⟨42989773671648113004496973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114639396457728301345325261 42989773671648113004496973)
        ·
          refine ⟨16121165126868042376686365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42989773671648113004496973 16121165126868042376686365)
          ·
            refine ⟨6045436922575515891257387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16121165126868042376686365 6045436922575515891257387)
            ·
              refine ⟨9068155383863273836886081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045436922575515891257387 9068155383863273836886081)
              ·
                refine ⟨6801116537897455377664561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9068155383863273836886081 6801116537897455377664561)
                ·
                  refine ⟨5100837403423091533248421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6801116537897455377664561 5100837403423091533248421)
                  ·
                    refine ⟨956407013141829662484079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5100837403423091533248421 956407013141829662484079)
                    ·
                      rfl

theorem cell23_5587788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_5587788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587788 prefixEnd_5587788 := by exact prefixLift 5587788
  have htrace : WordTrace (prefixWord ++ tailWord_5587788) baseStart_5587788 baseEnd_5587788 := by
    simpa [prefixWord, tailWord_5587788, baseEnd_5587788] using wordTrace_append hprefix tailTrace_5587788
  have hstable : (prefixWord ++ tailWord_5587788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587788).length < 2 ^ (prefixWord ++ tailWord_5587788).sum := by decide
  have hdescent : baseEnd_5587788 < baseStart_5587788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587811 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 3]
def baseStart_5587811 : Nat := 118140960795 + 5587811 * 2 ^ 59
def prefixEnd_5587811 : Nat := 4983230072969 + 3 ^ 40 * 5587811 * 2
def baseEnd_5587811 : Nat := 2869232849480542397464631

theorem tailTrace_5587811 : CollatzResearch.WordTrace tailWord_5587811 prefixEnd_5587811 2869232849480542397464631 := by
  unfold tailWord_5587811
  simp only [CollatzResearch.WordTrace]
  refine ⟨203804210359322543986443287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135869473572881695990962191 203804210359322543986443287)
  ·
    refine ⟨305706315538983815979664931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203804210359322543986443287 305706315538983815979664931)
    ·
      refine ⟨458559473308475723969497397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305706315538983815979664931 458559473308475723969497397)
      ·
        refine ⟨42989950622669599122140381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 458559473308475723969497397 42989950622669599122140381)
        ·
          refine ⟨16121231483501099670802643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42989950622669599122140381 16121231483501099670802643)
          ·
            refine ⟨24181847225251649506203965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16121231483501099670802643 24181847225251649506203965)
            ·
              refine ⟨9068192709469368564826487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24181847225251649506203965 9068192709469368564826487)
              ·
                refine ⟨13602289064204052847239731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9068192709469368564826487 13602289064204052847239731)
                ·
                  refine ⟨20403433596306079270859597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13602289064204052847239731 20403433596306079270859597)
                  ·
                    refine ⟨7651287598614779726572349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20403433596306079270859597 7651287598614779726572349)
                    ·
                      refine ⟨2869232849480542397464631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651287598614779726572349 2869232849480542397464631)
                      ·
                        rfl

theorem cell23_5587811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_5587811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587811 prefixEnd_5587811 := by exact prefixLift 5587811
  have htrace : WordTrace (prefixWord ++ tailWord_5587811) baseStart_5587811 baseEnd_5587811 := by
    simpa [prefixWord, tailWord_5587811, baseEnd_5587811] using wordTrace_append hprefix tailTrace_5587811
  have hstable : (prefixWord ++ tailWord_5587811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587811).length < 2 ^ (prefixWord ++ tailWord_5587811).sum := by decide
  have hdescent : baseEnd_5587811 < baseStart_5587811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587827 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 8]
def baseStart_5587827 : Nat := 118140960795 + 5587827 * 2 ^ 59
def prefixEnd_5587827 : Nat := 4983230072969 + 3 ^ 40 * 5587827 * 2
def baseEnd_5587827 : Nat := 956413688390338111621519

theorem tailTrace_5587827 : CollatzResearch.WordTrace tailWord_5587827 prefixEnd_5587827 956413688390338111621519 := by
  unfold tailWord_5587827
  simp only [CollatzResearch.WordTrace]
  refine ⟨203804793927264578719025735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135869862618176385812683823 203804793927264578719025735)
  ·
    refine ⟨305707190890896868078538603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203804793927264578719025735 305707190890896868078538603)
    ·
      refine ⟨458560786336345302117807905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305707190890896868078538603 458560786336345302117807905)
      ·
        refine ⟨343920589752258976588355929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458560786336345302117807905 343920589752258976588355929)
        ·
          refine ⟨257940442314194232441266947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343920589752258976588355929 257940442314194232441266947)
          ·
            refine ⟨386910663471291348661900421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257940442314194232441266947 386910663471291348661900421)
            ·
              refine ⟨72545749400867127874106329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 386910663471291348661900421 72545749400867127874106329)
              ·
                refine ⟨54409312050650345905579747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72545749400867127874106329 54409312050650345905579747)
                ·
                  refine ⟨81613968075975518858369621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54409312050650345905579747 81613968075975518858369621)
                  ·
                    refine ⟨956413688390338111621519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81613968075975518858369621 956413688390338111621519)
                    ·
                      rfl

theorem cell23_5587827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_5587827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587827 prefixEnd_5587827 := by exact prefixLift 5587827
  have htrace : WordTrace (prefixWord ++ tailWord_5587827) baseStart_5587827 baseEnd_5587827 := by
    simpa [prefixWord, tailWord_5587827, baseEnd_5587827] using wordTrace_append hprefix tailTrace_5587827
  have hstable : (prefixWord ++ tailWord_5587827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587827).length < 2 ^ (prefixWord ++ tailWord_5587827).sum := by decide
  have hdescent : baseEnd_5587827 < baseStart_5587827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587884 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_5587884 : Nat := 118140960795 + 5587884 * 2 ^ 59
def prefixEnd_5587884 : Nat := 4983230072969 + 3 ^ 40 * 5587884 * 2
def baseEnd_5587884 : Nat := 2869270333568320611851795

theorem tailTrace_5587884 : CollatzResearch.WordTrace tailWord_5587884 prefixEnd_5587884 2869270333568320611851795 := by
  unfold tailWord_5587884
  simp only [CollatzResearch.WordTrace]
  refine ⟨101903436444029038726925353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135871248592038718302567137 101903436444029038726925353)
  ·
    refine ⟨76427577333021779045194015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101903436444029038726925353 76427577333021779045194015)
    ·
      refine ⟨114641365999532668567791023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76427577333021779045194015 114641365999532668567791023)
      ·
        refine ⟨171962048999299002851686535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114641365999532668567791023 171962048999299002851686535)
        ·
          refine ⟨257943073498948504277529803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171962048999299002851686535 257943073498948504277529803)
          ·
            refine ⟨386914610248422756416294705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257943073498948504277529803 386914610248422756416294705)
            ·
              refine ⟨290185957686317067312221029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386914610248422756416294705 290185957686317067312221029)
              ·
                refine ⟨54409867066184450121041443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290185957686317067312221029 54409867066184450121041443)
                ·
                  refine ⟨81614800599276675181562165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54409867066184450121041443 81614800599276675181562165)
                  ·
                    refine ⟨7651387556182188298271453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81614800599276675181562165 7651387556182188298271453)
                    ·
                      refine ⟨2869270333568320611851795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651387556182188298271453 2869270333568320611851795)
                      ·
                        rfl

theorem cell23_5587884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_5587884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587884 prefixEnd_5587884 := by exact prefixLift 5587884
  have htrace : WordTrace (prefixWord ++ tailWord_5587884) baseStart_5587884 baseEnd_5587884 := by
    simpa [prefixWord, tailWord_5587884, baseEnd_5587884] using wordTrace_append hprefix tailTrace_5587884
  have hstable : (prefixWord ++ tailWord_5587884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587884).length < 2 ^ (prefixWord ++ tailWord_5587884).sum := by decide
  have hdescent : baseEnd_5587884 < baseStart_5587884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587911 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_5587911 : Nat := 118140960795 + 5587911 * 2 ^ 59
def prefixEnd_5587911 : Nat := 4983230072969 + 3 ^ 40 * 5587911 * 2
def baseEnd_5587911 : Nat := 2869284197545992006214171

theorem tailTrace_5587911 : CollatzResearch.WordTrace tailWord_5587911 prefixEnd_5587911 2869284197545992006214171 := by
  unfold tailWord_5587911
  simp only [CollatzResearch.WordTrace]
  refine ⟨203807857658960261065083587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135871905105973507376722391 203807857658960261065083587)
  ·
    refine ⟨305711786488440391597625381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203807857658960261065083587 305711786488440391597625381)
    ·
      refine ⟨57320959966582573424554759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305711786488440391597625381 57320959966582573424554759)
      ·
        refine ⟨85981439949873860136832139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57320959966582573424554759 85981439949873860136832139)
        ·
          refine ⟨128972159924810790205248209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85981439949873860136832139 128972159924810790205248209)
          ·
            refine ⟨96729119943608092653936157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128972159924810790205248209 96729119943608092653936157)
            ·
              refine ⟨36273419978853034745226059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96729119943608092653936157 36273419978853034745226059)
              ·
                refine ⟨54410129968279552117839089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36273419978853034745226059 54410129968279552117839089)
                ·
                  refine ⟨40807597476209664088379317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54410129968279552117839089 40807597476209664088379317)
                  ·
                    refine ⟨3825712263394656008285561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40807597476209664088379317 3825712263394656008285561)
                    ·
                      refine ⟨2869284197545992006214171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825712263394656008285561 2869284197545992006214171)
                      ·
                        rfl

theorem cell23_5587911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_5587911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587911 prefixEnd_5587911 := by exact prefixLift 5587911
  have htrace : WordTrace (prefixWord ++ tailWord_5587911) baseStart_5587911 baseEnd_5587911 := by
    simpa [prefixWord, tailWord_5587911, baseEnd_5587911] using wordTrace_append hprefix tailTrace_5587911
  have hstable : (prefixWord ++ tailWord_5587911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587911).length < 2 ^ (prefixWord ++ tailWord_5587911).sum := by decide
  have hdescent : baseEnd_5587911 < baseStart_5587911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587938 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5587938 : Nat := 118140960795 + 5587938 * 2 ^ 59
def prefixEnd_5587938 : Nat := 4983230072969 + 3 ^ 40 * 5587938 * 2
def baseEnd_5587938 : Nat := 956432687174554466858849

theorem tailTrace_5587938 : CollatzResearch.WordTrace tailWord_5587938 prefixEnd_5587938 956432687174554466858849 := by
  unfold tailWord_5587938
  simp only [CollatzResearch.WordTrace]
  refine ⟨50952210607465611169079117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135872561619908296450877645 50952210607465611169079117)
  ·
    refine ⟨19107078977799604188404669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50952210607465611169079117 19107078977799604188404669)
    ·
      refine ⟨7165154616674851570651751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19107078977799604188404669 7165154616674851570651751)
      ·
        refine ⟨10747731925012277355977627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7165154616674851570651751 10747731925012277355977627)
        ·
          refine ⟨16121597887518416033966441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10747731925012277355977627 16121597887518416033966441)
          ·
            refine ⟨12091198415638812025474831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16121597887518416033966441 12091198415638812025474831)
            ·
              refine ⟨18136797623458218038212247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12091198415638812025474831 18136797623458218038212247)
              ·
                refine ⟨27205196435187327057318371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18136797623458218038212247 27205196435187327057318371)
                ·
                  refine ⟨40807794652780990585977557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27205196435187327057318371 40807794652780990585977557)
                  ·
                    refine ⟨956432687174554466858849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40807794652780990585977557 956432687174554466858849)
                    ·
                      rfl

theorem cell23_5587938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5587938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587938 prefixEnd_5587938 := by exact prefixLift 5587938
  have htrace : WordTrace (prefixWord ++ tailWord_5587938) baseStart_5587938 baseEnd_5587938 := by
    simpa [prefixWord, tailWord_5587938, baseEnd_5587938] using wordTrace_append hprefix tailTrace_5587938
  have hstable : (prefixWord ++ tailWord_5587938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587938).length < 2 ^ (prefixWord ++ tailWord_5587938).sum := by decide
  have hdescent : baseEnd_5587938 < baseStart_5587938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587961 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_5587961 : Nat := 118140960795 + 5587961 * 2 ^ 59
def prefixEnd_5587961 : Nat := 4983230072969 + 3 ^ 40 * 5587961 * 2
def baseEnd_5587961 : Nat := 2869309871578716810588941

theorem tailTrace_5587961 : CollatzResearch.WordTrace tailWord_5587961 prefixEnd_5587961 2869309871578716810588941 := by
  unfold tailWord_5587961
  simp only [CollatzResearch.WordTrace]
  refine ⟨203809681308779119604403737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135873120872519413069602491 203809681308779119604403737)
  ·
    refine ⟨152857260981584339703302803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203809681308779119604403737 152857260981584339703302803)
    ·
      refine ⟨229285891472376509554954205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152857260981584339703302803 229285891472376509554954205)
      ·
        refine ⟨85982209302141191083107827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229285891472376509554954205 85982209302141191083107827)
        ·
          refine ⟨128973313953211786624661741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85982209302141191083107827 128973313953211786624661741)
          ·
            refine ⟨48364992732454419984248153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128973313953211786624661741 48364992732454419984248153)
            ·
              refine ⟨36273744549340814988186115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48364992732454419984248153 36273744549340814988186115)
              ·
                refine ⟨54410616824011222482279173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36273744549340814988186115 54410616824011222482279173)
                ·
                  refine ⟨10201990654502104215427345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54410616824011222482279173 10201990654502104215427345)
                  ·
                    refine ⟨7651492990876578161570509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10201990654502104215427345 7651492990876578161570509)
                    ·
                      refine ⟨2869309871578716810588941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651492990876578161570509 2869309871578716810588941)
                      ·
                        rfl

theorem cell23_5587961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_5587961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587961 prefixEnd_5587961 := by exact prefixLift 5587961
  have htrace : WordTrace (prefixWord ++ tailWord_5587961) baseStart_5587961 baseEnd_5587961 := by
    simpa [prefixWord, tailWord_5587961, baseEnd_5587961] using wordTrace_append hprefix tailTrace_5587961
  have hstable : (prefixWord ++ tailWord_5587961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587961).length < 2 ^ (prefixWord ++ tailWord_5587961).sum := by decide
  have hdescent : baseEnd_5587961 < baseStart_5587961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588002 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_5588002 : Nat := 118140960795 + 5588002 * 2 ^ 59
def prefixEnd_5588002 : Nat := 4983230072969 + 3 ^ 40 * 5588002 * 2
def baseEnd_5588002 : Nat := 956443641428517050058751

theorem tailTrace_5588002 : CollatzResearch.WordTrace tailWord_5588002 prefixEnd_5588002 956443641428517050058751 := by
  unfold tailWord_5588002
  simp only [CollatzResearch.WordTrace]
  refine ⟨50952794175407645901661565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135874117801087055737764173 50952794175407645901661565)
  ·
    refine ⟨19107297815777867213123087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50952794175407645901661565 19107297815777867213123087)
    ·
      refine ⟨28660946723666800819684631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19107297815777867213123087 28660946723666800819684631)
      ·
        refine ⟨42991420085500201229526947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28660946723666800819684631 42991420085500201229526947)
        ·
          refine ⟨64487130128250301844290421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42991420085500201229526947 64487130128250301844290421)
          ·
            refine ⟨6045668449523465797902227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64487130128250301844290421 6045668449523465797902227)
            ·
              refine ⟨9068502674285198696853341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045668449523465797902227 9068502674285198696853341)
              ·
                refine ⟨3400688502856949511320003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9068502674285198696853341 3400688502856949511320003)
                ·
                  refine ⟨5101032754285424266980005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400688502856949511320003 5101032754285424266980005)
                  ·
                    refine ⟨956443641428517050058751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5101032754285424266980005 956443641428517050058751)
                    ·
                      rfl

theorem cell23_5588002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_5588002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588002 prefixEnd_5588002 := by exact prefixLift 5588002
  have htrace : WordTrace (prefixWord ++ tailWord_5588002) baseStart_5588002 baseEnd_5588002 := by
    simpa [prefixWord, tailWord_5588002, baseEnd_5588002] using wordTrace_append hprefix tailTrace_5588002
  have hstable : (prefixWord ++ tailWord_5588002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588002).length < 2 ^ (prefixWord ++ tailWord_5588002).sum := by decide
  have hdescent : baseEnd_5588002 < baseStart_5588002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588011 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 1, 5]
def baseStart_5588011 : Nat := 118140960795 + 5588011 * 2 ^ 59
def prefixEnd_5588011 : Nat := 4983230072969 + 3 ^ 40 * 5588011 * 2
def baseEnd_5588011 : Nat := 956445181870480538321237

theorem tailTrace_5588011 : CollatzResearch.WordTrace tailWord_5588011 prefixEnd_5588011 956445181870480538321237 := by
  unfold tailWord_5588011
  simp only [CollatzResearch.WordTrace]
  refine ⟨203811504958597978143723887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135874336639065318762482591 203811504958597978143723887)
  ·
    refine ⟨305717257437896967215585831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203811504958597978143723887 305717257437896967215585831)
    ·
      refine ⟨458575886156845450823378747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305717257437896967215585831 458575886156845450823378747)
      ·
        refine ⟨687863829235268176235068121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458575886156845450823378747 687863829235268176235068121)
        ·
          refine ⟨515897871926451132176301091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687863829235268176235068121 515897871926451132176301091)
          ·
            refine ⟨773846807889676698264451637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515897871926451132176301091 773846807889676698264451637)
            ·
              refine ⟨72548138239657190462292341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 773846807889676698264451637 72548138239657190462292341)
              ·
                refine ⟨6801387959967861605839907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72548138239657190462292341 6801387959967861605839907)
                ·
                  refine ⟨10202081939951792408759861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6801387959967861605839907 10202081939951792408759861)
                  ·
                    refine ⟨956445181870480538321237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10202081939951792408759861 956445181870480538321237)
                    ·
                      rfl

theorem cell23_5588011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 5].length) (baseStart_5588011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588011 prefixEnd_5588011 := by exact prefixLift 5588011
  have htrace : WordTrace (prefixWord ++ tailWord_5588011) baseStart_5588011 baseEnd_5588011 := by
    simpa [prefixWord, tailWord_5588011, baseEnd_5588011] using wordTrace_append hprefix tailTrace_5588011
  have hstable : (prefixWord ++ tailWord_5588011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588011).length < 2 ^ (prefixWord ++ tailWord_5588011).sum := by decide
  have hdescent : baseEnd_5588011 < baseStart_5588011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588025 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5588025 : Nat := 118140960795 + 5588025 * 2 ^ 59
def prefixEnd_5588025 : Nat := 4983230072969 + 3 ^ 40 * 5588025 * 2
def baseEnd_5588025 : Nat := 2869342734340604560188647

theorem tailTrace_5588025 : CollatzResearch.WordTrace tailWord_5588025 prefixEnd_5588025 2869342734340604560188647 := by
  unfold tailWord_5588025
  simp only [CollatzResearch.WordTrace]
  refine ⟨203812015580547258534733529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135874677053698172356489019 203812015580547258534733529)
  ·
    refine ⟨152859011685410443901050147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203812015580547258534733529 152859011685410443901050147)
    ·
      refine ⟨229288517528115665851575221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152859011685410443901050147 229288517528115665851575221)
      ·
        refine ⟨21495798518260843673585177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229288517528115665851575221 21495798518260843673585177)
        ·
          refine ⟨16121848888695632755188883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21495798518260843673585177 16121848888695632755188883)
          ·
            refine ⟨24182773333043449132783325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16121848888695632755188883 24182773333043449132783325)
            ·
              refine ⟨9068539999891293424793747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24182773333043449132783325 9068539999891293424793747)
              ·
                refine ⟨13602809999836940137190621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9068539999891293424793747 13602809999836940137190621)
                ·
                  refine ⟨5101053749938852551446483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13602809999836940137190621 5101053749938852551446483)
                  ·
                    refine ⟨7651580624908278827169725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101053749938852551446483 7651580624908278827169725)
                    ·
                      refine ⟨2869342734340604560188647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651580624908278827169725 2869342734340604560188647)
                      ·
                        rfl

theorem cell23_5588025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5588025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588025 prefixEnd_5588025 := by exact prefixLift 5588025
  have htrace : WordTrace (prefixWord ++ tailWord_5588025) baseStart_5588025 baseEnd_5588025 := by
    simpa [prefixWord, tailWord_5588025, baseEnd_5588025] using wordTrace_append hprefix tailTrace_5588025
  have hstable : (prefixWord ++ tailWord_5588025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588025).length < 2 ^ (prefixWord ++ tailWord_5588025).sum := by decide
  have hdescent : baseEnd_5588025 < baseStart_5588025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588031 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_5588031 : Nat := 118140960795 + 5588031 * 2 ^ 59
def prefixEnd_5588031 : Nat := 4983230072969 + 3 ^ 40 * 5588031 * 2
def baseEnd_5588031 : Nat := 2869345815224531536713619

theorem tailTrace_5588031 : CollatzResearch.WordTrace tailWord_5588031 prefixEnd_5588031 2869345815224531536713619 := by
  unfold tailWord_5588031
  simp only [CollatzResearch.WordTrace]
  refine ⟨203812234418525521559451947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135874822945683681039634631 203812234418525521559451947)
  ·
    refine ⟨305718351627788282339177921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203812234418525521559451947 305718351627788282339177921)
    ·
      refine ⟨229288763720841211754383441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305718351627788282339177921 229288763720841211754383441)
      ·
        refine ⟨171966572790630908815787581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229288763720841211754383441 171966572790630908815787581)
        ·
          refine ⟨64487464796486590805920343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171966572790630908815787581 64487464796486590805920343)
          ·
            refine ⟨96731197194729886208880515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64487464796486590805920343 96731197194729886208880515)
            ·
              refine ⟨145096795792094829313320773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96731197194729886208880515 145096795792094829313320773)
              ·
                refine ⟨27205649211017780496247645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145096795792094829313320773 27205649211017780496247645)
                ·
                  refine ⟨10202118454131667686092867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27205649211017780496247645 10202118454131667686092867)
                  ·
                    refine ⟨15303177681197501529139301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10202118454131667686092867 15303177681197501529139301)
                    ·
                      refine ⟨2869345815224531536713619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15303177681197501529139301 2869345815224531536713619)
                      ·
                        rfl

theorem cell23_5588031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_5588031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588031 prefixEnd_5588031 := by exact prefixLift 5588031
  have htrace : WordTrace (prefixWord ++ tailWord_5588031) baseStart_5588031 baseEnd_5588031 := by
    simpa [prefixWord, tailWord_5588031, baseEnd_5588031] using wordTrace_append hprefix tailTrace_5588031
  have hstable : (prefixWord ++ tailWord_5588031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588031).length < 2 ^ (prefixWord ++ tailWord_5588031).sum := by decide
  have hdescent : baseEnd_5588031 < baseStart_5588031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588041 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 6, 4]
def baseStart_5588041 : Nat := 118140960795 + 5588041 * 2 ^ 59
def prefixEnd_5588041 : Nat := 4983230072969 + 3 ^ 40 * 5588041 * 2
def baseEnd_5588041 : Nat := 956450316677025499196191

theorem tailTrace_5588041 : CollatzResearch.WordTrace tailWord_5588041 prefixEnd_5588041 956450316677025499196191 := by
  unfold tailWord_5588041
  simp only [CollatzResearch.WordTrace]
  refine ⟨203812599148489293267315977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135875066098992862178210651 203812599148489293267315977)
  ·
    refine ⟨152859449361366969950486983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203812599148489293267315977 152859449361366969950486983)
    ·
      refine ⟨229289174042050454925730475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152859449361366969950486983 229289174042050454925730475)
      ·
        refine ⟨343933761063075682388595713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229289174042050454925730475 343933761063075682388595713)
        ·
          refine ⟨257950320797306761791446785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343933761063075682388595713 257950320797306761791446785)
          ·
            refine ⟨193462740597980071343585089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257950320797306761791446785 193462740597980071343585089)
            ·
              refine ⟨145097055448485053507688817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193462740597980071343585089 145097055448485053507688817)
              ·
                refine ⟨108822791586363790130766613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145097055448485053507688817 108822791586363790130766613)
                ·
                  refine ⟨5101068355610802662379685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108822791586363790130766613 5101068355610802662379685)
                  ·
                    refine ⟨956450316677025499196191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5101068355610802662379685 956450316677025499196191)
                    ·
                      rfl

theorem cell23_5588041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_5588041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588041 prefixEnd_5588041 := by exact prefixLift 5588041
  have htrace : WordTrace (prefixWord ++ tailWord_5588041) baseStart_5588041 baseEnd_5588041 := by
    simpa [prefixWord, tailWord_5588041, baseEnd_5588041] using wordTrace_append hprefix tailTrace_5588041
  have hstable : (prefixWord ++ tailWord_5588041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588041).length < 2 ^ (prefixWord ++ tailWord_5588041).sum := by decide
  have hdescent : baseEnd_5588041 < baseStart_5588041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588045 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_5588045 : Nat := 118140960795 + 5588045 * 2 ^ 59
def prefixEnd_5588045 : Nat := 4983230072969 + 3 ^ 40 * 5588045 * 2
def baseEnd_5588045 : Nat := 956451001317898160646185

theorem tailTrace_5588045 : CollatzResearch.WordTrace tailWord_5588045 prefixEnd_5588045 956451001317898160646185 := by
  unfold tailWord_5588045
  simp only [CollatzResearch.WordTrace]
  refine ⟨203812745040474801950461589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135875163360316534633641059 203812745040474801950461589)
  ·
    refine ⟨9553722423772256341427887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203812745040474801950461589 9553722423772256341427887)
    ·
      refine ⟨14330583635658384512141831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9553722423772256341427887 14330583635658384512141831)
      ·
        refine ⟨21495875453487576768212747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14330583635658384512141831 21495875453487576768212747)
        ·
          refine ⟨32243813180231365152319121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21495875453487576768212747 32243813180231365152319121)
          ·
            refine ⟨24182859885173523864239341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32243813180231365152319121 24182859885173523864239341)
            ·
              refine ⟨9068572456940071449089753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24182859885173523864239341 9068572456940071449089753)
              ·
                refine ⟨6801429342705053586817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9068572456940071449089753 6801429342705053586817315)
                ·
                  refine ⟨10202144014057580380225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6801429342705053586817315 10202144014057580380225973)
                  ·
                    refine ⟨956451001317898160646185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10202144014057580380225973 956451001317898160646185)
                    ·
                      rfl

theorem cell23_5588045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_5588045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588045 prefixEnd_5588045 := by exact prefixLift 5588045
  have htrace : WordTrace (prefixWord ++ tailWord_5588045) baseStart_5588045 baseEnd_5588045 := by
    simpa [prefixWord, tailWord_5588045, baseEnd_5588045] using wordTrace_append hprefix tailTrace_5588045
  have hstable : (prefixWord ++ tailWord_5588045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588045).length < 2 ^ (prefixWord ++ tailWord_5588045).sum := by decide
  have hdescent : baseEnd_5588045 < baseStart_5588045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588132 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_5588132 : Nat := 118140960795 + 5588132 * 2 ^ 59
def prefixEnd_5588132 : Nat := 4983230072969 + 3 ^ 40 * 5588132 * 2
def baseEnd_5588132 : Nat := 2869397676770635641550655

theorem tailTrace_5588132 : CollatzResearch.WordTrace tailWord_5588132 prefixEnd_5588132 2869397676770635641550655 := by
  unfold tailWord_5588132
  simp only [CollatzResearch.WordTrace]
  refine ⟨101907959095579807904439325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135877278794106410539252433 101907959095579807904439325)
  ·
    refine ⟨38215484660842427964164747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101907959095579807904439325 38215484660842427964164747)
    ·
      refine ⟨57323226991263641946247121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38215484660842427964164747 57323226991263641946247121)
      ·
        refine ⟨42992420243447731459685341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57323226991263641946247121 42992420243447731459685341)
        ·
          refine ⟨16122157591292899297382003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42992420243447731459685341 16122157591292899297382003)
          ·
            refine ⟨24183236386939348946073005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16122157591292899297382003 24183236386939348946073005)
            ·
              refine ⟨9068713645102255854777377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24183236386939348946073005 9068713645102255854777377)
              ·
                refine ⟨6801535233826691891083033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9068713645102255854777377 6801535233826691891083033)
                ·
                  refine ⟨5101151425370018918312275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6801535233826691891083033 5101151425370018918312275)
                  ·
                    refine ⟨7651727138055028377468413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101151425370018918312275 7651727138055028377468413)
                    ·
                      refine ⟨2869397676770635641550655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651727138055028377468413 2869397676770635641550655)
                      ·
                        rfl

theorem cell23_5588132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_5588132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588132 prefixEnd_5588132 := by exact prefixLift 5588132
  have htrace : WordTrace (prefixWord ++ tailWord_5588132) baseStart_5588132 baseEnd_5588132 := by
    simpa [prefixWord, tailWord_5588132, baseEnd_5588132] using wordTrace_append hprefix tailTrace_5588132
  have hstable : (prefixWord ++ tailWord_5588132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588132).length < 2 ^ (prefixWord ++ tailWord_5588132).sum := by decide
  have hdescent : baseEnd_5588132 < baseStart_5588132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588225 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 2, 5]
def baseStart_5588225 : Nat := 118140960795 + 5588225 * 2 ^ 59
def prefixEnd_5588225 : Nat := 4983230072969 + 3 ^ 40 * 5588225 * 2
def baseEnd_5588225 : Nat := 956481810157167925895909

theorem tailTrace_5588225 : CollatzResearch.WordTrace tailWord_5588225 prefixEnd_5588225 956481810157167925895909 := by
  unfold tailWord_5588225
  simp only [CollatzResearch.WordTrace]
  refine ⟨203819310179822692692014129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135879540119881795128009419 203819310179822692692014129)
  ·
    refine ⟨152864482634867019519010597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203819310179822692692014129 152864482634867019519010597)
    ·
      refine ⟨28662090494037566159814487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152864482634867019519010597 28662090494037566159814487)
      ·
        refine ⟨42993135741056349239721731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28662090494037566159814487 42993135741056349239721731)
        ·
          refine ⟨64489703611584523859582597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42993135741056349239721731 64489703611584523859582597)
          ·
            refine ⟨12091819427172098223671737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64489703611584523859582597 12091819427172098223671737)
            ·
              refine ⟨9068864570379073667753803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12091819427172098223671737 9068864570379073667753803)
              ·
                refine ⟨13603296855568610501630705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9068864570379073667753803 13603296855568610501630705)
                ·
                  refine ⟨10202472641676457876223029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13603296855568610501630705 10202472641676457876223029)
                  ·
                    refine ⟨956481810157167925895909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10202472641676457876223029 956481810157167925895909)
                    ·
                      rfl

theorem cell23_5588225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_5588225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588225 prefixEnd_5588225 := by exact prefixLift 5588225
  have htrace : WordTrace (prefixWord ++ tailWord_5588225) baseStart_5588225 baseEnd_5588225 := by
    simpa [prefixWord, tailWord_5588225, baseEnd_5588225] using wordTrace_append hprefix tailTrace_5588225
  have hstable : (prefixWord ++ tailWord_5588225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588225).length < 2 ^ (prefixWord ++ tailWord_5588225).sum := by decide
  have hdescent : baseEnd_5588225 < baseStart_5588225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588245 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_5588245 : Nat := 118140960795 + 5588245 * 2 ^ 59
def prefixEnd_5588245 : Nat := 4983230072969 + 3 ^ 40 * 5588245 * 2
def baseEnd_5588245 : Nat := 2869455700084593699437635

theorem tailTrace_5588245 : CollatzResearch.WordTrace tailWord_5588245 prefixEnd_5588245 2869455700084593699437635 := by
  unfold tailWord_5588245
  simp only [CollatzResearch.WordTrace]
  refine ⟨203820039639750236107742189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135880026426500157405161459 203820039639750236107742189)
  ·
    refine ⟨76432514864906338540403321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203820039639750236107742189 76432514864906338540403321)
    ·
      refine ⟨57324386148679753905302491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76432514864906338540403321 57324386148679753905302491)
      ·
        refine ⟨85986579223019630857953737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57324386148679753905302491 85986579223019630857953737)
        ·
          refine ⟨64489934417264723143465303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85986579223019630857953737 64489934417264723143465303)
          ·
            refine ⟨96734901625897084715197955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64489934417264723143465303 96734901625897084715197955)
            ·
              refine ⟨145102352438845627072796933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96734901625897084715197955 145102352438845627072796933)
              ·
                refine ⟨27206691082283555076149425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145102352438845627072796933 27206691082283555076149425)
                ·
                  refine ⟨20405018311712666307112069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27206691082283555076149425 20405018311712666307112069)
                  ·
                    refine ⟨3825940933446124932583513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20405018311712666307112069 3825940933446124932583513)
                    ·
                      refine ⟨2869455700084593699437635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825940933446124932583513 2869455700084593699437635)
                      ·
                        rfl

theorem cell23_5588245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_5588245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588245 prefixEnd_5588245 := by exact prefixLift 5588245
  have htrace : WordTrace (prefixWord ++ tailWord_5588245) baseStart_5588245 baseEnd_5588245 := by
    simpa [prefixWord, tailWord_5588245, baseEnd_5588245] using wordTrace_append hprefix tailTrace_5588245
  have hstable : (prefixWord ++ tailWord_5588245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588245).length < 2 ^ (prefixWord ++ tailWord_5588245).sum := by decide
  have hdescent : baseEnd_5588245 < baseStart_5588245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588289 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5588289 : Nat := 118140960795 + 5588289 * 2 ^ 59
def prefixEnd_5588289 : Nat := 4983230072969 + 3 ^ 40 * 5588289 * 2
def baseEnd_5588289 : Nat := 956492764411130509095811

theorem tailTrace_5588289 : CollatzResearch.WordTrace tailWord_5588289 prefixEnd_5588289 956492764411130509095811 := by
  unfold tailWord_5588289
  simp only [CollatzResearch.WordTrace]
  refine ⟨203821644451590831622343921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135881096301060554414895947 203821644451590831622343921)
  ·
    refine ⟨152866233338693123716757941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203821644451590831622343921 152866233338693123716757941)
    ·
      refine ⟨14331209375502480348446057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152866233338693123716757941 14331209375502480348446057)
      ·
        refine ⟨10748407031626860261334543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14331209375502480348446057 10748407031626860261334543)
        ·
          refine ⟨16122610547440290392001815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10748407031626860261334543 16122610547440290392001815)
          ·
            refine ⟨24183915821160435588002723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16122610547440290392001815 24183915821160435588002723)
            ·
              refine ⟨36275873731740653382004085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24183915821160435588002723 36275873731740653382004085)
              ·
                refine ⟨3400863162350686254562883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36275873731740653382004085 3400863162350686254562883)
                ·
                  refine ⟨5101294743526029381844325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400863162350686254562883 5101294743526029381844325)
                  ·
                    refine ⟨956492764411130509095811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5101294743526029381844325 956492764411130509095811)
                    ·
                      rfl

theorem cell23_5588289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5588289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588289 prefixEnd_5588289 := by exact prefixLift 5588289
  have htrace : WordTrace (prefixWord ++ tailWord_5588289) baseStart_5588289 baseEnd_5588289 := by
    simpa [prefixWord, tailWord_5588289, baseEnd_5588289] using wordTrace_append hprefix tailTrace_5588289
  have hstable : (prefixWord ++ tailWord_5588289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588289).length < 2 ^ (prefixWord ++ tailWord_5588289).sum := by decide
  have hdescent : baseEnd_5588289 < baseStart_5588289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588312 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_5588312 : Nat := 118140960795 + 5588312 * 2 ^ 59
def prefixEnd_5588312 : Nat := 4983230072969 + 3 ^ 40 * 5588312 * 2
def baseEnd_5588312 : Nat := 2869490103288444937299827

theorem tailTrace_5588312 : CollatzResearch.WordTrace tailWord_5588312 prefixEnd_5588312 2869490103288444937299827 := by
  unfold tailWord_5588312
  simp only [CollatzResearch.WordTrace]
  refine ⟨101911241665253753275215595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135881655553671671033620793 101911241665253753275215595)
  ·
    refine ⟨152866862497880629912823393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101911241665253753275215595 152866862497880629912823393)
    ·
      refine ⟨114650146873410472434617545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152866862497880629912823393 114650146873410472434617545)
      ·
        refine ⟨85987610155057854325963159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114650146873410472434617545 85987610155057854325963159)
        ·
          refine ⟨128981415232586781488944739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85987610155057854325963159 128981415232586781488944739)
          ·
            refine ⟨193472122848880172233417109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128981415232586781488944739 193472122848880172233417109)
            ·
              refine ⟨9069005758541258073441427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193472122848880172233417109 9069005758541258073441427)
              ·
                refine ⟨13603508637811887110162141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9069005758541258073441427 13603508637811887110162141)
                ·
                  refine ⟨5101315739179457666310803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13603508637811887110162141 5101315739179457666310803)
                  ·
                    refine ⟨7651973608769186499466205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101315739179457666310803 7651973608769186499466205)
                    ·
                      refine ⟨2869490103288444937299827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651973608769186499466205 2869490103288444937299827)
                      ·
                        rfl

theorem cell23_5588312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_5588312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588312 prefixEnd_5588312 := by exact prefixLift 5588312
  have htrace : WordTrace (prefixWord ++ tailWord_5588312) baseStart_5588312 baseEnd_5588312 := by
    simpa [prefixWord, tailWord_5588312, baseEnd_5588312] using wordTrace_append hprefix tailTrace_5588312
  have hstable : (prefixWord ++ tailWord_5588312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588312).length < 2 ^ (prefixWord ++ tailWord_5588312).sum := by decide
  have hdescent : baseEnd_5588312 < baseStart_5588312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588322 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_5588322 : Nat := 118140960795 + 5588322 * 2 ^ 59
def prefixEnd_5588322 : Nat := 4983230072969 + 3 ^ 40 * 5588322 * 2
def baseEnd_5588322 : Nat := 2869495238094989898174781

theorem tailTrace_5588322 : CollatzResearch.WordTrace tailWord_5588322 prefixEnd_5588322 2869495238094989898174781 := by
  unfold tailWord_5588322
  simp only [CollatzResearch.WordTrace]
  refine ⟨50955712015117819564573805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135881898706980852172196813 50955712015117819564573805)
  ·
    refine ⟨19108392005669182336715177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50955712015117819564573805 19108392005669182336715177)
    ·
      refine ⟨14331294004251886752536383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19108392005669182336715177 14331294004251886752536383)
      ·
        refine ⟨21496941006377830128804575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331294004251886752536383 21496941006377830128804575)
        ·
          refine ⟨32245411509566745193206863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21496941006377830128804575 32245411509566745193206863)
          ·
            refine ⟨48368117264350117789810295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32245411509566745193206863 48368117264350117789810295)
            ·
              refine ⟨72552175896525176684715443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48368117264350117789810295 72552175896525176684715443)
              ·
                refine ⟨108828263844787765027073165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72552175896525176684715443 108828263844787765027073165)
                ·
                  refine ⟨40810598941795411885152437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108828263844787765027073165 40810598941795411885152437)
                  ·
                    refine ⟨3825993650793319864233041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40810598941795411885152437 3825993650793319864233041)
                    ·
                      refine ⟨2869495238094989898174781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825993650793319864233041 2869495238094989898174781)
                      ·
                        rfl

theorem cell23_5588322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_5588322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588322 prefixEnd_5588322 := by exact prefixLift 5588322
  have htrace : WordTrace (prefixWord ++ tailWord_5588322) baseStart_5588322 baseEnd_5588322 := by
    simpa [prefixWord, tailWord_5588322, baseEnd_5588322] using wordTrace_append hprefix tailTrace_5588322
  have hstable : (prefixWord ++ tailWord_5588322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588322).length < 2 ^ (prefixWord ++ tailWord_5588322).sum := by decide
  have hdescent : baseEnd_5588322 < baseStart_5588322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588332 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_5588332 : Nat := 118140960795 + 5588332 * 2 ^ 59
def prefixEnd_5588332 : Nat := 4983230072969 + 3 ^ 40 * 5588332 * 2
def baseEnd_5588332 : Nat := 956500124300511619683245

theorem tailTrace_5588332 : CollatzResearch.WordTrace tailWord_5588332 prefixEnd_5588332 956500124300511619683245 := by
  unfold tailWord_5588332
  simp only [CollatzResearch.WordTrace]
  refine ⟨101911606395217524983079625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135882141860290033310772833 101911606395217524983079625)
  ·
    refine ⟨76433704796413143737309719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101911606395217524983079625 76433704796413143737309719)
    ·
      refine ⟨114650557194619715605964579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76433704796413143737309719 114650557194619715605964579)
      ·
        refine ⟨171975835791929573408946869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114650557194619715605964579 171975835791929573408946869)
        ·
          refine ⟨16122734605493397507088769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171975835791929573408946869 16122734605493397507088769)
          ·
            refine ⟨12092050954120048130316577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16122734605493397507088769 12092050954120048130316577)
            ·
              refine ⟨9069038215590036097737433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12092050954120048130316577 9069038215590036097737433)
              ·
                refine ⟨6801778661692527073303075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9069038215590036097737433 6801778661692527073303075)
                ·
                  refine ⟨10202667992538790609954613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6801778661692527073303075 10202667992538790609954613)
                  ·
                    refine ⟨956500124300511619683245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10202667992538790609954613 956500124300511619683245)
                    ·
                      rfl

theorem cell23_5588332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_5588332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588332 prefixEnd_5588332 := by exact prefixLift 5588332
  have htrace : WordTrace (prefixWord ++ tailWord_5588332) baseStart_5588332 baseEnd_5588332 := by
    simpa [prefixWord, tailWord_5588332, baseEnd_5588332] using wordTrace_append hprefix tailTrace_5588332
  have hstable : (prefixWord ++ tailWord_5588332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588332).length < 2 ^ (prefixWord ++ tailWord_5588332).sum := by decide
  have hdescent : baseEnd_5588332 < baseStart_5588332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588335 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 6, 2]
def baseStart_5588335 : Nat := 118140960795 + 5588335 * 2 ^ 59
def prefixEnd_5588335 : Nat := 4983230072969 + 3 ^ 40 * 5588335 * 2
def baseEnd_5588335 : Nat := 2869501913343498347312221

theorem tailTrace_5588335 : CollatzResearch.WordTrace tailWord_5588335 prefixEnd_5588335 2869501913343498347312221 := by
  unfold tailWord_5588335
  simp only [CollatzResearch.WordTrace]
  refine ⟨203823322209424181478518459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135882214806282787652345639 203823322209424181478518459)
  ·
    refine ⟨305734983314136272217777689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203823322209424181478518459 305734983314136272217777689)
    ·
      refine ⟨229301237485602204163333267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305734983314136272217777689 229301237485602204163333267)
      ·
        refine ⟨343951856228403306244999901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229301237485602204163333267 343951856228403306244999901)
        ·
          refine ⟨128981946085651239841874963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343951856228403306244999901 128981946085651239841874963)
          ·
            refine ⟨193472919128476859762812445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128981946085651239841874963 193472919128476859762812445)
            ·
              refine ⟨72552344673178822411054667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193472919128476859762812445 72552344673178822411054667)
              ·
                refine ⟨108828517009768233616582001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72552344673178822411054667 108828517009768233616582001)
                ·
                  refine ⟨81621387757326175212436501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108828517009768233616582001 81621387757326175212436501)
                  ·
                    refine ⟨3826002551124664463082961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81621387757326175212436501 3826002551124664463082961)
                    ·
                      refine ⟨2869501913343498347312221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826002551124664463082961 2869501913343498347312221)
                      ·
                        rfl

theorem cell23_5588335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6, 2].length) (baseStart_5588335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588335 prefixEnd_5588335 := by exact prefixLift 5588335
  have htrace : WordTrace (prefixWord ++ tailWord_5588335) baseStart_5588335 baseEnd_5588335 := by
    simpa [prefixWord, tailWord_5588335, baseEnd_5588335] using wordTrace_append hprefix tailTrace_5588335
  have hstable : (prefixWord ++ tailWord_5588335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588335).length < 2 ^ (prefixWord ++ tailWord_5588335).sum := by decide
  have hdescent : baseEnd_5588335 < baseStart_5588335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588345 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 4, 4]
def baseStart_5588345 : Nat := 118140960795 + 5588345 * 2 ^ 59
def prefixEnd_5588345 : Nat := 4983230072969 + 3 ^ 40 * 5588345 * 2
def baseEnd_5588345 : Nat := 956502349383347769395725

theorem tailTrace_5588345 : CollatzResearch.WordTrace tailWord_5588345 prefixEnd_5588345 956502349383347769395725 := by
  unfold tailWord_5588345
  simp only [CollatzResearch.WordTrace]
  refine ⟨203823686939387953186382489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135882457959591968790921659 203823686939387953186382489)
  ·
    refine ⟨152867765204540964889786867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203823686939387953186382489 152867765204540964889786867)
    ·
      refine ⟨229301647806811447334680301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152867765204540964889786867 229301647806811447334680301)
      ·
        refine ⟨85988117927554292750505113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229301647806811447334680301 85988117927554292750505113)
        ·
          refine ⟨64491088445665719562878835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85988117927554292750505113 64491088445665719562878835)
          ·
            refine ⟨96736632668498579344318253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64491088445665719562878835 96736632668498579344318253)
            ·
              refine ⟨36276237250686967254119345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96736632668498579344318253 36276237250686967254119345)
              ·
                refine ⟨27207177938015225440589509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36276237250686967254119345 27207177938015225440589509)
                ·
                  refine ⟨5101345863377854770110533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27207177938015225440589509 5101345863377854770110533)
                  ·
                    refine ⟨956502349383347769395725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5101345863377854770110533 956502349383347769395725)
                    ·
                      rfl

theorem cell23_5588345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_5588345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588345 prefixEnd_5588345 := by exact prefixLift 5588345
  have htrace : WordTrace (prefixWord ++ tailWord_5588345) baseStart_5588345 baseEnd_5588345 := by
    simpa [prefixWord, tailWord_5588345, baseEnd_5588345] using wordTrace_append hprefix tailTrace_5588345
  have hstable : (prefixWord ++ tailWord_5588345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588345).length < 2 ^ (prefixWord ++ tailWord_5588345).sum := by decide
  have hdescent : baseEnd_5588345 < baseStart_5588345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588352 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 5, 2, 2]
def baseStart_5588352 : Nat := 118140960795 + 5588352 * 2 ^ 59
def prefixEnd_5588352 : Nat := 4983230072969 + 3 ^ 40 * 5588352 * 2
def baseEnd_5588352 : Nat := 2869510642514624780799643

theorem tailTrace_5588352 : CollatzResearch.WordTrace tailWord_5588352 prefixEnd_5588352 2869510642514624780799643 := by
  unfold tailWord_5588352
  simp only [CollatzResearch.WordTrace]
  refine ⟨101911971125181296690943655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135882628166908395587924873 101911971125181296690943655)
  ·
    refine ⟨152867956687771945036415483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101911971125181296690943655 152867956687771945036415483)
    ·
      refine ⟨229301935031657917554623225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152867956687771945036415483 229301935031657917554623225)
      ·
        refine ⟨171976451273743438165967419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229301935031657917554623225 171976451273743438165967419)
        ·
          refine ⟨257964676910615157248951129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171976451273743438165967419 257964676910615157248951129)
          ·
            refine ⟨193473507682961367936713347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257964676910615157248951129 193473507682961367936713347)
            ·
              refine ⟨290210261524442051905070021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193473507682961367936713347 290210261524442051905070021)
              ·
                refine ⟨54414424035832884732200629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290210261524442051905070021 54414424035832884732200629)
                ·
                  refine ⟨5101352253359332943643809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54414424035832884732200629 5101352253359332943643809)
                  ·
                    refine ⟨3826014190019499707732857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5101352253359332943643809 3826014190019499707732857)
                    ·
                      refine ⟨2869510642514624780799643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826014190019499707732857 2869510642514624780799643)
                      ·
                        rfl

theorem cell23_5588352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_5588352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588352 prefixEnd_5588352 := by exact prefixLift 5588352
  have htrace : WordTrace (prefixWord ++ tailWord_5588352) baseStart_5588352 baseEnd_5588352 := by
    simpa [prefixWord, tailWord_5588352, baseEnd_5588352] using wordTrace_append hprefix tailTrace_5588352
  have hstable : (prefixWord ++ tailWord_5588352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588352).length < 2 ^ (prefixWord ++ tailWord_5588352).sum := by decide
  have hdescent : baseEnd_5588352 < baseStart_5588352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588355 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5]
def baseStart_5588355 : Nat := 118140960795 + 5588355 * 2 ^ 59
def prefixEnd_5588355 : Nat := 4983230072969 + 3 ^ 40 * 5588355 * 2
def baseEnd_5588355 : Nat := 2869512182956588269062129

theorem tailTrace_5588355 : CollatzResearch.WordTrace tailWord_5588355 prefixEnd_5588355 2869512182956588269062129 := by
  unfold tailWord_5588355
  simp only [CollatzResearch.WordTrace]
  refine ⟨203824051669351724894246519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135882701112901149929497679 203824051669351724894246519)
  ·
    refine ⟨305736077504027587341369779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203824051669351724894246519 305736077504027587341369779)
    ·
      refine ⟨458604116256041381012054669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305736077504027587341369779 458604116256041381012054669)
      ·
        refine ⟨171976543596015517879520501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458604116256041381012054669 171976543596015517879520501)
        ·
          refine ⟨16122800962126454801205047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171976543596015517879520501 16122800962126454801205047)
          ·
            refine ⟨24184201443189682201807571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16122800962126454801205047 24184201443189682201807571)
            ·
              refine ⟨36276302164784523302711357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24184201443189682201807571 36276302164784523302711357)
              ·
                refine ⟨13603613311794196238516759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36276302164784523302711357 13603613311794196238516759)
                ·
                  refine ⟨20405419967691294357775139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13603613311794196238516759 20405419967691294357775139)
                  ·
                    refine ⟨30608129951536941536662709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20405419967691294357775139 30608129951536941536662709)
                    ·
                      refine ⟨2869512182956588269062129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30608129951536941536662709 2869512182956588269062129)
                      ·
                        rfl

theorem cell23_5588355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_5588355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588355 prefixEnd_5588355 := by exact prefixLift 5588355
  have htrace : WordTrace (prefixWord ++ tailWord_5588355) baseStart_5588355 baseEnd_5588355 := by
    simpa [prefixWord, tailWord_5588355, baseEnd_5588355] using wordTrace_append hprefix tailTrace_5588355
  have hstable : (prefixWord ++ tailWord_5588355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588355).length < 2 ^ (prefixWord ++ tailWord_5588355).sum := by decide
  have hdescent : baseEnd_5588355 < baseStart_5588355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588372 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5588372 : Nat := 118140960795 + 5588372 * 2 ^ 59
def prefixEnd_5588372 : Nat := 4983230072969 + 3 ^ 40 * 5588372 * 2
def baseEnd_5588372 : Nat := 2869520912127714702549551

theorem tailTrace_5588372 : CollatzResearch.WordTrace tailWord_5588372 prefixEnd_5588372 2869520912127714702549551 := by
  unfold tailWord_5588372
  simp only [CollatzResearch.WordTrace]
  refine ⟨101912335855145068398807685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135883114473526757865076913 101912335855145068398807685)
  ·
    refine ⟨19108562972839700324776441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101912335855145068398807685 19108562972839700324776441)
    ·
      refine ⟨14331422229629775243582331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19108562972839700324776441 14331422229629775243582331)
      ·
        refine ⟨21497133344444662865373497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331422229629775243582331 21497133344444662865373497)
        ·
          refine ⟨16122850008333497149030123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21497133344444662865373497 16122850008333497149030123)
          ·
            refine ⟨24184275012500245723545185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16122850008333497149030123 24184275012500245723545185)
            ·
              refine ⟨18138206259375184292658889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24184275012500245723545185 18138206259375184292658889)
              ·
                refine ⟨13603654694531388219494167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18138206259375184292658889 13603654694531388219494167)
                ·
                  refine ⟨20405482041797082329241251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13603654694531388219494167 20405482041797082329241251)
                  ·
                    refine ⟨30608223062695623493861877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20405482041797082329241251 30608223062695623493861877)
                    ·
                      refine ⟨2869520912127714702549551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30608223062695623493861877 2869520912127714702549551)
                      ·
                        rfl

theorem cell23_5588372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5588372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588372 prefixEnd_5588372 := by exact prefixLift 5588372
  have htrace : WordTrace (prefixWord ++ tailWord_5588372) baseStart_5588372 baseEnd_5588372 := by
    simpa [prefixWord, tailWord_5588372, baseEnd_5588372] using wordTrace_append hprefix tailTrace_5588372
  have hstable : (prefixWord ++ tailWord_5588372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588372).length < 2 ^ (prefixWord ++ tailWord_5588372).sum := by decide
  have hdescent : baseEnd_5588372 < baseStart_5588372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588402 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_5588402 : Nat := 118140960795 + 5588402 * 2 ^ 59
def prefixEnd_5588402 : Nat := 4983230072969 + 3 ^ 40 * 5588402 * 2
def baseEnd_5588402 : Nat := 2869536316547349585174413

theorem tailTrace_5588402 : CollatzResearch.WordTrace tailWord_5588402 prefixEnd_5588402 2869536316547349585174413 := by
  unfold tailWord_5588402
  simp only [CollatzResearch.WordTrace]
  refine ⟨50956441475045362980301865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135883843933454301280804973 50956441475045362980301865)
  ·
    refine ⟨38217331106284022235226399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50956441475045362980301865 38217331106284022235226399)
    ·
      refine ⟨57325996659426033352839599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38217331106284022235226399 57325996659426033352839599)
      ·
        refine ⟨85988994989139050029259399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57325996659426033352839599 85988994989139050029259399)
        ·
          refine ⟨128983492483708575043889099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85988994989139050029259399 128983492483708575043889099)
          ·
            refine ⟨193475238725562862565833649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128983492483708575043889099 193475238725562862565833649)
            ·
              refine ⟨145106429044172146924375237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193475238725562862565833649 145106429044172146924375237)
              ·
                refine ⟨27207455445782277548320357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145106429044172146924375237 27207455445782277548320357)
                ·
                  refine ⟨5101397896084177040310067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27207455445782277548320357 5101397896084177040310067)
                  ·
                    refine ⟨7652096844126265560465101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101397896084177040310067 7652096844126265560465101)
                    ·
                      refine ⟨2869536316547349585174413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652096844126265560465101 2869536316547349585174413)
                      ·
                        rfl

theorem cell23_5588402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_5588402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588402 prefixEnd_5588402 := by exact prefixLift 5588402
  have htrace : WordTrace (prefixWord ++ tailWord_5588402) baseStart_5588402 baseEnd_5588402 := by
    simpa [prefixWord, tailWord_5588402, baseEnd_5588402] using wordTrace_append hprefix tailTrace_5588402
  have hstable : (prefixWord ++ tailWord_5588402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588402).length < 2 ^ (prefixWord ++ tailWord_5588402).sum := by decide
  have hdescent : baseEnd_5588402 < baseStart_5588402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588420 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5588420 : Nat := 118140960795 + 5588420 * 2 ^ 59
def prefixEnd_5588420 : Nat := 4983230072969 + 3 ^ 40 * 5588420 * 2
def baseEnd_5588420 : Nat := 2869545559199130514749331

theorem tailTrace_5588420 : CollatzResearch.WordTrace tailWord_5588420 prefixEnd_5588420 2869545559199130514749331 := by
  unfold tailWord_5588420
  simp only [CollatzResearch.WordTrace]
  refine ⟨101913211207058120497681357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135884281609410827330241809 101913211207058120497681357)
  ·
    refine ⟨38217454202646795186630509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101913211207058120497681357 38217454202646795186630509)
    ·
      refine ⟨14331545325992548194986441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38217454202646795186630509 14331545325992548194986441)
      ·
        refine ⟨10748658994494411146239831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14331545325992548194986441 10748658994494411146239831)
        ·
          refine ⟨16122988491741616719359747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10748658994494411146239831 16122988491741616719359747)
          ·
            refine ⟨24184482737612425079039621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16122988491741616719359747 24184482737612425079039621)
            ·
              refine ⟨4534590513302329702319929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24184482737612425079039621 4534590513302329702319929)
              ·
                refine ⟨3400942884976747276739947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4534590513302329702319929 3400942884976747276739947)
                ·
                  refine ⟨5101414327465120915109921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400942884976747276739947 5101414327465120915109921)
                  ·
                    refine ⟨3826060745598840686332441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5101414327465120915109921 3826060745598840686332441)
                    ·
                      refine ⟨2869545559199130514749331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826060745598840686332441 2869545559199130514749331)
                      ·
                        rfl

theorem cell23_5588420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5588420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588420 prefixEnd_5588420 := by exact prefixLift 5588420
  have htrace : WordTrace (prefixWord ++ tailWord_5588420) baseStart_5588420 baseEnd_5588420 := by
    simpa [prefixWord, tailWord_5588420, baseEnd_5588420] using wordTrace_append hprefix tailTrace_5588420
  have hstable : (prefixWord ++ tailWord_5588420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588420).length < 2 ^ (prefixWord ++ tailWord_5588420).sum := by decide
  have hdescent : baseEnd_5588420 < baseStart_5588420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588475 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 3]
def baseStart_5588475 : Nat := 118140960795 + 5588475 * 2 ^ 59
def prefixEnd_5588475 : Nat := 4983230072969 + 3 ^ 40 * 5588475 * 2
def baseEnd_5588475 : Nat := 2869573800635127799561577

theorem tailTrace_5588475 : CollatzResearch.WordTrace tailWord_5588475 prefixEnd_5588475 2869573800635127799561577 := by
  unfold tailWord_5588475
  simp only [CollatzResearch.WordTrace]
  refine ⟨203828428428916985388614879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135885618952611323592409919 203828428428916985388614879)
  ·
    refine ⟨305742642643375478082922319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203828428428916985388614879 305742642643375478082922319)
    ·
      refine ⟨458613963965063217124383479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305742642643375478082922319 458613963965063217124383479)
      ·
        refine ⟨687920945947594825686575219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458613963965063217124383479 687920945947594825686575219)
        ·
          refine ⟨1031881418921392238529862829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687920945947594825686575219 1031881418921392238529862829)
          ·
            refine ⟨386955532095522089448698561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1031881418921392238529862829 386955532095522089448698561)
            ·
              refine ⟨290216649071641567086523921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386955532095522089448698561 290216649071641567086523921)
              ·
                refine ⟨217662486803731175314892941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290216649071641567086523921 217662486803731175314892941)
                ·
                  refine ⟨81623432551399190743084853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217662486803731175314892941 81623432551399190743084853)
                  ·
                    refine ⟨7652196801693674132164205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81623432551399190743084853 7652196801693674132164205)
                    ·
                      refine ⟨2869573800635127799561577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652196801693674132164205 2869573800635127799561577)
                      ·
                        rfl

theorem cell23_5588475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 3].length) (baseStart_5588475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588475 prefixEnd_5588475 := by exact prefixLift 5588475
  have htrace : WordTrace (prefixWord ++ tailWord_5588475) baseStart_5588475 baseEnd_5588475 := by
    simpa [prefixWord, tailWord_5588475, baseEnd_5588475] using wordTrace_append hprefix tailTrace_5588475
  have hstable : (prefixWord ++ tailWord_5588475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588475).length < 2 ^ (prefixWord ++ tailWord_5588475).sum := by decide
  have hdescent : baseEnd_5588475 < baseStart_5588475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588476 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_5588476 : Nat := 118140960795 + 5588476 * 2 ^ 59
def prefixEnd_5588476 : Nat := 4983230072969 + 3 ^ 40 * 5588476 * 2
def baseEnd_5588476 : Nat := 2869574314115782295649073

theorem tailTrace_5588476 : CollatzResearch.WordTrace tailWord_5588476 prefixEnd_5588476 2869574314115782295649073 := by
  unfold tailWord_5588476
  simp only [CollatzResearch.WordTrace]
  refine ⟨101914232450956681279700641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135885643267942241706267521 101914232450956681279700641)
  ·
    refine ⟨76435674338217510959775481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101914232450956681279700641 76435674338217510959775481)
    ·
      refine ⟨57326755753663133219831611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76435674338217510959775481 57326755753663133219831611)
      ·
        refine ⟨85990133630494699829747417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57326755753663133219831611 85990133630494699829747417)
        ·
          refine ⟨64492600222871024872310563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85990133630494699829747417 64492600222871024872310563)
          ·
            refine ⟨96738900334306537308465845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64492600222871024872310563 96738900334306537308465845)
            ·
              refine ⟨9069271906341237872668673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96738900334306537308465845 9069271906341237872668673)
              ·
                refine ⟨6801953929755928404501505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9069271906341237872668673 6801953929755928404501505)
                ·
                  refine ⟨5101465447316946303376129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6801953929755928404501505 5101465447316946303376129)
                  ·
                    refine ⟨3826099085487709727532097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5101465447316946303376129 3826099085487709727532097)
                    ·
                      refine ⟨2869574314115782295649073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826099085487709727532097 2869574314115782295649073)
                      ·
                        rfl

theorem cell23_5588476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_5588476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588476 prefixEnd_5588476 := by exact prefixLift 5588476
  have htrace : WordTrace (prefixWord ++ tailWord_5588476) baseStart_5588476 baseEnd_5588476 := by
    simpa [prefixWord, tailWord_5588476, baseEnd_5588476] using wordTrace_append hprefix tailTrace_5588476
  have hstable : (prefixWord ++ tailWord_5588476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588476).length < 2 ^ (prefixWord ++ tailWord_5588476).sum := by decide
  have hdescent : baseEnd_5588476 < baseStart_5588476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588512 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_5588512 : Nat := 118140960795 + 5588512 * 2 ^ 59
def prefixEnd_5588512 : Nat := 4983230072969 + 3 ^ 40 * 5588512 * 2
def baseEnd_5588512 : Nat := 956530933139781384932969

theorem tailTrace_5588512 : CollatzResearch.WordTrace tailWord_5588512 prefixEnd_5588512 956530933139781384932969 := by
  unfold tailWord_5588512
  simp only [CollatzResearch.WordTrace]
  refine ⟨101914888964891470353855895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135886518619855293805141193 101914888964891470353855895)
  ·
    refine ⟨152872333447337205530783843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101914888964891470353855895 152872333447337205530783843)
    ·
      refine ⟨229308500171005808296175765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152872333447337205530783843 229308500171005808296175765)
      ·
        refine ⟨10748835945515897263883239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229308500171005808296175765 10748835945515897263883239)
        ·
          refine ⟨16123253918273845895824859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10748835945515897263883239 16123253918273845895824859)
          ·
            refine ⟨24184880877410768843737289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16123253918273845895824859 24184880877410768843737289)
            ·
              refine ⟨18138660658058076632802967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24184880877410768843737289 18138660658058076632802967)
              ·
                refine ⟨27207990987087114949204451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18138660658058076632802967 27207990987087114949204451)
                ·
                  refine ⟨40811986480630672423806677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27207990987087114949204451 40811986480630672423806677)
                  ·
                    refine ⟨956530933139781384932969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40811986480630672423806677 956530933139781384932969)
                    ·
                      rfl

theorem cell23_5588512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_5588512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588512 prefixEnd_5588512 := by exact prefixLift 5588512
  have htrace : WordTrace (prefixWord ++ tailWord_5588512) baseStart_5588512 baseEnd_5588512 := by
    simpa [prefixWord, tailWord_5588512, baseEnd_5588512] using wordTrace_append hprefix tailTrace_5588512
  have hstable : (prefixWord ++ tailWord_5588512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588512).length < 2 ^ (prefixWord ++ tailWord_5588512).sum := by decide
  have hdescent : baseEnd_5588512 < baseStart_5588512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588522 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5588522 : Nat := 118140960795 + 5588522 * 2 ^ 59
def prefixEnd_5588522 : Nat := 4983230072969 + 3 ^ 40 * 5588522 * 2
def baseEnd_5588522 : Nat := 2869597934225889115673861

theorem tailTrace_5588522 : CollatzResearch.WordTrace tailWord_5588522 prefixEnd_5588522 2869597934225889115673861 := by
  unfold tailWord_5588522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50957535664936678103893955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135886761773164474943717213 50957535664936678103893955)
  ·
    refine ⟨76436303497405017155840933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50957535664936678103893955 76436303497405017155840933)
    ·
      refine ⟨14331806905763440716720175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76436303497405017155840933 14331806905763440716720175)
      ·
        refine ⟨21497710358645161075080263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331806905763440716720175 21497710358645161075080263)
        ·
          refine ⟨32246565537967741612620395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21497710358645161075080263 32246565537967741612620395)
          ·
            refine ⟨48369848306951612418930593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32246565537967741612620395 48369848306951612418930593)
            ·
              refine ⟨36277386230213709314197945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48369848306951612418930593 36277386230213709314197945)
              ·
                refine ⟨27208039672660281985648459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36277386230213709314197945 27208039672660281985648459)
                ·
                  refine ⟨40812059508990422978472689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27208039672660281985648459 40812059508990422978472689)
                  ·
                    refine ⟨30609044631742817233854517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40812059508990422978472689 30609044631742817233854517)
                    ·
                      refine ⟨2869597934225889115673861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30609044631742817233854517 2869597934225889115673861)
                      ·
                        rfl

theorem cell23_5588522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5588522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588522 prefixEnd_5588522 := by exact prefixLift 5588522
  have htrace : WordTrace (prefixWord ++ tailWord_5588522) baseStart_5588522 baseEnd_5588522 := by
    simpa [prefixWord, tailWord_5588522, baseEnd_5588522] using wordTrace_append hprefix tailTrace_5588522
  have hstable : (prefixWord ++ tailWord_5588522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588522).length < 2 ^ (prefixWord ++ tailWord_5588522).sum := by decide
  have hdescent : baseEnd_5588522 < baseStart_5588522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588575 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_5588575 : Nat := 118140960795 + 5588575 * 2 ^ 59
def prefixEnd_5588575 : Nat := 4983230072969 + 3 ^ 40 * 5588575 * 2
def baseEnd_5588575 : Nat := 2869625148700577408311117

theorem tailTrace_5588575 : CollatzResearch.WordTrace tailWord_5588575 prefixEnd_5588575 2869625148700577408311117 := by
  unfold tailWord_5588575
  simp only [CollatzResearch.WordTrace]
  refine ⟨203832075728554702467255179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135888050485703134978170119 203832075728554702467255179)
  ·
    refine ⟨305748113592832053700882769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203832075728554702467255179 305748113592832053700882769)
    ·
      refine ⟨229311085194624040275662077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305748113592832053700882769 229311085194624040275662077)
      ·
        refine ⟨85991656947984015103373279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229311085194624040275662077 85991656947984015103373279)
        ·
          refine ⟨128987485421976022655059919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85991656947984015103373279 128987485421976022655059919)
          ·
            refine ⟨193481228132964033982589879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128987485421976022655059919 193481228132964033982589879)
            ·
              refine ⟨290221842199446050973884819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193481228132964033982589879 290221842199446050973884819)
              ·
                refine ⟨435332763299169076460827229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290221842199446050973884819 435332763299169076460827229)
                ·
                  refine ⟨163249786237188403672810211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435332763299169076460827229 163249786237188403672810211)
                  ·
                    refine ⟨244874679355782605509215317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163249786237188403672810211 244874679355782605509215317)
                    ·
                      refine ⟨2869625148700577408311117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 244874679355782605509215317 2869625148700577408311117)
                      ·
                        rfl

theorem cell23_5588575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_5588575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588575 prefixEnd_5588575 := by exact prefixLift 5588575
  have htrace : WordTrace (prefixWord ++ tailWord_5588575) baseStart_5588575 baseEnd_5588575 := by
    simpa [prefixWord, tailWord_5588575, baseEnd_5588575] using wordTrace_append hprefix tailTrace_5588575
  have hstable : (prefixWord ++ tailWord_5588575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588575).length < 2 ^ (prefixWord ++ tailWord_5588575).sum := by decide
  have hdescent : baseEnd_5588575 < baseStart_5588575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588599 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_5588599 : Nat := 118140960795 + 5588599 * 2 ^ 59
def prefixEnd_5588599 : Nat := 4983230072969 + 3 ^ 40 * 5588599 * 2
def baseEnd_5588599 : Nat := 2869637472236285314411007

theorem tailTrace_5588599 : CollatzResearch.WordTrace tailWord_5588599 prefixEnd_5588599 2869637472236285314411007 := by
  unfold tailWord_5588599
  simp only [CollatzResearch.WordTrace]
  refine ⟨203832951080467754566128851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135888634053645169710752567 203832951080467754566128851)
  ·
    refine ⟨305749426620701631849193277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203832951080467754566128851 305749426620701631849193277)
    ·
      refine ⟨114656034982763111943447479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305749426620701631849193277 114656034982763111943447479)
      ·
        refine ⟨171984052474144667915171219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114656034982763111943447479 171984052474144667915171219)
        ·
          refine ⟨257976078711217001872756829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171984052474144667915171219 257976078711217001872756829)
          ·
            refine ⟨96741029516706375702283811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257976078711217001872756829 96741029516706375702283811)
            ·
              refine ⟨145111544275059563553425717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96741029516706375702283811 145111544275059563553425717)
              ·
                refine ⟨13604207275786834083133661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145111544275059563553425717 13604207275786834083133661)
                ·
                  refine ⟨5101577728420062781175123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13604207275786834083133661 5101577728420062781175123)
                  ·
                    refine ⟨7652366592630094171762685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101577728420062781175123 7652366592630094171762685)
                    ·
                      refine ⟨2869637472236285314411007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652366592630094171762685 2869637472236285314411007)
                      ·
                        rfl

theorem cell23_5588599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_5588599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588599 prefixEnd_5588599 := by exact prefixLift 5588599
  have htrace : WordTrace (prefixWord ++ tailWord_5588599) baseStart_5588599 baseEnd_5588599 := by
    simpa [prefixWord, tailWord_5588599, baseEnd_5588599] using wordTrace_append hprefix tailTrace_5588599
  have hstable : (prefixWord ++ tailWord_5588599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588599).length < 2 ^ (prefixWord ++ tailWord_5588599).sum := by decide
  have hdescent : baseEnd_5588599 < baseStart_5588599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588636 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_5588636 : Nat := 118140960795 + 5588636 * 2 ^ 59
def prefixEnd_5588636 : Nat := 4983230072969 + 3 ^ 40 * 5588636 * 2
def baseEnd_5588636 : Nat := 956552157006833889882779

theorem tailTrace_5588636 : CollatzResearch.WordTrace tailWord_5588636 prefixEnd_5588636 956552157006833889882779 := by
  unfold tailWord_5588636
  simp only [CollatzResearch.WordTrace]
  refine ⟨101917150290666854942612881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135889533720889139923483841 101917150290666854942612881)
  ·
    refine ⟨76437862718000141206959661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101917150290666854942612881 76437862718000141206959661)
    ·
      refine ⟨28664198519250052952609873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76437862718000141206959661 28664198519250052952609873)
      ·
        refine ⟨21498148889437539714457405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28664198519250052952609873 21498148889437539714457405)
        ·
          refine ⟨8061805833539077392921527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21498148889437539714457405 8061805833539077392921527)
          ·
            refine ⟨12092708750308616089382291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8061805833539077392921527 12092708750308616089382291)
            ·
              refine ⟨18139063125462924134073437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12092708750308616089382291 18139063125462924134073437)
              ·
                refine ⟨6802148672048596550277539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18139063125462924134073437 6802148672048596550277539)
                ·
                  refine ⟨10203223008072894825416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6802148672048596550277539 10203223008072894825416309)
                  ·
                    refine ⟨956552157006833889882779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10203223008072894825416309 956552157006833889882779)
                    ·
                      rfl

theorem cell23_5588636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_5588636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588636 prefixEnd_5588636 := by exact prefixLift 5588636
  have htrace : WordTrace (prefixWord ++ tailWord_5588636) baseStart_5588636 baseEnd_5588636 := by
    simpa [prefixWord, tailWord_5588636, baseEnd_5588636] using wordTrace_append hprefix tailTrace_5588636
  have hstable : (prefixWord ++ tailWord_5588636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588636).length < 2 ^ (prefixWord ++ tailWord_5588636).sum := by decide
  have hdescent : baseEnd_5588636 < baseStart_5588636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588656 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 3, 2, 2]
def baseStart_5588656 : Nat := 118140960795 + 5588656 * 2 ^ 59
def prefixEnd_5588656 : Nat := 4983230072969 + 3 ^ 40 * 5588656 * 2
def baseEnd_5588656 : Nat := 2869666740633591591398245

theorem tailTrace_5588656 : CollatzResearch.WordTrace tailWord_5588656 prefixEnd_5588656 2869666740633591591398245 := by
  unfold tailWord_5588656
  simp only [CollatzResearch.WordTrace]
  refine ⟨101917515020630626650476911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135890020027507502200635881 101917515020630626650476911)
  ·
    refine ⟨152876272530945939975715367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101917515020630626650476911 152876272530945939975715367)
    ·
      refine ⟨229314408796418909963573051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152876272530945939975715367 229314408796418909963573051)
      ·
        refine ⟨343971613194628364945359577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229314408796418909963573051 343971613194628364945359577)
        ·
          refine ⟨257978709895971273709019683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343971613194628364945359577 257978709895971273709019683)
          ·
            refine ⟨386968064843956910563529525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257978709895971273709019683 386968064843956910563529525)
            ·
              refine ⟨36278256079120960365330893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 386968064843956910563529525 36278256079120960365330893)
              ·
                refine ⟨13604346029670360136999085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36278256079120960365330893 13604346029670360136999085)
                ·
                  refine ⟨5101629761126385051374657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13604346029670360136999085 5101629761126385051374657)
                  ·
                    refine ⟨3826222320844788788530993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5101629761126385051374657 3826222320844788788530993)
                    ·
                      refine ⟨2869666740633591591398245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826222320844788788530993 2869666740633591591398245)
                      ·
                        rfl

theorem cell23_5588656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 2, 2].length) (baseStart_5588656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588656 prefixEnd_5588656 := by exact prefixLift 5588656
  have htrace : WordTrace (prefixWord ++ tailWord_5588656) baseStart_5588656 baseEnd_5588656 := by
    simpa [prefixWord, tailWord_5588656, baseEnd_5588656] using wordTrace_append hprefix tailTrace_5588656
  have hstable : (prefixWord ++ tailWord_5588656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588656).length < 2 ^ (prefixWord ++ tailWord_5588656).sum := by decide
  have hdescent : baseEnd_5588656 < baseStart_5588656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588707 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5588707 : Nat := 118140960795 + 5588707 * 2 ^ 59
def prefixEnd_5588707 : Nat := 4983230072969 + 3 ^ 40 * 5588707 * 2
def baseEnd_5588707 : Nat := 2869692928146970891860511

theorem tailTrace_5588707 : CollatzResearch.WordTrace tailWord_5588707 prefixEnd_5588707 2869692928146970891860511 := by
  unfold tailWord_5588707
  simp only [CollatzResearch.WordTrace]
  refine ⟨203836890164076489011060375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135891260109384326007373583 203836890164076489011060375)
  ·
    refine ⟨305755335246114733516590563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203836890164076489011060375 305755335246114733516590563)
    ·
      refine ⟨458633002869172100274885845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305755335246114733516590563 458633002869172100274885845)
      ·
        refine ⟨10749211004746221100192637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 458633002869172100274885845 10749211004746221100192637)
        ·
          refine ⟨4030954126779832912572239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10749211004746221100192637 4030954126779832912572239)
          ·
            refine ⟨6046431190169749368858359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030954126779832912572239 6046431190169749368858359)
            ·
              refine ⟨9069646785254624053287539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046431190169749368858359 9069646785254624053287539)
              ·
                refine ⟨13604470177881936079931309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9069646785254624053287539 13604470177881936079931309)
                ·
                  refine ⟨5101676316705726029974241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13604470177881936079931309 5101676316705726029974241)
                  ·
                    refine ⟨3826257237529294522480681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5101676316705726029974241 3826257237529294522480681)
                    ·
                      refine ⟨2869692928146970891860511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826257237529294522480681 2869692928146970891860511)
                      ·
                        rfl

theorem cell23_5588707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5588707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588707 prefixEnd_5588707 := by exact prefixLift 5588707
  have htrace : WordTrace (prefixWord ++ tailWord_5588707) baseStart_5588707 baseEnd_5588707 := by
    simpa [prefixWord, tailWord_5588707, baseEnd_5588707] using wordTrace_append hprefix tailTrace_5588707
  have hstable : (prefixWord ++ tailWord_5588707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588707).length < 2 ^ (prefixWord ++ tailWord_5588707).sum := by decide
  have hdescent : baseEnd_5588707 < baseStart_5588707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588723 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 2, 1, 3]
def baseStart_5588723 : Nat := 118140960795 + 5588723 * 2 ^ 59
def prefixEnd_5588723 : Nat := 4983230072969 + 3 ^ 40 * 5588723 * 2
def baseEnd_5588723 : Nat := 2869701143837442829260437

theorem tailTrace_5588723 : CollatzResearch.WordTrace tailWord_5588723 prefixEnd_5588723 2869701143837442829260437 := by
  unfold tailWord_5588723
  simp only [CollatzResearch.WordTrace]
  refine ⟨203837473732018523743642823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135891649154679015829095215 203837473732018523743642823)
  ·
    refine ⟨305756210598027785615464235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203837473732018523743642823 305756210598027785615464235)
    ·
      refine ⟨458634315897041678423196353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305756210598027785615464235 458634315897041678423196353)
      ·
        refine ⟨343975736922781258817397265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458634315897041678423196353 343975736922781258817397265)
        ·
          refine ⟨257981802692085944113047949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343975736922781258817397265 257981802692085944113047949)
          ·
            refine ⟨96743176009532229042392981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257981802692085944113047949 96743176009532229042392981)
            ·
              refine ⟨4534836375446823236362171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96743176009532229042392981 4534836375446823236362171)
              ·
                refine ⟨6802254563170234854543257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534836375446823236362171 6802254563170234854543257)
                ·
                  refine ⟨5101690922377676140907443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6802254563170234854543257 5101690922377676140907443)
                  ·
                    refine ⟨7652536383566514211361165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101690922377676140907443 7652536383566514211361165)
                    ·
                      refine ⟨2869701143837442829260437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652536383566514211361165 2869701143837442829260437)
                      ·
                        rfl

theorem cell23_5588723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 1, 3].length) (baseStart_5588723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588723 prefixEnd_5588723 := by exact prefixLift 5588723
  have htrace : WordTrace (prefixWord ++ tailWord_5588723) baseStart_5588723 baseEnd_5588723 := by
    simpa [prefixWord, tailWord_5588723, baseEnd_5588723] using wordTrace_append hprefix tailTrace_5588723
  have hstable : (prefixWord ++ tailWord_5588723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588723).length < 2 ^ (prefixWord ++ tailWord_5588723).sum := by decide
  have hdescent : baseEnd_5588723 < baseStart_5588723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588746 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_5588746 : Nat := 118140960795 + 5588746 * 2 ^ 59
def prefixEnd_5588746 : Nat := 4983230072969 + 3 ^ 40 * 5588746 * 2
def baseEnd_5588746 : Nat := 2869712953892496239272831

theorem tailTrace_5588746 : CollatzResearch.WordTrace tailWord_5588746 prefixEnd_5588746 2869712953892496239272831 := by
  unfold tailWord_5588746
  simp only [CollatzResearch.WordTrace]
  refine ⟨50959578152733799667932523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135892208407290132447820061 50959578152733799667932523)
  ·
    refine ⟨76439367229100699501898785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50959578152733799667932523 76439367229100699501898785)
    ·
      refine ⟨57329525421825524626424089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76439367229100699501898785 57329525421825524626424089)
      ·
        refine ⟨42997144066369143469818067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57329525421825524626424089 42997144066369143469818067)
        ·
          refine ⟨64495716099553715204727101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42997144066369143469818067 64495716099553715204727101)
          ·
            refine ⟨24185893537332643201772663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64495716099553715204727101 24185893537332643201772663)
            ·
              refine ⟨36278840305998964802658995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24185893537332643201772663 36278840305998964802658995)
              ·
                refine ⟨54418260458998447203988493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36278840305998964802658995 54418260458998447203988493)
                ·
                  refine ⟨20406847672124417701495685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54418260458998447203988493 20406847672124417701495685)
                  ·
                    refine ⟨3826283938523328319030441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20406847672124417701495685 3826283938523328319030441)
                    ·
                      refine ⟨2869712953892496239272831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826283938523328319030441 2869712953892496239272831)
                      ·
                        rfl

theorem cell23_5588746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_5588746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588746 prefixEnd_5588746 := by exact prefixLift 5588746
  have htrace : WordTrace (prefixWord ++ tailWord_5588746) baseStart_5588746 baseEnd_5588746 := by
    simpa [prefixWord, tailWord_5588746, baseEnd_5588746] using wordTrace_append hprefix tailTrace_5588746
  have hstable : (prefixWord ++ tailWord_5588746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588746).length < 2 ^ (prefixWord ++ tailWord_5588746).sum := by decide
  have hdescent : baseEnd_5588746 < baseStart_5588746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588776 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5588776 : Nat := 118140960795 + 5588776 * 2 ^ 59
def prefixEnd_5588776 : Nat := 4983230072969 + 3 ^ 40 * 5588776 * 2
def baseEnd_5588776 : Nat := 2869728358312131121897693

theorem tailTrace_5588776 : CollatzResearch.WordTrace tailWord_5588776 prefixEnd_5588776 2869728358312131121897693 := by
  unfold tailWord_5588776
  simp only [CollatzResearch.WordTrace]
  refine ⟨101919703400413256897661091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135892937867217675863548121 101919703400413256897661091)
  ·
    refine ⟨152879555100619885346491637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101919703400413256897661091 152879555100619885346491637)
    ·
      refine ⟨14332458290683114251233591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152879555100619885346491637 14332458290683114251233591)
      ·
        refine ⟨21498687436024671376850387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14332458290683114251233591 21498687436024671376850387)
        ·
          refine ⟨32248031154037007065275581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21498687436024671376850387 32248031154037007065275581)
          ·
            refine ⟨12093011682763877649478343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32248031154037007065275581 12093011682763877649478343)
            ·
              refine ⟨18139517524145816474217515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12093011682763877649478343 18139517524145816474217515)
              ·
                refine ⟨27209276286218724711326273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18139517524145816474217515 27209276286218724711326273)
                ·
                  refine ⟨20406957214664043533494705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27209276286218724711326273 20406957214664043533494705)
                  ·
                    refine ⟨15305217910998032650121029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20406957214664043533494705 15305217910998032650121029)
                    ·
                      refine ⟨2869728358312131121897693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15305217910998032650121029 2869728358312131121897693)
                      ·
                        rfl

theorem cell23_5588776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5588776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588776 prefixEnd_5588776 := by exact prefixLift 5588776
  have htrace : WordTrace (prefixWord ++ tailWord_5588776) baseStart_5588776 baseEnd_5588776 := by
    simpa [prefixWord, tailWord_5588776, baseEnd_5588776] using wordTrace_append hprefix tailTrace_5588776
  have hstable : (prefixWord ++ tailWord_5588776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588776).length < 2 ^ (prefixWord ++ tailWord_5588776).sum := by decide
  have hdescent : baseEnd_5588776 < baseStart_5588776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588813 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5588813 : Nat := 118140960795 + 5588813 * 2 ^ 59
def prefixEnd_5588813 : Nat := 4983230072969 + 3 ^ 40 * 5588813 * 2
def baseEnd_5588813 : Nat := 2869747357096347477135023

theorem tailTrace_5588813 : CollatzResearch.WordTrace tailWord_5588813 prefixEnd_5588813 2869747357096347477135023 := by
  unfold tailWord_5588813
  simp only [CollatzResearch.WordTrace]
  refine ⟨203840756301692469114419093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135893837534461646076279395 203840756301692469114419093)
  ·
    refine ⟨9555035451641834489738395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203840756301692469114419093 9555035451641834489738395)
    ·
      refine ⟨14332553177462751734607593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9555035451641834489738395 14332553177462751734607593)
      ·
        refine ⟨10749414883097063800955695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14332553177462751734607593 10749414883097063800955695)
        ·
          refine ⟨16124122324645595701433543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10749414883097063800955695 16124122324645595701433543)
          ·
            refine ⟨24186183486968393552150315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16124122324645595701433543 24186183486968393552150315)
            ·
              refine ⟨36279275230452590328225473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24186183486968393552150315 36279275230452590328225473)
              ·
                refine ⟨27209456422839442746169105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36279275230452590328225473 27209456422839442746169105)
                ·
                  refine ⟨20407092317129582059626829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27209456422839442746169105 20407092317129582059626829)
                  ·
                    refine ⟨7652659618923593272360061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20407092317129582059626829 7652659618923593272360061)
                    ·
                      refine ⟨2869747357096347477135023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652659618923593272360061 2869747357096347477135023)
                      ·
                        rfl

theorem cell23_5588813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5588813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588813 prefixEnd_5588813 := by exact prefixLift 5588813
  have htrace : WordTrace (prefixWord ++ tailWord_5588813) baseStart_5588813 baseEnd_5588813 := by
    simpa [prefixWord, tailWord_5588813, baseEnd_5588813] using wordTrace_append hprefix tailTrace_5588813
  have hstable : (prefixWord ++ tailWord_5588813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588813).length < 2 ^ (prefixWord ++ tailWord_5588813).sum := by decide
  have hdescent : baseEnd_5588813 < baseStart_5588813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588849 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_5588849 : Nat := 118140960795 + 5588849 * 2 ^ 59
def prefixEnd_5588849 : Nat := 4983230072969 + 3 ^ 40 * 5588849 * 2
def baseEnd_5588849 : Nat := 2869765842399909336284857

theorem tailTrace_5588849 : CollatzResearch.WordTrace tailWord_5588849 prefixEnd_5588849 2869765842399909336284857 := by
  unfold tailWord_5588849
  simp only [CollatzResearch.WordTrace]
  refine ⟨203842069329562047262729601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135894712886374698175153067 203842069329562047262729601)
  ·
    refine ⟨152881551997171535447047201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203842069329562047262729601 152881551997171535447047201)
    ·
      refine ⟨114661163997878651585285401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152881551997171535447047201 114661163997878651585285401)
      ·
        refine ⟨85995872998408988688964051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114661163997878651585285401 85995872998408988688964051)
        ·
          refine ⟨128993809497613483033446077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85995872998408988688964051 128993809497613483033446077)
          ·
            refine ⟨48372678561605056137542279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128993809497613483033446077 48372678561605056137542279)
            ·
              refine ⟨72559017842407584206313419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48372678561605056137542279 72559017842407584206313419)
              ·
                refine ⟨108838526763611376309470129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72559017842407584206313419 108838526763611376309470129)
                ·
                  refine ⟨81628895072708532232102597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108838526763611376309470129 81628895072708532232102597)
                  ·
                    refine ⟨15305417826132849793519237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81628895072708532232102597 15305417826132849793519237)
                    ·
                      refine ⟨2869765842399909336284857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15305417826132849793519237 2869765842399909336284857)
                      ·
                        rfl

theorem cell23_5588849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_5588849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588849 prefixEnd_5588849 := by exact prefixLift 5588849
  have htrace : WordTrace (prefixWord ++ tailWord_5588849) baseStart_5588849 baseEnd_5588849 := by
    simpa [prefixWord, tailWord_5588849, baseEnd_5588849] using wordTrace_append hprefix tailTrace_5588849
  have hstable : (prefixWord ++ tailWord_5588849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588849).length < 2 ^ (prefixWord ++ tailWord_5588849).sum := by decide
  have hdescent : baseEnd_5588849 < baseStart_5588849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588893 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 6]
def baseStart_5588893 : Nat := 118140960795 + 5588893 * 2 ^ 59
def prefixEnd_5588893 : Nat := 4983230072969 + 3 ^ 40 * 5588893 * 2
def baseEnd_5588893 : Nat := 318865381727634129348295

theorem tailTrace_5588893 : CollatzResearch.WordTrace tailWord_5588893 prefixEnd_5588893 318865381727634129348295 := by
  unfold tailWord_5588893
  simp only [CollatzResearch.WordTrace]
  refine ⟨203843674141402642777331333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135895782760935095184887555 203843674141402642777331333)
  ·
    refine ⟨38220688901512995520749625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203843674141402642777331333 38220688901512995520749625)
    ·
      refine ⟨28665516676134746640562219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38220688901512995520749625 28665516676134746640562219)
      ·
        refine ⟨42998275014202119960843329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28665516676134746640562219 42998275014202119960843329)
        ·
          refine ⟨32248706260651589970632497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42998275014202119960843329 32248706260651589970632497)
          ·
            refine ⟨24186529695488692477974373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32248706260651589970632497 24186529695488692477974373)
            ·
              refine ⟨4534974317904129839620195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24186529695488692477974373 4534974317904129839620195)
              ·
                refine ⟨6802461476856194759430293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534974317904129839620195 6802461476856194759430293)
                ·
                  refine ⟨318865381727634129348295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6802461476856194759430293 318865381727634129348295)
                  ·
                    rfl

theorem cell23_5588893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_5588893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588893 prefixEnd_5588893 := by exact prefixLift 5588893
  have htrace : WordTrace (prefixWord ++ tailWord_5588893) baseStart_5588893 baseEnd_5588893 := by
    simpa [prefixWord, tailWord_5588893, baseEnd_5588893] using wordTrace_append hprefix tailTrace_5588893
  have hstable : (prefixWord ++ tailWord_5588893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588893).length < 2 ^ (prefixWord ++ tailWord_5588893).sum := by decide
  have hdescent : baseEnd_5588893 < baseStart_5588893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588920 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 1, 1, 3]
def baseStart_5588920 : Nat := 118140960795 + 5588920 * 2 ^ 59
def prefixEnd_5588920 : Nat := 4983230072969 + 3 ^ 40 * 5588920 * 2
def baseEnd_5588920 : Nat := 2869802299526378558497031

theorem tailTrace_5588920 : CollatzResearch.WordTrace tailWord_5588920 prefixEnd_5588920 2869802299526378558497031 := by
  unfold tailWord_5588920
  simp only [CollatzResearch.WordTrace]
  refine ⟨101922329456152413194282107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135896439274869884259042809 101922329456152413194282107)
  ·
    refine ⟨152883494184228619791423161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101922329456152413194282107 152883494184228619791423161)
    ·
      refine ⟨114662620638171464843567371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152883494184228619791423161 114662620638171464843567371)
      ·
        refine ⟨171993930957257197265351057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114662620638171464843567371 171993930957257197265351057)
        ·
          refine ⟨128995448217942897949013293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171993930957257197265351057 128995448217942897949013293)
          ·
            refine ⟨48373293081728586730879985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128995448217942897949013293 48373293081728586730879985)
            ·
              refine ⟨36279969811296440048159989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48373293081728586730879985 36279969811296440048159989)
              ·
                refine ⟨3401247169809041254514999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36279969811296440048159989 3401247169809041254514999)
                ·
                  refine ⟨5101870754713561881772499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401247169809041254514999 5101870754713561881772499)
                  ·
                    refine ⟨7652806132070342822658749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101870754713561881772499 7652806132070342822658749)
                    ·
                      refine ⟨2869802299526378558497031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652806132070342822658749 2869802299526378558497031)
                      ·
                        rfl

theorem cell23_5588920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_5588920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588920 prefixEnd_5588920 := by exact prefixLift 5588920
  have htrace : WordTrace (prefixWord ++ tailWord_5588920) baseStart_5588920 baseEnd_5588920 := by
    simpa [prefixWord, tailWord_5588920, baseEnd_5588920] using wordTrace_append hprefix tailTrace_5588920
  have hstable : (prefixWord ++ tailWord_5588920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588920).length < 2 ^ (prefixWord ++ tailWord_5588920).sum := by decide
  have hdescent : baseEnd_5588920 < baseStart_5588920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588953 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 1, 6]
def baseStart_5588953 : Nat := 118140960795 + 5588953 * 2 ^ 59
def prefixEnd_5588953 : Nat := 4983230072969 + 3 ^ 40 * 5588953 * 2
def baseEnd_5588953 : Nat := 956606414795992309794793

theorem tailTrace_5588953 : CollatzResearch.WordTrace tailWord_5588953 prefixEnd_5588953 956606414795992309794793 := by
  unfold tailWord_5588953
  simp only [CollatzResearch.WordTrace]
  refine ⟨203845862521185273024515513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135897241680790182016343675 203845862521185273024515513)
  ·
    refine ⟨152884396890888954768386635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203845862521185273024515513 152884396890888954768386635)
    ·
      refine ⟨229326595336333432152579953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152884396890888954768386635 229326595336333432152579953)
      ·
        refine ⟨171994946502250074114434965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229326595336333432152579953 171994946502250074114434965)
        ·
          refine ⟨8062263117292972224114139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171994946502250074114434965 8062263117292972224114139)
          ·
            refine ⟨12093394675939458336171209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062263117292972224114139 12093394675939458336171209)
            ·
              refine ⟨9070046006954593752128407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12093394675939458336171209 9070046006954593752128407)
              ·
                refine ⟨13605069010431890628192611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9070046006954593752128407 13605069010431890628192611)
                ·
                  refine ⟨20407603515647835942288917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13605069010431890628192611 20407603515647835942288917)
                  ·
                    refine ⟨956606414795992309794793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20407603515647835942288917 956606414795992309794793)
                    ·
                      rfl

theorem cell23_5588953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_5588953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588953 prefixEnd_5588953 := by exact prefixLift 5588953
  have htrace : WordTrace (prefixWord ++ tailWord_5588953) baseStart_5588953 baseEnd_5588953 := by
    simpa [prefixWord, tailWord_5588953, baseEnd_5588953] using wordTrace_append hprefix tailTrace_5588953
  have hstable : (prefixWord ++ tailWord_5588953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588953).length < 2 ^ (prefixWord ++ tailWord_5588953).sum := by decide
  have hdescent : baseEnd_5588953 < baseStart_5588953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588963 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5588963 : Nat := 118140960795 + 5588963 * 2 ^ 59
def prefixEnd_5588963 : Nat := 4983230072969 + 3 ^ 40 * 5588963 * 2
def baseEnd_5588963 : Nat := 2869824379194521890259333

theorem tailTrace_5588963 : CollatzResearch.WordTrace tailWord_5588963 prefixEnd_5588963 2869824379194521890259333 := by
  unfold tailWord_5588963
  simp only [CollatzResearch.WordTrace]
  refine ⟨203846227251149044732379543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135897484834099363154919695 203846227251149044732379543)
  ·
    refine ⟨305769340876723567098569315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203846227251149044732379543 305769340876723567098569315)
    ·
      refine ⟨458654011315085350647853973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305769340876723567098569315 458654011315085350647853973)
      ·
        refine ⟨21499406780394625811618155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 458654011315085350647853973 21499406780394625811618155)
        ·
          refine ⟨32249110170591938717427233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21499406780394625811618155 32249110170591938717427233)
          ·
            refine ⟨24186832627943954038070425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32249110170591938717427233 24186832627943954038070425)
            ·
              refine ⟨18140124470957965528552819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24186832627943954038070425 18140124470957965528552819)
              ·
                refine ⟨27210186706436948292829229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18140124470957965528552819 27210186706436948292829229)
                ·
                  refine ⟨10203820014913855609810961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27210186706436948292829229 10203820014913855609810961)
                  ·
                    refine ⟨7652865011185391707358221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10203820014913855609810961 7652865011185391707358221)
                    ·
                      refine ⟨2869824379194521890259333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652865011185391707358221 2869824379194521890259333)
                      ·
                        rfl

theorem cell23_5588963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5588963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588963 prefixEnd_5588963 := by exact prefixLift 5588963
  have htrace : WordTrace (prefixWord ++ tailWord_5588963) baseStart_5588963 baseEnd_5588963 := by
    simpa [prefixWord, tailWord_5588963, baseEnd_5588963] using wordTrace_append hprefix tailTrace_5588963
  have hstable : (prefixWord ++ tailWord_5588963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588963).length < 2 ^ (prefixWord ++ tailWord_5588963).sum := by decide
  have hdescent : baseEnd_5588963 < baseStart_5588963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5588977 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 1, 1, 4]
def baseStart_5588977 : Nat := 118140960795 + 5588977 * 2 ^ 59
def prefixEnd_5588977 : Nat := 4983230072969 + 3 ^ 40 * 5588977 * 2
def baseEnd_5588977 : Nat := 2869831567923684835484269

theorem tailTrace_5588977 : CollatzResearch.WordTrace tailWord_5588977 prefixEnd_5588977 2869831567923684835484269 := by
  unfold tailWord_5588977
  simp only [CollatzResearch.WordTrace]
  refine ⟨203846737873098325123389185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135897825248732216748926123 203846737873098325123389185)
  ·
    refine ⟨152885053404823743842541889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203846737873098325123389185 152885053404823743842541889)
    ·
      refine ⟨114663790053617807881906417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152885053404823743842541889 114663790053617807881906417)
      ·
        refine ⟨85997842540213355911429813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114663790053617807881906417 85997842540213355911429813)
        ·
          refine ⟨8062297738145002116696545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85997842540213355911429813 8062297738145002116696545)
          ·
            refine ⟨6046723303608751587522409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8062297738145002116696545 6046723303608751587522409)
            ·
              refine ⟨4535042477706563690641807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6046723303608751587522409 4535042477706563690641807)
              ·
                refine ⟨6802563716559845535962711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535042477706563690641807 6802563716559845535962711)
                ·
                  refine ⟨10203845574839768303944067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6802563716559845535962711 10203845574839768303944067)
                  ·
                    refine ⟨15305768362259652455916101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10203845574839768303944067 15305768362259652455916101)
                    ·
                      refine ⟨2869831567923684835484269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15305768362259652455916101 2869831567923684835484269)
                      ·
                        rfl

theorem cell23_5588977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_5588977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5588977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5588977 prefixEnd_5588977 := by exact prefixLift 5588977
  have htrace : WordTrace (prefixWord ++ tailWord_5588977) baseStart_5588977 baseEnd_5588977 := by
    simpa [prefixWord, tailWord_5588977, baseEnd_5588977] using wordTrace_append hprefix tailTrace_5588977
  have hstable : (prefixWord ++ tailWord_5588977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5588977).length < 2 ^ (prefixWord ++ tailWord_5588977).sum := by decide
  have hdescent : baseEnd_5588977 < baseStart_5588977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5588977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589028 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5589028 : Nat := 118140960795 + 5589028 * 2 ^ 59
def prefixEnd_5589028 : Nat := 4983230072969 + 3 ^ 40 * 5589028 * 2
def baseEnd_5589028 : Nat := 2869857755437064135946535

theorem tailTrace_5589028 : CollatzResearch.WordTrace tailWord_5589028 prefixEnd_5589028 2869857755437064135946535 := by
  unfold tailWord_5589028
  simp only [CollatzResearch.WordTrace]
  refine ⟨101924298997956780416747869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135899065330609040555663825 101924298997956780416747869)
  ·
    refine ⟨38221612124233792656280451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101924298997956780416747869 38221612124233792656280451)
    ·
      refine ⟨57332418186350688984420677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38221612124233792656280451 57332418186350688984420677)
      ·
        refine ⟨10749828409940754184578877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57332418186350688984420677 10749828409940754184578877)
        ·
          refine ⟨4031185653727782819217079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10749828409940754184578877 4031185653727782819217079)
          ·
            refine ⟨6046778480591674228825619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031185653727782819217079 6046778480591674228825619)
            ·
              refine ⟨9070167720887511343238429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046778480591674228825619 9070167720887511343238429)
              ·
                refine ⟨3401312895332816753714411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9070167720887511343238429 3401312895332816753714411)
                ·
                  refine ⟨5101969342999225130571617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401312895332816753714411 5101969342999225130571617)
                  ·
                    refine ⟨3826477007249418847928713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5101969342999225130571617 3826477007249418847928713)
                    ·
                      refine ⟨2869857755437064135946535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826477007249418847928713 2869857755437064135946535)
                      ·
                        rfl

theorem cell23_5589028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5589028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589028 prefixEnd_5589028 := by exact prefixLift 5589028
  have htrace : WordTrace (prefixWord ++ tailWord_5589028) baseStart_5589028 baseEnd_5589028 := by
    simpa [prefixWord, tailWord_5589028, baseEnd_5589028] using wordTrace_append hprefix tailTrace_5589028
  have hstable : (prefixWord ++ tailWord_5589028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589028).length < 2 ^ (prefixWord ++ tailWord_5589028).sum := by decide
  have hdescent : baseEnd_5589028 < baseStart_5589028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589053 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5589053 : Nat := 118140960795 + 5589053 * 2 ^ 59
def prefixEnd_5589053 : Nat := 4983230072969 + 3 ^ 40 * 5589053 * 2
def baseEnd_5589053 : Nat := 2869870592453426538133919

theorem tailTrace_5589053 : CollatzResearch.WordTrace tailWord_5589053 prefixEnd_5589053 2869870592453426538133919 := by
  unfold tailWord_5589053
  simp only [CollatzResearch.WordTrace]
  refine ⟨203849509820822990103155813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135899673213881993402103875 203849509820822990103155813)
  ·
    refine ⟨38221783091404310644341715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203849509820822990103155813 38221783091404310644341715)
    ·
      refine ⟨57332674637106465966512573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38221783091404310644341715 57332674637106465966512573)
      ·
        refine ⟨21499752988914924737442215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57332674637106465966512573 21499752988914924737442215)
        ·
          refine ⟨32249629483372387106163323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21499752988914924737442215 32249629483372387106163323)
          ·
            refine ⟨48374444225058580659244985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32249629483372387106163323 48374444225058580659244985)
            ·
              refine ⟨36280833168793935494433739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48374444225058580659244985 36280833168793935494433739)
              ·
                refine ⟨54421249753190903241650609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36280833168793935494433739 54421249753190903241650609)
                ·
                  refine ⟨40815937314893177431237957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54421249753190903241650609 40815937314893177431237957)
                  ·
                    refine ⟨7652988246542470768357117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40815937314893177431237957 7652988246542470768357117)
                    ·
                      refine ⟨2869870592453426538133919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7652988246542470768357117 2869870592453426538133919)
                      ·
                        rfl

theorem cell23_5589053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5589053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589053 prefixEnd_5589053 := by exact prefixLift 5589053
  have htrace : WordTrace (prefixWord ++ tailWord_5589053) baseStart_5589053 baseEnd_5589053 := by
    simpa [prefixWord, tailWord_5589053, baseEnd_5589053] using wordTrace_append hprefix tailTrace_5589053
  have hstable : (prefixWord ++ tailWord_5589053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589053).length < 2 ^ (prefixWord ++ tailWord_5589053).sum := by decide
  have hdescent : baseEnd_5589053 < baseStart_5589053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589103 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 2, 5]
def baseStart_5589103 : Nat := 118140960795 + 5589103 * 2 ^ 59
def prefixEnd_5589103 : Nat := 4983230072969 + 3 ^ 40 * 5589103 * 2
def baseEnd_5589103 : Nat := 956632088828717114169563

theorem tailTrace_5589103 : CollatzResearch.WordTrace tailWord_5589103 prefixEnd_5589103 956632088828717114169563 := by
  unfold tailWord_5589103
  simp only [CollatzResearch.WordTrace]
  refine ⟨203851333470641848642475963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135900888980427899094983975 203851333470641848642475963)
  ·
    refine ⟨305777000205962772963713945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203851333470641848642475963 305777000205962772963713945)
    ·
      refine ⟨229332750154472079722785459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305777000205962772963713945 229332750154472079722785459)
      ·
        refine ⟨343999125231708119584178189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229332750154472079722785459 343999125231708119584178189)
        ·
          refine ⟨128999671961890544844066821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343999125231708119584178189 128999671961890544844066821)
          ·
            refine ⟨24187438492854477158262529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128999671961890544844066821 24187438492854477158262529)
            ·
              refine ⟨18140578869640857868696897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24187438492854477158262529 18140578869640857868696897)
              ·
                refine ⟨13605434152230643401522673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18140578869640857868696897 13605434152230643401522673)
                ·
                  refine ⟨10204075614172982551142005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13605434152230643401522673 10204075614172982551142005)
                  ·
                    refine ⟨956632088828717114169563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10204075614172982551142005 956632088828717114169563)
                    ·
                      rfl

theorem cell23_5589103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_5589103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589103 prefixEnd_5589103 := by exact prefixLift 5589103
  have htrace : WordTrace (prefixWord ++ tailWord_5589103) baseStart_5589103 baseEnd_5589103 := by
    simpa [prefixWord, tailWord_5589103, baseEnd_5589103] using wordTrace_append hprefix tailTrace_5589103
  have hstable : (prefixWord ++ tailWord_5589103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589103).length < 2 ^ (prefixWord ++ tailWord_5589103).sum := by decide
  have hdescent : baseEnd_5589103 < baseStart_5589103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589113 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_5589113 : Nat := 118140960795 + 5589113 * 2 ^ 59
def prefixEnd_5589113 : Nat := 4983230072969 + 3 ^ 40 * 5589113 * 2
def baseEnd_5589113 : Nat := 2869901401292696303383643

theorem tailTrace_5589113 : CollatzResearch.WordTrace tailWord_5589113 prefixEnd_5589113 2869901401292696303383643 := by
  unfold tailWord_5589113
  simp only [CollatzResearch.WordTrace]
  refine ⟨203851698200605620350339993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135901132133737080233559995 203851698200605620350339993)
  ·
    refine ⟨152888773650454215262754995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203851698200605620350339993 152888773650454215262754995)
    ·
      refine ⟨229333160475681322894132493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152888773650454215262754995 229333160475681322894132493)
      ·
        refine ⟨85999935178380496085299685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229333160475681322894132493 85999935178380496085299685)
        ·
          refine ⟨16124987845946343015993691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85999935178380496085299685 16124987845946343015993691)
          ·
            refine ⟨24187481768919514523990537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16124987845946343015993691 24187481768919514523990537)
            ·
              refine ⟨18140611326689635892992903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24187481768919514523990537 18140611326689635892992903)
              ·
                refine ⟨27210916990034453839489355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18140611326689635892992903 27210916990034453839489355)
                ·
                  refine ⟨40816375485051680759234033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27210916990034453839489355 40816375485051680759234033)
                  ·
                    refine ⟨30612281613788760569425525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40816375485051680759234033 30612281613788760569425525)
                    ·
                      refine ⟨2869901401292696303383643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30612281613788760569425525 2869901401292696303383643)
                      ·
                        rfl

theorem cell23_5589113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_5589113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589113 prefixEnd_5589113 := by exact prefixLift 5589113
  have htrace : WordTrace (prefixWord ++ tailWord_5589113) baseStart_5589113 baseEnd_5589113 := by
    simpa [prefixWord, tailWord_5589113, baseEnd_5589113] using wordTrace_append hprefix tailTrace_5589113
  have hstable : (prefixWord ++ tailWord_5589113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589113).length < 2 ^ (prefixWord ++ tailWord_5589113).sum := by decide
  have hdescent : baseEnd_5589113 < baseStart_5589113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589153 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5589153 : Nat := 118140960795 + 5589153 * 2 ^ 59
def prefixEnd_5589153 : Nat := 4983230072969 + 3 ^ 40 * 5589153 * 2
def baseEnd_5589153 : Nat := 2869921940518876146883459

theorem tailTrace_5589153 : CollatzResearch.WordTrace tailWord_5589153 prefixEnd_5589153 2869921940518876146883459 := by
  unfold tailWord_5589153
  simp only [CollatzResearch.WordTrace]
  refine ⟨203853157120460707181796113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135902104746973804787864075 203853157120460707181796113)
  ·
    refine ⟨152889867840345530386347085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203853157120460707181796113 152889867840345530386347085)
    ·
      refine ⟨57333700440129573894880157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152889867840345530386347085 57333700440129573894880157)
      ·
        refine ⟨21500137665048590210580059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57333700440129573894880157 21500137665048590210580059)
        ·
          refine ⟨32250206497572885315870089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21500137665048590210580059 32250206497572885315870089)
          ·
            refine ⟨24187654873179663986902567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32250206497572885315870089 24187654873179663986902567)
            ·
              refine ⟨36281482309769495980353851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24187654873179663986902567 36281482309769495980353851)
              ·
                refine ⟨54422223464654243970530777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36281482309769495980353851 54422223464654243970530777)
                ·
                  refine ⟨40816667598490682977898083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54422223464654243970530777 40816667598490682977898083)
                  ·
                    refine ⟨61225001397736024466847125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40816667598490682977898083 61225001397736024466847125)
                    ·
                      refine ⟨2869921940518876146883459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61225001397736024466847125 2869921940518876146883459)
                      ·
                        rfl

theorem cell23_5589153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5589153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589153 prefixEnd_5589153 := by exact prefixLift 5589153
  have htrace : WordTrace (prefixWord ++ tailWord_5589153) baseStart_5589153 baseEnd_5589153 := by
    simpa [prefixWord, tailWord_5589153, baseEnd_5589153] using wordTrace_append hprefix tailTrace_5589153
  have hstable : (prefixWord ++ tailWord_5589153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589153).length < 2 ^ (prefixWord ++ tailWord_5589153).sum := by decide
  have hdescent : baseEnd_5589153 < baseStart_5589153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589200 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 8, 3, 2]
def baseStart_5589200 : Nat := 118140960795 + 5589200 * 2 ^ 59
def prefixEnd_5589200 : Nat := 4983230072969 + 3 ^ 40 * 5589200 * 2
def baseEnd_5589200 : Nat := 2869946074109637462995743

theorem tailTrace_5589200 : CollatzResearch.WordTrace tailWord_5589200 prefixEnd_5589200 2869946074109637462995743 := by
  unfold tailWord_5589200
  simp only [CollatzResearch.WordTrace]
  refine ⟨101927435675645217104378527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135903247567526956139171369 101927435675645217104378527)
  ·
    refine ⟨152891153513467825656567791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101927435675645217104378527 152891153513467825656567791)
    ·
      refine ⟨229336730270201738484851687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152891153513467825656567791 229336730270201738484851687)
      ·
        refine ⟨344005095405302607727277531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229336730270201738484851687 344005095405302607727277531)
        ·
          refine ⟨516007643107953911590916297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344005095405302607727277531 516007643107953911590916297)
          ·
            refine ⟨387005732330965433693187223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516007643107953911590916297 387005732330965433693187223)
            ·
              refine ⟨580508598496448150539780835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387005732330965433693187223 580508598496448150539780835)
              ·
                refine ⟨870762897744672225809671253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580508598496448150539780835 870762897744672225809671253)
                ·
                  refine ⟨10204252707945377646207085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 870762897744672225809671253 10204252707945377646207085)
                  ·
                    refine ⟨3826594765479516617327657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10204252707945377646207085 3826594765479516617327657)
                    ·
                      refine ⟨2869946074109637462995743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826594765479516617327657 2869946074109637462995743)
                      ·
                        rfl

theorem cell23_5589200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 3, 2].length) (baseStart_5589200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589200 prefixEnd_5589200 := by exact prefixLift 5589200
  have htrace : WordTrace (prefixWord ++ tailWord_5589200) baseStart_5589200 baseEnd_5589200 := by
    simpa [prefixWord, tailWord_5589200, baseEnd_5589200] using wordTrace_append hprefix tailTrace_5589200
  have hstable : (prefixWord ++ tailWord_5589200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589200).length < 2 ^ (prefixWord ++ tailWord_5589200).sum := by decide
  have hdescent : baseEnd_5589200 < baseStart_5589200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589210 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_5589210 : Nat := 118140960795 + 5589210 * 2 ^ 59
def prefixEnd_5589210 : Nat := 4983230072969 + 3 ^ 40 * 5589210 * 2
def baseEnd_5589210 : Nat := 956650402972060807956899

theorem tailTrace_5589210 : CollatzResearch.WordTrace tailWord_5589210 prefixEnd_5589210 956650402972060807956899 := by
  unfold tailWord_5589210
  simp only [CollatzResearch.WordTrace]
  refine ⟨50963809020313551479155271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135903490720836137277747389 50963809020313551479155271)
  ·
    refine ⟨76445713530470327218732907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50963809020313551479155271 76445713530470327218732907)
    ·
      refine ⟨114668570295705490828099361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76445713530470327218732907 114668570295705490828099361)
      ·
        refine ⟨86001427721779118121074521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114668570295705490828099361 86001427721779118121074521)
        ·
          refine ⟨64501070791334338590805891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86001427721779118121074521 64501070791334338590805891)
          ·
            refine ⟨96751606187001507886208837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64501070791334338590805891 96751606187001507886208837)
            ·
              refine ⟨18140926160062782728664157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96751606187001507886208837 18140926160062782728664157)
              ·
                refine ⟨6802847310023543523249059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18140926160062782728664157 6802847310023543523249059)
                ·
                  refine ⟨10204270965035315284873589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6802847310023543523249059 10204270965035315284873589)
                  ·
                    refine ⟨956650402972060807956899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10204270965035315284873589 956650402972060807956899)
                    ·
                      rfl

theorem cell23_5589210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_5589210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589210 prefixEnd_5589210 := by exact prefixLift 5589210
  have htrace : WordTrace (prefixWord ++ tailWord_5589210) baseStart_5589210 baseEnd_5589210 := by
    simpa [prefixWord, tailWord_5589210, baseEnd_5589210] using wordTrace_append hprefix tailTrace_5589210
  have hstable : (prefixWord ++ tailWord_5589210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589210).length < 2 ^ (prefixWord ++ tailWord_5589210).sum := by decide
  have hdescent : baseEnd_5589210 < baseStart_5589210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589217 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_5589217 : Nat := 118140960795 + 5589217 * 2 ^ 59
def prefixEnd_5589217 : Nat := 4983230072969 + 3 ^ 40 * 5589217 * 2
def baseEnd_5589217 : Nat := 2869954803280763896483165

theorem tailTrace_5589217 : CollatzResearch.WordTrace tailWord_5589217 prefixEnd_5589217 2869954803280763896483165 := by
  unfold tailWord_5589217
  simp only [CollatzResearch.WordTrace]
  refine ⟨203855491392228846112125905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135903660928152564074750603 203855491392228846112125905)
  ·
    refine ⟨152891618544171634584094429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203855491392228846112125905 152891618544171634584094429)
    ·
      refine ⟨57334356954064362969035411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152891618544171634584094429 57334356954064362969035411)
      ·
        refine ⟨86001535431096544453553117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57334356954064362969035411 86001535431096544453553117)
        ·
          refine ⟨32250575786661204170082419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86001535431096544453553117 32250575786661204170082419)
          ·
            refine ⟨48375863679991806255123629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32250575786661204170082419 48375863679991806255123629)
            ·
              refine ⟨18140948879996927345671361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48375863679991806255123629 18140948879996927345671361)
              ·
                refine ⟨13605711659997695509253521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18140948879996927345671361 13605711659997695509253521)
                ·
                  refine ⟨10204283744998271631940141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13605711659997695509253521 10204283744998271631940141)
                  ·
                    refine ⟨3826606404374351861977553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10204283744998271631940141 3826606404374351861977553)
                    ·
                      refine ⟨2869954803280763896483165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826606404374351861977553 2869954803280763896483165)
                      ·
                        rfl

theorem cell23_5589217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_5589217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589217 prefixEnd_5589217 := by exact prefixLift 5589217
  have htrace : WordTrace (prefixWord ++ tailWord_5589217) baseStart_5589217 baseEnd_5589217 := by
    simpa [prefixWord, tailWord_5589217, baseEnd_5589217] using wordTrace_append hprefix tailTrace_5589217
  have hstable : (prefixWord ++ tailWord_5589217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589217).length < 2 ^ (prefixWord ++ tailWord_5589217).sum := by decide
  have hdescent : baseEnd_5589217 < baseStart_5589217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589218 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5589218 : Nat := 118140960795 + 5589218 * 2 ^ 59
def prefixEnd_5589218 : Nat := 4983230072969 + 3 ^ 40 * 5589218 * 2
def baseEnd_5589218 : Nat := 956651772253806130856887

theorem tailTrace_5589218 : CollatzResearch.WordTrace tailWord_5589218 prefixEnd_5589218 956651772253806130856887 := by
  unfold tailWord_5589218
  simp only [CollatzResearch.WordTrace]
  refine ⟨50963881966306305820728077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135903685243483482188608205 50963881966306305820728077)
  ·
    refine ⟨19111455737364864682773029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50963881966306305820728077 19111455737364864682773029)
    ·
      refine ⟨3583397950755912128019943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19111455737364864682773029 3583397950755912128019943)
      ·
        refine ⟨5375096926133868192029915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583397950755912128019943 5375096926133868192029915)
        ·
          refine ⟨8062645389200802288044873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375096926133868192029915 8062645389200802288044873)
          ·
            refine ⟨6046984041900601716033655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8062645389200802288044873 6046984041900601716033655)
            ·
              refine ⟨9070476062850902574050483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046984041900601716033655 9070476062850902574050483)
              ·
                refine ⟨13605714094276353861075725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9070476062850902574050483 13605714094276353861075725)
                ·
                  refine ⟨5102142785353632697903397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13605714094276353861075725 5102142785353632697903397)
                  ·
                    refine ⟨956651772253806130856887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102142785353632697903397 956651772253806130856887)
                    ·
                      rfl

theorem cell23_5589218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5589218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589218 prefixEnd_5589218 := by exact prefixLift 5589218
  have htrace : WordTrace (prefixWord ++ tailWord_5589218) baseStart_5589218 baseEnd_5589218 := by
    simpa [prefixWord, tailWord_5589218, baseEnd_5589218] using wordTrace_append hprefix tailTrace_5589218
  have hstable : (prefixWord ++ tailWord_5589218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589218).length < 2 ^ (prefixWord ++ tailWord_5589218).sum := by decide
  have hdescent : baseEnd_5589218 < baseStart_5589218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589224 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_5589224 : Nat := 118140960795 + 5589224 * 2 ^ 59
def prefixEnd_5589224 : Nat := 4983230072969 + 3 ^ 40 * 5589224 * 2
def baseEnd_5589224 : Nat := 2869958397645345369095633

theorem tailTrace_5589224 : CollatzResearch.WordTrace tailWord_5589224 prefixEnd_5589224 2869958397645345369095633 := by
  unfold tailWord_5589224
  simp only [CollatzResearch.WordTrace]
  refine ⟨101927873351601743153815363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135903831135468990871753817 101927873351601743153815363)
  ·
    refine ⟨152891810027402614730723045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101927873351601743153815363 152891810027402614730723045)
    ·
      refine ⟨28667214380137990262010571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152891810027402614730723045 28667214380137990262010571)
      ·
        refine ⟨43000821570206985393015857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28667214380137990262010571 43000821570206985393015857)
        ·
          refine ⟨32250616177655239044761893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43000821570206985393015857 32250616177655239044761893)
          ·
            refine ⟨6046990533310357320892855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32250616177655239044761893 6046990533310357320892855)
            ·
              refine ⟨9070485799965535981339283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046990533310357320892855 9070485799965535981339283)
              ·
                refine ⟨13605728699948303972008925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9070485799965535981339283 13605728699948303972008925)
                ·
                  refine ⟨5102148262480613989503347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13605728699948303972008925 5102148262480613989503347)
                  ·
                    refine ⟨7653222393720920984255021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5102148262480613989503347 7653222393720920984255021)
                    ·
                      refine ⟨2869958397645345369095633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7653222393720920984255021 2869958397645345369095633)
                      ·
                        rfl

theorem cell23_5589224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_5589224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589224 prefixEnd_5589224 := by exact prefixLift 5589224
  have htrace : WordTrace (prefixWord ++ tailWord_5589224) baseStart_5589224 baseEnd_5589224 := by
    simpa [prefixWord, tailWord_5589224, baseEnd_5589224] using wordTrace_append hprefix tailTrace_5589224
  have hstable : (prefixWord ++ tailWord_5589224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589224).length < 2 ^ (prefixWord ++ tailWord_5589224).sum := by decide
  have hdescent : baseEnd_5589224 < baseStart_5589224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589230 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_5589230 : Nat := 118140960795 + 5589230 * 2 ^ 59
def prefixEnd_5589230 : Nat := 4983230072969 + 3 ^ 40 * 5589230 * 2
def baseEnd_5589230 : Nat := 2869961478529272345620605

theorem tailTrace_5589230 : CollatzResearch.WordTrace tailWord_5589230 prefixEnd_5589230 2869961478529272345620605 := by
  unfold tailWord_5589230
  simp only [CollatzResearch.WordTrace]
  refine ⟨25481995692647718666543643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135903977027454499554899429 25481995692647718666543643)
  ·
    refine ⟨38222993538971577999815465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25481995692647718666543643 38222993538971577999815465)
    ·
      refine ⟨28667245154228683499861599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38222993538971577999815465 28667245154228683499861599)
      ·
        refine ⟨43000867731343025249792399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28667245154228683499861599 43000867731343025249792399)
        ·
          refine ⟨64501301597014537874688599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43000867731343025249792399 64501301597014537874688599)
          ·
            refine ⟨96751952395521806812032899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64501301597014537874688599 96751952395521806812032899)
            ·
              refine ⟨145127928593282710218049349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96751952395521806812032899 145127928593282710218049349)
              ·
                refine ⟨27211486611240508165884253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145127928593282710218049349 27211486611240508165884253)
                ·
                  refine ⟨10204307479215190562206595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27211486611240508165884253 10204307479215190562206595)
                  ·
                    refine ⟨15306461218822785843309893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10204307479215190562206595 15306461218822785843309893)
                    ·
                      refine ⟨2869961478529272345620605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15306461218822785843309893 2869961478529272345620605)
                      ·
                        rfl

theorem cell23_5589230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_5589230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589230 prefixEnd_5589230 := by exact prefixLift 5589230
  have htrace : WordTrace (prefixWord ++ tailWord_5589230) baseStart_5589230 baseEnd_5589230 := by
    simpa [prefixWord, tailWord_5589230, baseEnd_5589230] using wordTrace_append hprefix tailTrace_5589230
  have hstable : (prefixWord ++ tailWord_5589230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589230).length < 2 ^ (prefixWord ++ tailWord_5589230).sum := by decide
  have hdescent : baseEnd_5589230 < baseStart_5589230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589243 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4]
def baseStart_5589243 : Nat := 118140960795 + 5589243 * 2 ^ 59
def prefixEnd_5589243 : Nat := 4983230072969 + 3 ^ 40 * 5589243 * 2
def baseEnd_5589243 : Nat := 2869968153777780794758045

theorem tailTrace_5589243 : CollatzResearch.WordTrace tailWord_5589243 prefixEnd_5589243 2869968153777780794758045 := by
  unfold tailWord_5589243
  simp only [CollatzResearch.WordTrace]
  refine ⟨203856439690134652552572383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135904293126756435035048255 203856439690134652552572383)
  ·
    refine ⟨305784659535201978828858575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203856439690134652552572383 305784659535201978828858575)
    ·
      refine ⟨458676989302802968243287863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305784659535201978828858575 458676989302802968243287863)
      ·
        refine ⟨688015483954204452364931795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458676989302802968243287863 688015483954204452364931795)
        ·
          refine ⟨1032023225931306678547397693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688015483954204452364931795 1032023225931306678547397693)
          ·
            refine ⟨387008709724240004455274135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032023225931306678547397693 387008709724240004455274135)
            ·
              refine ⟨580513064586360006682911203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387008709724240004455274135 580513064586360006682911203)
              ·
                refine ⟨870769596879540010024366805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580513064586360006682911203 870769596879540010024366805)
                ·
                  refine ⟨20408662426864218984946097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 870769596879540010024366805 20408662426864218984946097)
                  ·
                    refine ⟨15306496820148164238709573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20408662426864218984946097 15306496820148164238709573)
                    ·
                      refine ⟨2869968153777780794758045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15306496820148164238709573 2869968153777780794758045)
                      ·
                        rfl

theorem cell23_5589243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_5589243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589243 prefixEnd_5589243 := by exact prefixLift 5589243
  have htrace : WordTrace (prefixWord ++ tailWord_5589243) baseStart_5589243 baseEnd_5589243 := by
    simpa [prefixWord, tailWord_5589243, baseEnd_5589243] using wordTrace_append hprefix tailTrace_5589243
  have hstable : (prefixWord ++ tailWord_5589243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589243).length < 2 ^ (prefixWord ++ tailWord_5589243).sum := by decide
  have hdescent : baseEnd_5589243 < baseStart_5589243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589247 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 5, 2, 2]
def baseStart_5589247 : Nat := 118140960795 + 5589247 * 2 ^ 59
def prefixEnd_5589247 : Nat := 4983230072969 + 3 ^ 40 * 5589247 * 2
def baseEnd_5589247 : Nat := 2869970207700398779108027

theorem tailTrace_5589247 : CollatzResearch.WordTrace tailWord_5589247 prefixEnd_5589247 2869970207700398779108027 := by
  unfold tailWord_5589247
  simp only [CollatzResearch.WordTrace]
  refine ⟨203856585582120161235717995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135904390388080107490478663 203856585582120161235717995)
  ·
    refine ⟨305784878373180241853576993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203856585582120161235717995 305784878373180241853576993)
    ·
      refine ⟨229338658779885181390182745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305784878373180241853576993 229338658779885181390182745)
      ·
        refine ⟨172003994084913886042637059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229338658779885181390182745 172003994084913886042637059)
        ·
          refine ⟨258005991127370829063955589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172003994084913886042637059 258005991127370829063955589)
          ·
            refine ⟨48376123336382030449491673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258005991127370829063955589 48376123336382030449491673)
            ·
              refine ⟨36282092502286522837118755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48376123336382030449491673 36282092502286522837118755)
              ·
                refine ⟨54423138753429784255678133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36282092502286522837118755 54423138753429784255678133)
                ·
                  refine ⟨5102169258134042273969825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54423138753429784255678133 5102169258134042273969825)
                  ·
                    refine ⟨3826626943600531705477369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5102169258134042273969825 3826626943600531705477369)
                    ·
                      refine ⟨2869970207700398779108027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826626943600531705477369 2869970207700398779108027)
                      ·
                        rfl

theorem cell23_5589247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_5589247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589247 prefixEnd_5589247 := by exact prefixLift 5589247
  have htrace : WordTrace (prefixWord ++ tailWord_5589247) baseStart_5589247 baseEnd_5589247 := by
    simpa [prefixWord, tailWord_5589247, baseEnd_5589247] using wordTrace_append hprefix tailTrace_5589247
  have hstable : (prefixWord ++ tailWord_5589247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589247).length < 2 ^ (prefixWord ++ tailWord_5589247).sum := by decide
  have hdescent : baseEnd_5589247 < baseStart_5589247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589260 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5589260 : Nat := 118140960795 + 5589260 * 2 ^ 59
def prefixEnd_5589260 : Nat := 4983230072969 + 3 ^ 40 * 5589260 * 2
def baseEnd_5589260 : Nat := 2869976882948907228245467

theorem tailTrace_5589260 : CollatzResearch.WordTrace tailWord_5589260 prefixEnd_5589260 2869976882948907228245467 := by
  unfold tailWord_5589260
  simp only [CollatzResearch.WordTrace]
  refine ⟨101928529865536532227970617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135904706487382042970627489 101928529865536532227970617)
  ·
    refine ⟨76446397399152399170977963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101928529865536532227970617 76446397399152399170977963)
    ·
      refine ⟨114669596098728598756466945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76446397399152399170977963 114669596098728598756466945)
      ·
        refine ⟨86002197074046449067350209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114669596098728598756466945 86002197074046449067350209)
        ·
          refine ⟨64501647805534836800512657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86002197074046449067350209 64501647805534836800512657)
          ·
            refine ⟨48376235854151127600384493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64501647805534836800512657 48376235854151127600384493)
            ·
              refine ⟨18141088445306672850144185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48376235854151127600384493 18141088445306672850144185)
              ·
                refine ⟨13605816333980004637608139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18141088445306672850144185 13605816333980004637608139)
                ·
                  refine ⟨20408724500970006956412209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13605816333980004637608139 20408724500970006956412209)
                  ·
                    refine ⟨15306543375727505217309157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20408724500970006956412209 15306543375727505217309157)
                    ·
                      refine ⟨2869976882948907228245467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15306543375727505217309157 2869976882948907228245467)
                      ·
                        rfl

theorem cell23_5589260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5589260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589260 prefixEnd_5589260 := by exact prefixLift 5589260
  have htrace : WordTrace (prefixWord ++ tailWord_5589260) baseStart_5589260 baseEnd_5589260 := by
    simpa [prefixWord, tailWord_5589260, baseEnd_5589260] using wordTrace_append hprefix tailTrace_5589260
  have hstable : (prefixWord ++ tailWord_5589260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589260).length < 2 ^ (prefixWord ++ tailWord_5589260).sum := by decide
  have hdescent : baseEnd_5589260 < baseStart_5589260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589274 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_5589274 : Nat := 118140960795 + 5589274 * 2 ^ 59
def prefixEnd_5589274 : Nat := 4983230072969 + 3 ^ 40 * 5589274 * 2
def baseEnd_5589274 : Nat := 956661357226023391156801

theorem tailTrace_5589274 : CollatzResearch.WordTrace tailWord_5589274 prefixEnd_5589274 956661357226023391156801 := by
  unfold tailWord_5589274
  simp only [CollatzResearch.WordTrace]
  refine ⟨50964392588255586211737719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135905046902014896564633917 50964392588255586211737719)
  ·
    refine ⟨76446588882383379317606579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50964392588255586211737719 76446588882383379317606579)
    ·
      refine ⟨114669883323575068976409869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76446588882383379317606579 114669883323575068976409869)
      ·
        refine ⟨43001206246340650866153701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114669883323575068976409869 43001206246340650866153701)
        ·
          refine ⟨8062726171188872037403819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43001206246340650866153701 8062726171188872037403819)
          ·
            refine ⟨12094089256783308056105729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062726171188872037403819 12094089256783308056105729)
            ·
              refine ⟨9070566942587481042079297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12094089256783308056105729 9070566942587481042079297)
              ·
                refine ⟨6802925206940610781559473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9070566942587481042079297 6802925206940610781559473)
                ·
                  refine ⟨5102193905205458086169605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6802925206940610781559473 5102193905205458086169605)
                  ·
                    refine ⟨956661357226023391156801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102193905205458086169605 956661357226023391156801)
                    ·
                      rfl

theorem cell23_5589274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_5589274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589274 prefixEnd_5589274 := by exact prefixLift 5589274
  have htrace : WordTrace (prefixWord ++ tailWord_5589274) baseStart_5589274 baseEnd_5589274 := by
    simpa [prefixWord, tailWord_5589274, baseEnd_5589274] using wordTrace_append hprefix tailTrace_5589274
  have hstable : (prefixWord ++ tailWord_5589274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589274).length < 2 ^ (prefixWord ++ tailWord_5589274).sum := by decide
  have hdescent : baseEnd_5589274 < baseStart_5589274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589283 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 9]
def baseStart_5589283 : Nat := 118140960795 + 5589283 * 2 ^ 59
def prefixEnd_5589283 : Nat := 4983230072969 + 3 ^ 40 * 5589283 * 2
def baseEnd_5589283 : Nat := 956662897667986879419287

theorem tailTrace_5589283 : CollatzResearch.WordTrace tailWord_5589283 prefixEnd_5589283 956662897667986879419287 := by
  unfold tailWord_5589283
  simp only [CollatzResearch.WordTrace]
  refine ⟨203857898609989739384028503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135905265739993159589352335 203857898609989739384028503)
  ·
    refine ⟨305786847914984609076042755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203857898609989739384028503 305786847914984609076042755)
    ·
      refine ⟨458680271872476913614064133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305786847914984609076042755 458680271872476913614064133)
      ·
        refine ⟨86002550976089421302637025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 458680271872476913614064133 86002550976089421302637025)
        ·
          refine ⟨64501913232067065976977769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86002550976089421302637025 64501913232067065976977769)
          ·
            refine ⟨48376434924050299482733327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64501913232067065976977769 48376434924050299482733327)
            ·
              refine ⟨72564652386075449224099991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48376434924050299482733327 72564652386075449224099991)
              ·
                refine ⟨108846978579113173836149987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72564652386075449224099991 108846978579113173836149987)
                ·
                  refine ⟨163270467868669760754224981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108846978579113173836149987 163270467868669760754224981)
                  ·
                    refine ⟨956662897667986879419287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 163270467868669760754224981 956662897667986879419287)
                    ·
                      rfl

theorem cell23_5589283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_5589283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589283 prefixEnd_5589283 := by exact prefixLift 5589283
  have htrace : WordTrace (prefixWord ++ tailWord_5589283) baseStart_5589283 baseEnd_5589283 := by
    simpa [prefixWord, tailWord_5589283, baseEnd_5589283] using wordTrace_append hprefix tailTrace_5589283
  have hstable : (prefixWord ++ tailWord_5589283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589283).length < 2 ^ (prefixWord ++ tailWord_5589283).sum := by decide
  have hdescent : baseEnd_5589283 < baseStart_5589283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589324 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 1, 3, 2]
def baseStart_5589324 : Nat := 118140960795 + 5589324 * 2 ^ 59
def prefixEnd_5589324 : Nat := 4983230072969 + 3 ^ 40 * 5589324 * 2
def baseEnd_5589324 : Nat := 2870009745710794977845173

theorem tailTrace_5589324 : CollatzResearch.WordTrace tailWord_5589324 prefixEnd_5589324 2870009745710794977845173 := by
  unfold tailWord_5589324
  simp only [CollatzResearch.WordTrace]
  refine ⟨101929697001420601693135513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135906262668560802257514017 101929697001420601693135513)
  ·
    refine ⟨76447272751065451269851635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101929697001420601693135513 76447272751065451269851635)
    ·
      refine ⟨114670909126598176904777453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76447272751065451269851635 114670909126598176904777453)
      ·
        refine ⟨43001590922474316339291545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114670909126598176904777453 43001590922474316339291545)
        ·
          refine ⟨32251193191855737254468659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43001590922474316339291545 32251193191855737254468659)
          ·
            refine ⟨48376789787783605881702989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32251193191855737254468659 48376789787783605881702989)
            ·
              refine ⟨18141296170418852205638621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48376789787783605881702989 18141296170418852205638621)
              ·
                refine ⟨6802986063907069577114483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18141296170418852205638621 6802986063907069577114483)
                ·
                  refine ⟨10204479095860604365671725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6802986063907069577114483 10204479095860604365671725)
                  ·
                    refine ⟨3826679660947726637126897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10204479095860604365671725 3826679660947726637126897)
                    ·
                      refine ⟨2870009745710794977845173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826679660947726637126897 2870009745710794977845173)
                      ·
                        rfl

theorem cell23_5589324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_5589324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589324 prefixEnd_5589324 := by exact prefixLift 5589324
  have htrace : WordTrace (prefixWord ++ tailWord_5589324) baseStart_5589324 baseEnd_5589324 := by
    simpa [prefixWord, tailWord_5589324, baseEnd_5589324] using wordTrace_append hprefix tailTrace_5589324
  have hstable : (prefixWord ++ tailWord_5589324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589324).length < 2 ^ (prefixWord ++ tailWord_5589324).sum := by decide
  have hdescent : baseEnd_5589324 < baseStart_5589324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589330 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_5589330 : Nat := 118140960795 + 5589330 * 2 ^ 59
def prefixEnd_5589330 : Nat := 4983230072969 + 3 ^ 40 * 5589330 * 2
def baseEnd_5589330 : Nat := 956670942198240651456715

theorem tailTrace_5589330 : CollatzResearch.WordTrace tailWord_5589330 prefixEnd_5589330 956670942198240651456715 := by
  unfold tailWord_5589330
  simp only [CollatzResearch.WordTrace]
  refine ⟨50964903210204866602747361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135906408560546310940659629 50964903210204866602747361)
  ·
    refine ⟨38223677407653649952060521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50964903210204866602747361 38223677407653649952060521)
    ·
      refine ⟨28667758055740237464045391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38223677407653649952060521 28667758055740237464045391)
      ·
        refine ⟨43001637083610356196068087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28667758055740237464045391 43001637083610356196068087)
        ·
          refine ⟨64502455625415534294102131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43001637083610356196068087 64502455625415534294102131)
          ·
            refine ⟨96753683438123301441153197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64502455625415534294102131 96753683438123301441153197)
            ·
              refine ⟨36282631289296238040432449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96753683438123301441153197 36282631289296238040432449)
              ·
                refine ⟨27211973466972178530324337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36282631289296238040432449 27211973466972178530324337)
                ·
                  refine ⟨20408980100229133897743253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27211973466972178530324337 20408980100229133897743253)
                  ·
                    refine ⟨956670942198240651456715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20408980100229133897743253 956670942198240651456715)
                    ·
                      rfl

theorem cell23_5589330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_5589330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589330 prefixEnd_5589330 := by exact prefixLift 5589330
  have htrace : WordTrace (prefixWord ++ tailWord_5589330) baseStart_5589330 baseEnd_5589330 := by
    simpa [prefixWord, tailWord_5589330, baseEnd_5589330] using wordTrace_append hprefix tailTrace_5589330
  have hstable : (prefixWord ++ tailWord_5589330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589330).length < 2 ^ (prefixWord ++ tailWord_5589330).sum := by decide
  have hdescent : baseEnd_5589330 < baseStart_5589330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589342 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5589342 : Nat := 118140960795 + 5589342 * 2 ^ 59
def prefixEnd_5589342 : Nat := 4983230072969 + 3 ^ 40 * 5589342 * 2
def baseEnd_5589342 : Nat := 956672996120858635806697

theorem tailTrace_5589342 : CollatzResearch.WordTrace tailWord_5589342 prefixEnd_5589342 956672996120858635806697 := by
  unfold tailWord_5589342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25482506314596999057553285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135906700344517328306950853 25482506314596999057553285)
  ·
    refine ⟨4777969933986937323291241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25482506314596999057553285 4777969933986937323291241)
    ·
      refine ⟨3583477450490202992468431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4777969933986937323291241 3583477450490202992468431)
      ·
        refine ⟨5375216175735304488702647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583477450490202992468431 5375216175735304488702647)
        ·
          refine ⟨8062824263602956733053971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375216175735304488702647 8062824263602956733053971)
          ·
            refine ⟨12094236395404435099580957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062824263602956733053971 12094236395404435099580957)
            ·
              refine ⟨4535338648276663162342859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12094236395404435099580957 4535338648276663162342859)
              ·
                refine ⟨6803007972414994743514289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535338648276663162342859 6803007972414994743514289)
                ·
                  refine ⟨5102255979311246057635717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803007972414994743514289 5102255979311246057635717)
                  ·
                    refine ⟨956672996120858635806697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102255979311246057635717 956672996120858635806697)
                    ·
                      rfl

theorem cell23_5589342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5589342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589342 prefixEnd_5589342 := by exact prefixLift 5589342
  have htrace : WordTrace (prefixWord ++ tailWord_5589342) baseStart_5589342 baseEnd_5589342 := by
    simpa [prefixWord, tailWord_5589342, baseEnd_5589342] using wordTrace_append hprefix tailTrace_5589342
  have hstable : (prefixWord ++ tailWord_5589342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589342).length < 2 ^ (prefixWord ++ tailWord_5589342).sum := by decide
  have hdescent : baseEnd_5589342 < baseStart_5589342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589360 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 7]
def baseStart_5589360 : Nat := 118140960795 + 5589360 * 2 ^ 59
def prefixEnd_5589360 : Nat := 4983230072969 + 3 ^ 40 * 5589360 * 2
def baseEnd_5589360 : Nat := 318892025668261870777223

theorem tailTrace_5589360 : CollatzResearch.WordTrace tailWord_5589360 prefixEnd_5589360 318892025668261870777223 := by
  unfold tailWord_5589360
  simp only [CollatzResearch.WordTrace]
  refine ⟨101930353515355390767290767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135907138020473854356387689 101930353515355390767290767)
  ·
    refine ⟨152895530273033086150936151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101930353515355390767290767 152895530273033086150936151)
    ·
      refine ⟨229343295409549629226404227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152895530273033086150936151 229343295409549629226404227)
      ·
        refine ⟨344014943114324443839606341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229343295409549629226404227 344014943114324443839606341)
        ·
          refine ⟨64502801833935833219926189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344014943114324443839606341 64502801833935833219926189)
          ·
            refine ⟨24188550687725937457472321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64502801833935833219926189 24188550687725937457472321)
            ·
              refine ⟨18141413015794453093104241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24188550687725937457472321 18141413015794453093104241)
              ·
                refine ⟨13606059761845839819828181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18141413015794453093104241 13606059761845839819828181)
                ·
                  refine ⟨318892025668261870777223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13606059761845839819828181 318892025668261870777223)
                  ·
                    rfl

theorem cell23_5589360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_5589360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589360 prefixEnd_5589360 := by exact prefixLift 5589360
  have htrace : WordTrace (prefixWord ++ tailWord_5589360) baseStart_5589360 baseEnd_5589360 := by
    simpa [prefixWord, tailWord_5589360, baseEnd_5589360] using wordTrace_append hprefix tailTrace_5589360
  have hstable : (prefixWord ++ tailWord_5589360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589360).length < 2 ^ (prefixWord ++ tailWord_5589360).sum := by decide
  have hdescent : baseEnd_5589360 < baseStart_5589360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589397 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_5589397 : Nat := 118140960795 + 5589397 * 2 ^ 59
def prefixEnd_5589397 : Nat := 4983230072969 + 3 ^ 40 * 5589397 * 2
def baseEnd_5589397 : Nat := 2870047229798573192232337

theorem tailTrace_5589397 : CollatzResearch.WordTrace tailWord_5589397 prefixEnd_5589397 2870047229798573192232337 := by
  unfold tailWord_5589397
  simp only [CollatzResearch.WordTrace]
  refine ⟨203862056531576736853678445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135908037687717824569118963 203862056531576736853678445)
  ·
    refine ⟨76448271199341276320129417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203862056531576736853678445 76448271199341276320129417)
    ·
      refine ⟨57336203399505957240097063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76448271199341276320129417 57336203399505957240097063)
      ·
        refine ⟨86004305099258935860145595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57336203399505957240097063 86004305099258935860145595)
        ·
          refine ⟨129006457648888403790218393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86004305099258935860145595 129006457648888403790218393)
          ·
            refine ⟨96754843236666302842663795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129006457648888403790218393 96754843236666302842663795)
            ·
              refine ⟨145132264854999454263995693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96754843236666302842663795 145132264854999454263995693)
              ·
                refine ⟨54424599320624795348998385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145132264854999454263995693 54424599320624795348998385)
                ·
                  refine ⟨40818449490468596511748789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54424599320624795348998385 40818449490468596511748789)
                  ·
                    refine ⟨3826729639731430922976449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40818449490468596511748789 3826729639731430922976449)
                    ·
                      refine ⟨2870047229798573192232337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826729639731430922976449 2870047229798573192232337)
                      ·
                        rfl

theorem cell23_5589397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_5589397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589397 prefixEnd_5589397 := by exact prefixLift 5589397
  have htrace : WordTrace (prefixWord ++ tailWord_5589397) baseStart_5589397 baseEnd_5589397 := by
    simpa [prefixWord, tailWord_5589397, baseEnd_5589397] using wordTrace_append hprefix tailTrace_5589397
  have hstable : (prefixWord ++ tailWord_5589397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589397).length < 2 ^ (prefixWord ++ tailWord_5589397).sum := by decide
  have hdescent : baseEnd_5589397 < baseStart_5589397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589405 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_5589405 : Nat := 118140960795 + 5589405 * 2 ^ 59
def prefixEnd_5589405 : Nat := 4983230072969 + 3 ^ 40 * 5589405 * 2
def baseEnd_5589405 : Nat := 2870051337643809160932301

theorem tailTrace_5589405 : CollatzResearch.WordTrace tailWord_5589405 prefixEnd_5589405 2870051337643809160932301 := by
  unfold tailWord_5589405
  simp only [CollatzResearch.WordTrace]
  refine ⟨203862348315547754219969669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135908232210365169479979779 203862348315547754219969669)
  ·
    refine ⟨38224190309165203916244313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203862348315547754219969669 38224190309165203916244313)
    ·
      refine ⟨28668142731873902937183235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38224190309165203916244313 28668142731873902937183235)
      ·
        refine ⟨43002214097810854405774853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28668142731873902937183235 43002214097810854405774853)
        ·
          refine ⟨8062915143339535201082785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43002214097810854405774853 8062915143339535201082785)
          ·
            refine ⟨6047186357504651400812089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8062915143339535201082785 6047186357504651400812089)
            ·
              refine ⟨4535389768128488550609067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6047186357504651400812089 4535389768128488550609067)
              ·
                refine ⟨6803084652192732825913601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535389768128488550609067 6803084652192732825913601)
                ·
                  refine ⟨5102313489144549619435201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803084652192732825913601 5102313489144549619435201)
                  ·
                    refine ⟨3826735116858412214576401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5102313489144549619435201 3826735116858412214576401)
                    ·
                      refine ⟨2870051337643809160932301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826735116858412214576401 2870051337643809160932301)
                      ·
                        rfl

theorem cell23_5589405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_5589405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589405 prefixEnd_5589405 := by exact prefixLift 5589405
  have htrace : WordTrace (prefixWord ++ tailWord_5589405) baseStart_5589405 baseEnd_5589405 := by
    simpa [prefixWord, tailWord_5589405, baseEnd_5589405] using wordTrace_append hprefix tailTrace_5589405
  have hstable : (prefixWord ++ tailWord_5589405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589405).length < 2 ^ (prefixWord ++ tailWord_5589405).sum := by decide
  have hdescent : baseEnd_5589405 < baseStart_5589405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589427 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 6, 4, 2]
def baseStart_5589427 : Nat := 118140960795 + 5589427 * 2 ^ 59
def prefixEnd_5589427 : Nat := 4983230072969 + 3 ^ 40 * 5589427 * 2
def baseEnd_5589427 : Nat := 2870062634218208074857199

theorem tailTrace_5589427 : CollatzResearch.WordTrace tailWord_5589427 prefixEnd_5589427 2870062634218208074857199 := by
  unfold tailWord_5589427
  simp only [CollatzResearch.WordTrace]
  refine ⟨203863150721468051977270535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135908767147645367984847023 203863150721468051977270535)
  ·
    refine ⟨305794726082202077965905803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203863150721468051977270535 305794726082202077965905803)
    ·
      refine ⟨458692089123303116948858705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305794726082202077965905803 458692089123303116948858705)
      ·
        refine ⟨344019066842477337711644029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458692089123303116948858705 344019066842477337711644029)
        ·
          refine ⟨129007150065929001641866511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344019066842477337711644029 129007150065929001641866511)
          ·
            refine ⟨193510725098893502462799767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129007150065929001641866511 193510725098893502462799767)
            ·
              refine ⟨290266087648340253694199651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193510725098893502462799767 290266087648340253694199651)
              ·
                refine ⟨435399131472510380541299477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290266087648340253694199651 435399131472510380541299477)
                ·
                  refine ⟨20409334287773924087873413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 435399131472510380541299477 20409334287773924087873413)
                  ·
                    refine ⟨3826750178957610766476265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20409334287773924087873413 3826750178957610766476265)
                    ·
                      refine ⟨2870062634218208074857199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826750178957610766476265 2870062634218208074857199)
                      ·
                        rfl

theorem cell23_5589427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4, 2].length) (baseStart_5589427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589427 prefixEnd_5589427 := by exact prefixLift 5589427
  have htrace : WordTrace (prefixWord ++ tailWord_5589427) baseStart_5589427 baseEnd_5589427 := by
    simpa [prefixWord, tailWord_5589427, baseEnd_5589427] using wordTrace_append hprefix tailTrace_5589427
  have hstable : (prefixWord ++ tailWord_5589427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589427).length < 2 ^ (prefixWord ++ tailWord_5589427).sum := by decide
  have hdescent : baseEnd_5589427 < baseStart_5589427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589440 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_5589440 : Nat := 118140960795 + 5589440 * 2 ^ 59
def prefixEnd_5589440 : Nat := 4983230072969 + 3 ^ 40 * 5589440 * 2
def baseEnd_5589440 : Nat := 2870069309466716523994639

theorem tailTrace_5589440 : CollatzResearch.WordTrace tailWord_5589440 prefixEnd_5589440 2870069309466716523994639 := by
  unfold tailWord_5589440
  simp only [CollatzResearch.WordTrace]
  refine ⟨101931812435210477598746887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135909083246947303464995849 101931812435210477598746887)
  ·
    refine ⟨152897718652815716398120331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101931812435210477598746887 152897718652815716398120331)
    ·
      refine ⟨229346577979223574597180497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152897718652815716398120331 229346577979223574597180497)
      ·
        refine ⟨172009933484417680947885373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229346577979223574597180497 172009933484417680947885373)
        ·
          refine ⟨64503725056656630355457015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172009933484417680947885373 64503725056656630355457015)
          ·
            refine ⟨96755587584984945533185523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64503725056656630355457015 96755587584984945533185523)
            ·
              refine ⟨145133381377477418299778285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96755587584984945533185523 145133381377477418299778285)
              ·
                refine ⟨54425018016554031862416857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145133381377477418299778285 54425018016554031862416857)
                ·
                  refine ⟨40818763512415523896812643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54425018016554031862416857 40818763512415523896812643)
                  ·
                    refine ⟨61228145268623285845218965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40818763512415523896812643 61228145268623285845218965)
                    ·
                      refine ⟨2870069309466716523994639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61228145268623285845218965 2870069309466716523994639)
                      ·
                        rfl

theorem cell23_5589440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_5589440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589440 prefixEnd_5589440 := by exact prefixLift 5589440
  have htrace : WordTrace (prefixWord ++ tailWord_5589440) baseStart_5589440 baseEnd_5589440 := by
    simpa [prefixWord, tailWord_5589440, baseEnd_5589440] using wordTrace_append hprefix tailTrace_5589440
  have hstable : (prefixWord ++ tailWord_5589440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589440).length < 2 ^ (prefixWord ++ tailWord_5589440).sum := by decide
  have hdescent : baseEnd_5589440 < baseStart_5589440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589537 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5589537 : Nat := 118140960795 + 5589537 * 2 ^ 59
def prefixEnd_5589537 : Nat := 4983230072969 + 3 ^ 40 * 5589537 * 2
def baseEnd_5589537 : Nat := 2870119117090202644481693

theorem tailTrace_5589537 : CollatzResearch.WordTrace tailWord_5589537 prefixEnd_5589537 2870119117090202644481693 := by
  unfold tailWord_5589537
  simp only [CollatzResearch.WordTrace]
  refine ⟨203867162751069540763774865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135911441834046360509183243 203867162751069540763774865)
  ·
    refine ⟨152900372063302155572831149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203867162751069540763774865 152900372063302155572831149)
    ·
      refine ⟨57337639523738308339811681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152900372063302155572831149 57337639523738308339811681)
      ·
        refine ⟨43003229642803731254858761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57337639523738308339811681 43003229642803731254858761)
        ·
          refine ⟨32252422232102798441144071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43003229642803731254858761 32252422232102798441144071)
          ·
            refine ⟨48378633348154197661716107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32252422232102798441144071 48378633348154197661716107)
            ·
              refine ⟨72567950022231296492574161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48378633348154197661716107 72567950022231296492574161)
              ·
                refine ⟨54425962516673472369430621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72567950022231296492574161 54425962516673472369430621)
                ·
                  refine ⟨20409735943752552138536483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54425962516673472369430621 20409735943752552138536483)
                  ·
                    refine ⟨30614603915628828207804725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20409735943752552138536483 30614603915628828207804725)
                    ·
                      refine ⟨2870119117090202644481693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30614603915628828207804725 2870119117090202644481693)
                      ·
                        rfl

theorem cell23_5589537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5589537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589537 prefixEnd_5589537 := by exact prefixLift 5589537
  have htrace : WordTrace (prefixWord ++ tailWord_5589537) baseStart_5589537 baseEnd_5589537 := by
    simpa [prefixWord, tailWord_5589537, baseEnd_5589537] using wordTrace_append hprefix tailTrace_5589537
  have hstable : (prefixWord ++ tailWord_5589537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589537).length < 2 ^ (prefixWord ++ tailWord_5589537).sum := by decide
  have hdescent : baseEnd_5589537 < baseStart_5589537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589547 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4]
def baseStart_5589547 : Nat := 118140960795 + 5589547 * 2 ^ 59
def prefixEnd_5589547 : Nat := 4983230072969 + 3 ^ 40 * 5589547 * 2
def baseEnd_5589547 : Nat := 2870124251896747605356647

theorem tailTrace_5589547 : CollatzResearch.WordTrace tailWord_5589547 prefixEnd_5589547 2870124251896747605356647 := by
  unfold tailWord_5589547
  simp only [CollatzResearch.WordTrace]
  refine ⟨203867527481033312471638895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135911684987355541647759263 203867527481033312471638895)
  ·
    refine ⟨305801291221549968707458343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203867527481033312471638895 305801291221549968707458343)
    ·
      refine ⟨458701936832324953061187515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305801291221549968707458343 458701936832324953061187515)
      ·
        refine ⟨688052905248487429591781273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458701936832324953061187515 688052905248487429591781273)
        ·
          refine ⟨516039678936365572193835955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688052905248487429591781273 516039678936365572193835955)
          ·
            refine ⟨774059518404548358290753933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516039678936365572193835955 774059518404548358290753933)
            ·
              refine ⟨290272319401705634359032725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 774059518404548358290753933 290272319401705634359032725)
              ·
                refine ⟨13606514971954951610579659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290272319401705634359032725 13606514971954951610579659)
                ·
                  refine ⟨20409772457932427415869489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13606514971954951610579659 20409772457932427415869489)
                  ·
                    refine ⟨15307329343449320561902117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20409772457932427415869489 15307329343449320561902117)
                    ·
                      refine ⟨2870124251896747605356647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15307329343449320561902117 2870124251896747605356647)
                      ·
                        rfl

theorem cell23_5589547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].length) (baseStart_5589547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589547 prefixEnd_5589547 := by exact prefixLift 5589547
  have htrace : WordTrace (prefixWord ++ tailWord_5589547) baseStart_5589547 baseEnd_5589547 := by
    simpa [prefixWord, tailWord_5589547, baseEnd_5589547] using wordTrace_append hprefix tailTrace_5589547
  have hstable : (prefixWord ++ tailWord_5589547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589547).length < 2 ^ (prefixWord ++ tailWord_5589547).sum := by decide
  have hdescent : baseEnd_5589547 < baseStart_5589547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589568 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 1, 2, 2]
def baseStart_5589568 : Nat := 118140960795 + 5589568 * 2 ^ 59
def prefixEnd_5589568 : Nat := 4983230072969 + 3 ^ 40 * 5589568 * 2
def baseEnd_5589568 : Nat := 2870135034990492023194051

theorem tailTrace_5589568 : CollatzResearch.WordTrace tailWord_5589568 prefixEnd_5589568 2870135034990492023194051 := by
  unfold tailWord_5589568
  simp only [CollatzResearch.WordTrace]
  refine ⟨101934146706978616529076679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135912195609304822038768905 101934146706978616529076679)
  ·
    refine ⟨152901220060467924793615019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101934146706978616529076679 152901220060467924793615019)
    ·
      refine ⟨229351830090701887190422529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152901220060467924793615019 229351830090701887190422529)
      ·
        refine ⟨172013872568026415392816897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229351830090701887190422529 172013872568026415392816897)
        ·
          refine ⟨129010404426019811544612673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172013872568026415392816897 129010404426019811544612673)
          ·
            refine ⟨96757803319514858658459505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129010404426019811544612673 96757803319514858658459505)
            ·
              refine ⟨72568352489636143993844629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96757803319514858658459505 72568352489636143993844629)
              ·
                refine ⟨3401641522951694249711467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72568352489636143993844629 3401641522951694249711467)
                ·
                  refine ⟨5102462284427541374567201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401641522951694249711467 5102462284427541374567201)
                  ·
                    refine ⟨3826846713320656030925401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5102462284427541374567201 3826846713320656030925401)
                    ·
                      refine ⟨2870135034990492023194051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826846713320656030925401 2870135034990492023194051)
                      ·
                        rfl

theorem cell23_5589568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_5589568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589568 prefixEnd_5589568 := by exact prefixLift 5589568
  have htrace : WordTrace (prefixWord ++ tailWord_5589568) baseStart_5589568 baseEnd_5589568 := by
    simpa [prefixWord, tailWord_5589568, baseEnd_5589568] using wordTrace_append hprefix tailTrace_5589568
  have hstable : (prefixWord ++ tailWord_5589568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589568).length < 2 ^ (prefixWord ++ tailWord_5589568).sum := by decide
  have hdescent : baseEnd_5589568 < baseStart_5589568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589578 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_5589578 : Nat := 118140960795 + 5589578 * 2 ^ 59
def prefixEnd_5589578 : Nat := 4983230072969 + 3 ^ 40 * 5589578 * 2
def baseEnd_5589578 : Nat := 956713389932345661356335

theorem tailTrace_5589578 : CollatzResearch.WordTrace tailWord_5589578 prefixEnd_5589578 956713389932345661356335 := by
  unfold tailWord_5589578
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967164535980251191504347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135912438762614003177344925 50967164535980251191504347)
  ·
    refine ⟨76450746803970376787256521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50967164535980251191504347 76450746803970376787256521)
    ·
      refine ⟨57338060102977782590442391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76450746803970376787256521 57338060102977782590442391)
      ·
        refine ⟨86007090154466673885663587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57338060102977782590442391 86007090154466673885663587)
        ·
          refine ⟨129010635231700010828495381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86007090154466673885663587 129010635231700010828495381)
          ·
            refine ⟨6047373526485938007585721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129010635231700010828495381 6047373526485938007585721)
            ·
              refine ⟨4535530144864453505689291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6047373526485938007585721 4535530144864453505689291)
              ·
                refine ⟨6803295217296680258533937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535530144864453505689291 6803295217296680258533937)
                ·
                  refine ⟨5102471412972510193900453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803295217296680258533937 5102471412972510193900453)
                  ·
                    refine ⟨956713389932345661356335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102471412972510193900453 956713389932345661356335)
                    ·
                      rfl

theorem cell23_5589578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_5589578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589578 prefixEnd_5589578 := by exact prefixLift 5589578
  have htrace : WordTrace (prefixWord ++ tailWord_5589578) baseStart_5589578 baseEnd_5589578 := by
    simpa [prefixWord, tailWord_5589578, baseEnd_5589578] using wordTrace_append hprefix tailTrace_5589578
  have hstable : (prefixWord ++ tailWord_5589578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589578).length < 2 ^ (prefixWord ++ tailWord_5589578).sum := by decide
  have hdescent : baseEnd_5589578 < baseStart_5589578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589584 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 6, 1, 3]
def baseStart_5589584 : Nat := 118140960795 + 5589584 * 2 ^ 59
def prefixEnd_5589584 : Nat := 4983230072969 + 3 ^ 40 * 5589584 * 2
def baseEnd_5589584 : Nat := 2870143250680963960593977

theorem tailTrace_5589584 : CollatzResearch.WordTrace tailWord_5589584 prefixEnd_5589584 2870143250680963960593977 := by
  unfold tailWord_5589584
  simp only [CollatzResearch.WordTrace]
  refine ⟨101934438490949633895367903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135912584654599511860490537 101934438490949633895367903)
  ·
    refine ⟨152901657736424450843051855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101934438490949633895367903 152901657736424450843051855)
    ·
      refine ⟨229352486604636676264577783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152901657736424450843051855 229352486604636676264577783)
      ·
        refine ⟨344028729906955014396866675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229352486604636676264577783 344028729906955014396866675)
        ·
          refine ⟨516043094860432521595300013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344028729906955014396866675 516043094860432521595300013)
          ·
            refine ⟨193516160572662195598237505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516043094860432521595300013 193516160572662195598237505)
            ·
              refine ⟨145137120429496646698678129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193516160572662195598237505 145137120429496646698678129)
              ·
                refine ⟨108852840322122485024008597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145137120429496646698678129 108852840322122485024008597)
                ·
                  refine ⟨5102476890099491485500403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108852840322122485024008597 5102476890099491485500403)
                  ·
                    refine ⟨7653715335149237228250605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5102476890099491485500403 7653715335149237228250605)
                    ·
                      refine ⟨2870143250680963960593977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7653715335149237228250605 2870143250680963960593977)
                      ·
                        rfl

theorem cell23_5589584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_5589584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589584 prefixEnd_5589584 := by exact prefixLift 5589584
  have htrace : WordTrace (prefixWord ++ tailWord_5589584) baseStart_5589584 baseEnd_5589584 := by
    simpa [prefixWord, tailWord_5589584, baseEnd_5589584] using wordTrace_append hprefix tailTrace_5589584
  have hstable : (prefixWord ++ tailWord_5589584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589584).length < 2 ^ (prefixWord ++ tailWord_5589584).sum := by decide
  have hdescent : baseEnd_5589584 < baseStart_5589584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589588 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_5589588 : Nat := 118140960795 + 5589588 * 2 ^ 59
def prefixEnd_5589588 : Nat := 4983230072969 + 3 ^ 40 * 5589588 * 2
def baseEnd_5589588 : Nat := 2870145304603581944943959

theorem tailTrace_5589588 : CollatzResearch.WordTrace tailWord_5589588 prefixEnd_5589588 2870145304603581944943959 := by
  unfold tailWord_5589588
  simp only [CollatzResearch.WordTrace]
  refine ⟨101934511436942388236940709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135912681915923184315920945 101934511436942388236940709)
  ·
    refine ⟨19112720894426697794426383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101934511436942388236940709 19112720894426697794426383)
    ·
      refine ⟨28669081341640046691639575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19112720894426697794426383 28669081341640046691639575)
      ·
        refine ⟨43003622012460070037459363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28669081341640046691639575 43003622012460070037459363)
        ·
          refine ⟨64505433018690105056189045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43003622012460070037459363 64505433018690105056189045)
          ·
            refine ⟨6047384345502197349017723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64505433018690105056189045 6047384345502197349017723)
            ·
              refine ⟨9071076518253296023526585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6047384345502197349017723 9071076518253296023526585)
              ·
                refine ⟨6803307388689972017644939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9071076518253296023526585 6803307388689972017644939)
                ·
                  refine ⟨10204961083034958026467409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6803307388689972017644939 10204961083034958026467409)
                  ·
                    refine ⟨7653720812276218519850557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10204961083034958026467409 7653720812276218519850557)
                    ·
                      refine ⟨2870145304603581944943959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7653720812276218519850557 2870145304603581944943959)
                      ·
                        rfl

theorem cell23_5589588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_5589588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589588 prefixEnd_5589588 := by exact prefixLift 5589588
  have htrace : WordTrace (prefixWord ++ tailWord_5589588) baseStart_5589588 baseEnd_5589588 := by
    simpa [prefixWord, tailWord_5589588, baseEnd_5589588] using wordTrace_append hprefix tailTrace_5589588
  have hstable : (prefixWord ++ tailWord_5589588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589588).length < 2 ^ (prefixWord ++ tailWord_5589588).sum := by decide
  have hdescent : baseEnd_5589588 < baseStart_5589588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589627 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5]
def baseStart_5589627 : Nat := 118140960795 + 5589627 * 2 ^ 59
def prefixEnd_5589627 : Nat := 4983230072969 + 3 ^ 40 * 5589627 * 2
def baseEnd_5589627 : Nat := 2870165330349107292356279

theorem tailTrace_5589627 : CollatzResearch.WordTrace tailWord_5589627 prefixEnd_5589627 2870165330349107292356279 := by
  unfold tailWord_5589627
  simp only [CollatzResearch.WordTrace]
  refine ⟨203870445320743486134551135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135913630213828990756367423 203870445320743486134551135)
  ·
    refine ⟨305805667981115229201826703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203870445320743486134551135 305805667981115229201826703)
    ·
      refine ⟨458708501971672843802740055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305805667981115229201826703 458708501971672843802740055)
      ·
        refine ⟨688062752957509265704110083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458708501971672843802740055 688062752957509265704110083)
        ·
          refine ⟨1032094129436263898556165125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688062752957509265704110083 1032094129436263898556165125)
          ·
            refine ⟨193517649269299480979280961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1032094129436263898556165125 193517649269299480979280961)
            ·
              refine ⟨145138236951974610734460721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193517649269299480979280961 145138236951974610734460721)
              ·
                refine ⟨108853677713980958050845541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145138236951974610734460721 108853677713980958050845541)
                ·
                  refine ⟨20410064571371429634533539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108853677713980958050845541 20410064571371429634533539)
                  ·
                    refine ⟨30615096857057144451800309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20410064571371429634533539 30615096857057144451800309)
                    ·
                      refine ⟨2870165330349107292356279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30615096857057144451800309 2870165330349107292356279)
                      ·
                        rfl

theorem cell23_5589627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_5589627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589627 prefixEnd_5589627 := by exact prefixLift 5589627
  have htrace : WordTrace (prefixWord ++ tailWord_5589627) baseStart_5589627 baseEnd_5589627 := by
    simpa [prefixWord, tailWord_5589627, baseEnd_5589627] using wordTrace_append hprefix tailTrace_5589627
  have hstable : (prefixWord ++ tailWord_5589627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589627).length < 2 ^ (prefixWord ++ tailWord_5589627).sum := by decide
  have hdescent : baseEnd_5589627 < baseStart_5589627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589641 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 6, 2, 2]
def baseStart_5589641 : Nat := 118140960795 + 5589641 * 2 ^ 59
def prefixEnd_5589641 : Nat := 4983230072969 + 3 ^ 40 * 5589641 * 2
def baseEnd_5589641 : Nat := 2870172519078270237581215

theorem tailTrace_5589641 : CollatzResearch.WordTrace tailWord_5589641 prefixEnd_5589641 2870172519078270237581215 := by
  unfold tailWord_5589641
  simp only [CollatzResearch.WordTrace]
  refine ⟨203870955942692766525560777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135913970628461844350373851 203870955942692766525560777)
  ·
    refine ⟨152903216957019574894170583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203870955942692766525560777 152903216957019574894170583)
    ·
      refine ⟨229354825435529362341255875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152903216957019574894170583 229354825435529362341255875)
      ·
        refine ⟨344032238153294043511883813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229354825435529362341255875 344032238153294043511883813)
        ·
          refine ⟨64506044653742633158478215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344032238153294043511883813 64506044653742633158478215)
          ·
            refine ⟨96759066980613949737717323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64506044653742633158478215 96759066980613949737717323)
            ·
              refine ⟨145138600470920924606575985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96759066980613949737717323 145138600470920924606575985)
              ·
                refine ⟨108853950353190693454931989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145138600470920924606575985 108853950353190693454931989)
                ·
                  refine ⟨5102528922805813755699937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108853950353190693454931989 5102528922805813755699937)
                  ·
                    refine ⟨3826896692104360316774953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5102528922805813755699937 3826896692104360316774953)
                    ·
                      refine ⟨2870172519078270237581215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3826896692104360316774953 2870172519078270237581215)
                      ·
                        rfl

theorem cell23_5589641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 2, 2].length) (baseStart_5589641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589641 prefixEnd_5589641 := by exact prefixLift 5589641
  have htrace : WordTrace (prefixWord ++ tailWord_5589641) baseStart_5589641 baseEnd_5589641 := by
    simpa [prefixWord, tailWord_5589641, baseEnd_5589641] using wordTrace_append hprefix tailTrace_5589641
  have hstable : (prefixWord ++ tailWord_5589641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589641).length < 2 ^ (prefixWord ++ tailWord_5589641).sum := by decide
  have hdescent : baseEnd_5589641 < baseStart_5589641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589647 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 7]
def baseStart_5589647 : Nat := 118140960795 + 5589647 * 2 ^ 59
def prefixEnd_5589647 : Nat := 4983230072969 + 3 ^ 40 * 5589647 * 2
def baseEnd_5589647 : Nat := 318908399995799690456243

theorem tailTrace_5589647 : CollatzResearch.WordTrace tailWord_5589647 prefixEnd_5589647 318908399995799690456243 := by
  unfold tailWord_5589647
  simp only [CollatzResearch.WordTrace]
  refine ⟨203871174780671029550279195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135914116520447353033519463 203871174780671029550279195)
  ·
    refine ⟨305806762171006544325418793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203871174780671029550279195 305806762171006544325418793)
    ·
      refine ⟨229355071628254908244064095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305806762171006544325418793 229355071628254908244064095)
      ·
        refine ⟨344032607442382362366096143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229355071628254908244064095 344032607442382362366096143)
        ·
          refine ⟨516048911163573543549144215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344032607442382362366096143 516048911163573543549144215)
          ·
            refine ⟨774073366745360315323716323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516048911163573543549144215 774073366745360315323716323)
            ·
              refine ⟨1161110050118040472985574485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774073366745360315323716323 1161110050118040472985574485)
              ·
                refine ⟨13606758399820786792799701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1161110050118040472985574485 13606758399820786792799701)
                ·
                  refine ⟨318908399995799690456243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13606758399820786792799701 318908399995799690456243)
                  ·
                    rfl

theorem cell23_5589647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 7].length) (baseStart_5589647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589647 prefixEnd_5589647 := by exact prefixLift 5589647
  have htrace : WordTrace (prefixWord ++ tailWord_5589647) baseStart_5589647 baseEnd_5589647 := by
    simpa [prefixWord, tailWord_5589647, baseEnd_5589647] using wordTrace_append hprefix tailTrace_5589647
  have hstable : (prefixWord ++ tailWord_5589647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589647).length < 2 ^ (prefixWord ++ tailWord_5589647).sum := by decide
  have hdescent : baseEnd_5589647 < baseStart_5589647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589694 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_5589694 : Nat := 118140960795 + 5589694 * 2 ^ 59
def prefixEnd_5589694 : Nat := 4983230072969 + 3 ^ 40 * 5589694 * 2
def baseEnd_5589694 : Nat := 956733244517652843406157

theorem tailTrace_5589694 : CollatzResearch.WordTrace tailWord_5589694 prefixEnd_5589694 956733244517652843406157 := by
  unfold tailWord_5589694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25484111126437594572155017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135915259341000504384826757 25484111126437594572155017)
  ·
    refine ⟨19113083344828195929116263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25484111126437594572155017 19113083344828195929116263)
    ·
      refine ⟨28669625017242293893674395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19113083344828195929116263 28669625017242293893674395)
      ·
        refine ⟨43004437525863440840511593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28669625017242293893674395 43004437525863440840511593)
        ·
          refine ⟨32253328144397580630383695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43004437525863440840511593 32253328144397580630383695)
          ·
            refine ⟨48379992216596370945575543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32253328144397580630383695 48379992216596370945575543)
            ·
              refine ⟨72569988324894556418363315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48379992216596370945575543 72569988324894556418363315)
              ·
                refine ⟨108854982487341834627544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72569988324894556418363315 108854982487341834627544973)
                ·
                  refine ⟨40820618432753187985329365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108854982487341834627544973 40820618432753187985329365)
                  ·
                    refine ⟨956733244517652843406157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40820618432753187985329365 956733244517652843406157)
                    ·
                      rfl

theorem cell23_5589694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_5589694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589694 prefixEnd_5589694 := by exact prefixLift 5589694
  have htrace : WordTrace (prefixWord ++ tailWord_5589694) baseStart_5589694 baseEnd_5589694 := by
    simpa [prefixWord, tailWord_5589694, baseEnd_5589694] using wordTrace_append hprefix tailTrace_5589694
  have hstable : (prefixWord ++ tailWord_5589694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589694).length < 2 ^ (prefixWord ++ tailWord_5589694).sum := by decide
  have hdescent : baseEnd_5589694 < baseStart_5589694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589731 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5589731 : Nat := 118140960795 + 5589731 * 2 ^ 59
def prefixEnd_5589731 : Nat := 4983230072969 + 3 ^ 40 * 5589731 * 2
def baseEnd_5589731 : Nat := 2870218732337174885455801

theorem tailTrace_5589731 : CollatzResearch.WordTrace tailWord_5589731 prefixEnd_5589731 2870218732337174885455801 := by
  unfold tailWord_5589731
  simp only [CollatzResearch.WordTrace]
  refine ⟨203874238512366711896337047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135916159008244474597558031 203874238512366711896337047)
  ·
    refine ⟨305811357768550067844505571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203874238512366711896337047 305811357768550067844505571)
    ·
      refine ⟨458717036652825101766758357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305811357768550067844505571 458717036652825101766758357)
      ·
        refine ⟨10751180546550588322658399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 458717036652825101766758357 10751180546550588322658399)
        ·
          refine ⟨16126770819825882483987599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10751180546550588322658399 16126770819825882483987599)
          ·
            refine ⟨24190156229738823725981399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16126770819825882483987599 24190156229738823725981399)
            ·
              refine ⟨36285234344608235588972099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24190156229738823725981399 36285234344608235588972099)
              ·
                refine ⟨54427851516912353383458149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36285234344608235588972099 54427851516912353383458149)
                ·
                  refine ⟨10205222159421066259398403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54427851516912353383458149 10205222159421066259398403)
                  ·
                    refine ⟨15307833239131599389097605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10205222159421066259398403 15307833239131599389097605)
                    ·
                      refine ⟨2870218732337174885455801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15307833239131599389097605 2870218732337174885455801)
                      ·
                        rfl

theorem cell23_5589731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5589731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589731 prefixEnd_5589731 := by exact prefixLift 5589731
  have htrace : WordTrace (prefixWord ++ tailWord_5589731) baseStart_5589731 baseEnd_5589731 := by
    simpa [prefixWord, tailWord_5589731, baseEnd_5589731] using wordTrace_append hprefix tailTrace_5589731
  have hstable : (prefixWord ++ tailWord_5589731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589731).length < 2 ^ (prefixWord ++ tailWord_5589731).sum := by decide
  have hdescent : baseEnd_5589731 < baseStart_5589731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589768 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_5589768 : Nat := 118140960795 + 5589768 * 2 ^ 59
def prefixEnd_5589768 : Nat := 4983230072969 + 3 ^ 40 * 5589768 * 2
def baseEnd_5589768 : Nat := 2870237731121391240693131

theorem tailTrace_5589768 : CollatzResearch.WordTrace tailWord_5589768 prefixEnd_5589768 2870237731121391240693131 := by
  unfold tailWord_5589768
  simp only [CollatzResearch.WordTrace]
  refine ⟨101937794006616333607716979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135917058675488444810289305 101937794006616333607716979)
  ·
    refine ⟨152906691009924500411575469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101937794006616333607716979 152906691009924500411575469)
    ·
      refine ⟨57340009128721687654340801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152906691009924500411575469 57340009128721687654340801)
      ·
        refine ⟨43005006846541265740755601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57340009128721687654340801 43005006846541265740755601)
        ·
          refine ⟨32253755134905949305566701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43005006846541265740755601 32253755134905949305566701)
          ·
            refine ⟨12095158175589730989587513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32253755134905949305566701 12095158175589730989587513)
            ·
              refine ⟨9071368631692298242190635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12095158175589730989587513 9071368631692298242190635)
              ·
                refine ⟨13607052947538447363285953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9071368631692298242190635 13607052947538447363285953)
                ·
                  refine ⟨10205289710653835522464465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13607052947538447363285953 10205289710653835522464465)
                  ·
                    refine ⟨7653967282990376641848349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10205289710653835522464465 7653967282990376641848349)
                    ·
                      refine ⟨2870237731121391240693131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7653967282990376641848349 2870237731121391240693131)
                      ·
                        rfl

theorem cell23_5589768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_5589768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589768 prefixEnd_5589768 := by exact prefixLift 5589768
  have htrace : WordTrace (prefixWord ++ tailWord_5589768) baseStart_5589768 baseEnd_5589768 := by
    simpa [prefixWord, tailWord_5589768, baseEnd_5589768] using wordTrace_append hprefix tailTrace_5589768
  have hstable : (prefixWord ++ tailWord_5589768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589768).length < 2 ^ (prefixWord ++ tailWord_5589768).sum := by decide
  have hdescent : baseEnd_5589768 < baseStart_5589768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589774 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5589774 : Nat := 118140960795 + 5589774 * 2 ^ 59
def prefixEnd_5589774 : Nat := 4983230072969 + 3 ^ 40 * 5589774 * 2
def baseEnd_5589774 : Nat := 2870240812005318217218103

theorem tailTrace_5589774 : CollatzResearch.WordTrace tailWord_5589774 prefixEnd_5589774 2870240812005318217218103 := by
  unfold tailWord_5589774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25484475856401366280019047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135917204567473953493434917 25484475856401366280019047)
  ·
    refine ⟨38226713784602049420028571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25484475856401366280019047 38226713784602049420028571)
    ·
      refine ⟨57340070676903074130042857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38226713784602049420028571 57340070676903074130042857)
      ·
        refine ⟨43005053007677305597532143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57340070676903074130042857 43005053007677305597532143)
        ·
          refine ⟨64507579511515958396298215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43005053007677305597532143 64507579511515958396298215)
          ·
            refine ⟨96761369267273937594447323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64507579511515958396298215 96761369267273937594447323)
            ·
              refine ⟨145142053900910906391670985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96761369267273937594447323 145142053900910906391670985)
              ·
                refine ⟨108856540425683179793753239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145142053900910906391670985 108856540425683179793753239)
                ·
                  refine ⟨163284810638524769690629859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108856540425683179793753239 163284810638524769690629859)
                  ·
                    refine ⟨244927215957787154535944789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163284810638524769690629859 244927215957787154535944789)
                    ·
                      refine ⟨2870240812005318217218103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 244927215957787154535944789 2870240812005318217218103)
                      ·
                        rfl

theorem cell23_5589774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5589774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589774 prefixEnd_5589774 := by exact prefixLift 5589774
  have htrace : WordTrace (prefixWord ++ tailWord_5589774) baseStart_5589774 baseEnd_5589774 := by
    simpa [prefixWord, tailWord_5589774, baseEnd_5589774] using wordTrace_append hprefix tailTrace_5589774
  have hstable : (prefixWord ++ tailWord_5589774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589774).length < 2 ^ (prefixWord ++ tailWord_5589774).sum := by decide
  have hdescent : baseEnd_5589774 < baseStart_5589774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589792 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 1, 4]
def baseStart_5589792 : Nat := 118140960795 + 5589792 * 2 ^ 59
def prefixEnd_5589792 : Nat := 4983230072969 + 3 ^ 40 * 5589792 * 2
def baseEnd_5589792 : Nat := 956750018219033048931007

theorem tailTrace_5589792 : CollatzResearch.WordTrace tailWord_5589792 prefixEnd_5589792 956750018219033048931007 := by
  unfold tailWord_5589792
  simp only [CollatzResearch.WordTrace]
  refine ⟨101938231682572859657153815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135917642243430479542871753 101938231682572859657153815)
  ·
    refine ⟨152907347523859289485730723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101938231682572859657153815 152907347523859289485730723)
    ·
      refine ⟨229361021285788934228596085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152907347523859289485730723 229361021285788934228596085)
      ·
        refine ⟨21502595745542712583930883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229361021285788934228596085 21502595745542712583930883)
        ·
          refine ⟨32253893618314068875896325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21502595745542712583930883 32253893618314068875896325)
          ·
            refine ⟨6047605053433887914230561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32253893618314068875896325 6047605053433887914230561)
            ·
              refine ⟨4535703790075415935672921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6047605053433887914230561 4535703790075415935672921)
              ·
                refine ⟨3401777842556561951754691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4535703790075415935672921 3401777842556561951754691)
                ·
                  refine ⟨5102666763834842927632037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401777842556561951754691 5102666763834842927632037)
                  ·
                    refine ⟨956750018219033048931007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102666763834842927632037 956750018219033048931007)
                    ·
                      rfl

theorem cell23_5589792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 4].length) (baseStart_5589792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589792 prefixEnd_5589792 := by exact prefixLift 5589792
  have htrace : WordTrace (prefixWord ++ tailWord_5589792) baseStart_5589792 baseEnd_5589792 := by
    simpa [prefixWord, tailWord_5589792, baseEnd_5589792] using wordTrace_append hprefix tailTrace_5589792
  have hstable : (prefixWord ++ tailWord_5589792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589792).length < 2 ^ (prefixWord ++ tailWord_5589792).sum := by decide
  have hdescent : baseEnd_5589792 < baseStart_5589792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589831 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 4, 4]
def baseStart_5589831 : Nat := 118140960795 + 5589831 * 2 ^ 59
def prefixEnd_5589831 : Nat := 4983230072969 + 3 ^ 40 * 5589831 * 2
def baseEnd_5589831 : Nat := 956756693467541498068447

theorem tailTrace_5589831 : CollatzResearch.WordTrace tailWord_5589831 prefixEnd_5589831 956756693467541498068447 := by
  unfold tailWord_5589831
  simp only [CollatzResearch.WordTrace]
  refine ⟨203877885812004428974977347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135918590541336285983318231 203877885812004428974977347)
  ·
    refine ⟨305816828718006643462466021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203877885812004428974977347 305816828718006643462466021)
    ·
      refine ⟨57340655384626245649212379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305816828718006643462466021 57340655384626245649212379)
      ·
        refine ⟨86010983076939368473818569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57340655384626245649212379 86010983076939368473818569)
        ·
          refine ⟨64508237307704526355363927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86010983076939368473818569 64508237307704526355363927)
          ·
            refine ⟨96762355961556789533045891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64508237307704526355363927 96762355961556789533045891)
            ·
              refine ⟨145143533942335184299568837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96762355961556789533045891 145143533942335184299568837)
              ·
                refine ⟨27214412614187847056169157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145143533942335184299568837 27214412614187847056169157)
                ·
                  refine ⟨5102702365160221323031717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27214412614187847056169157 5102702365160221323031717)
                  ·
                    refine ⟨956756693467541498068447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102702365160221323031717 956756693467541498068447)
                    ·
                      rfl

theorem cell23_5589831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_5589831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589831 prefixEnd_5589831 := by exact prefixLift 5589831
  have htrace : WordTrace (prefixWord ++ tailWord_5589831) baseStart_5589831 baseEnd_5589831 := by
    simpa [prefixWord, tailWord_5589831, baseEnd_5589831] using wordTrace_append hprefix tailTrace_5589831
  have hstable : (prefixWord ++ tailWord_5589831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589831).length < 2 ^ (prefixWord ++ tailWord_5589831).sum := by decide
  have hdescent : baseEnd_5589831 < baseStart_5589831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589855 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 3, 2, 2]
def baseStart_5589855 : Nat := 118140960795 + 5589855 * 2 ^ 59
def prefixEnd_5589855 : Nat := 4983230072969 + 3 ^ 40 * 5589855 * 2
def baseEnd_5589855 : Nat := 2870282403938332400305231

theorem tailTrace_5589855 : CollatzResearch.WordTrace tailWord_5589855 prefixEnd_5589855 2870282403938332400305231 := by
  unfold tailWord_5589855
  simp only [CollatzResearch.WordTrace]
  refine ⟨203878761163917481073851019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135919174109278320715900679 203878761163917481073851019)
  ·
    refine ⟨305818141745876221610776529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203878761163917481073851019 305818141745876221610776529)
    ·
      refine ⟨229363606309407166208082397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305818141745876221610776529 229363606309407166208082397)
      ·
        refine ⟨86011352366027687328030899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229363606309407166208082397 86011352366027687328030899)
        ·
          refine ⟨129017028549041530992046349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86011352366027687328030899 129017028549041530992046349)
          ·
            refine ⟨48381385705890574122017381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129017028549041530992046349 48381385705890574122017381)
            ·
              refine ⟨9071509819854482647878259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48381385705890574122017381 9071509819854482647878259)
              ·
                refine ⟨13607264729781723971817389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9071509819854482647878259 13607264729781723971817389)
                ·
                  refine ⟨5102724273668146489431521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13607264729781723971817389 5102724273668146489431521)
                  ·
                    refine ⟨3827043205251109867073641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5102724273668146489431521 3827043205251109867073641)
                    ·
                      refine ⟨2870282403938332400305231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827043205251109867073641 2870282403938332400305231)
                      ·
                        rfl

theorem cell23_5589855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_5589855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589855 prefixEnd_5589855 := by exact prefixLift 5589855
  have htrace : WordTrace (prefixWord ++ tailWord_5589855) baseStart_5589855 baseEnd_5589855 := by
    simpa [prefixWord, tailWord_5589855, baseEnd_5589855] using wordTrace_append hprefix tailTrace_5589855
  have hstable : (prefixWord ++ tailWord_5589855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589855).length < 2 ^ (prefixWord ++ tailWord_5589855).sum := by decide
  have hdescent : baseEnd_5589855 < baseStart_5589855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589878 : List Nat := [5, 1, 1, 3, 1, 2, 1, 9]
def baseStart_5589878 : Nat := 118140960795 + 5589878 * 2 ^ 59
def prefixEnd_5589878 : Nat := 4983230072969 + 3 ^ 40 * 5589878 * 2
def baseEnd_5589878 : Nat := 106307193110866141122875

theorem tailTrace_5589878 : CollatzResearch.WordTrace tailWord_5589878 prefixEnd_5589878 106307193110866141122875 := by
  unfold tailWord_5589878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12742475002677134750121143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135919733361889437334625525 12742475002677134750121143)
  ·
    refine ⟨19113712504015702125181715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12742475002677134750121143 19113712504015702125181715)
    ·
      refine ⟨28670568756023553187772573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19113712504015702125181715 28670568756023553187772573)
      ·
        refine ⟨10751463283508832445414715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28670568756023553187772573 10751463283508832445414715)
        ·
          refine ⟨16127194925263248668122073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10751463283508832445414715 16127194925263248668122073)
          ·
            refine ⟨12095396193947436501091555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16127194925263248668122073 12095396193947436501091555)
            ·
              refine ⟨18143094290921154751637333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12095396193947436501091555 18143094290921154751637333)
              ·
                refine ⟨106307193110866141122875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18143094290921154751637333 106307193110866141122875)
                ·
                  rfl

theorem cell23_5589878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_5589878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589878 prefixEnd_5589878 := by exact prefixLift 5589878
  have htrace : WordTrace (prefixWord ++ tailWord_5589878) baseStart_5589878 baseEnd_5589878 := by
    simpa [prefixWord, tailWord_5589878, baseEnd_5589878] using wordTrace_append hprefix tailTrace_5589878
  have hstable : (prefixWord ++ tailWord_5589878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589878).length < 2 ^ (prefixWord ++ tailWord_5589878).sum := by decide
  have hdescent : baseEnd_5589878 < baseStart_5589878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589906 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5589906 : Nat := 118140960795 + 5589906 * 2 ^ 59
def prefixEnd_5589906 : Nat := 4983230072969 + 3 ^ 40 * 5589906 * 2
def baseEnd_5589906 : Nat := 2870308591451711700767497

theorem tailTrace_5589906 : CollatzResearch.WordTrace tailWord_5589906 prefixEnd_5589906 2870308591451711700767497 := by
  unfold tailWord_5589906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50970155321683179195989393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135920414191155144522638381 50970155321683179195989393)
  ·
    refine ⟨38227616491262384396992045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50970155321683179195989393 38227616491262384396992045)
    ·
      refine ⟨14335356184223394148872017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38227616491262384396992045 14335356184223394148872017)
      ·
        refine ⟨10751517138167545611654013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14335356184223394148872017 10751517138167545611654013)
        ·
          refine ⟨4031818926812829604370255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10751517138167545611654013 4031818926812829604370255)
          ·
            refine ⟨6047728390219244406555383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031818926812829604370255 6047728390219244406555383)
            ·
              refine ⟨9071592585328866609833075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6047728390219244406555383 9071592585328866609833075)
              ·
                refine ⟨13607388877993299914749613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9071592585328866609833075 13607388877993299914749613)
                ·
                  refine ⟨5102770829247487468031105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13607388877993299914749613 5102770829247487468031105)
                  ·
                    refine ⟨3827078121935615601023329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5102770829247487468031105 3827078121935615601023329)
                    ·
                      refine ⟨2870308591451711700767497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827078121935615601023329 2870308591451711700767497)
                      ·
                        rfl

theorem cell23_5589906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5589906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589906 prefixEnd_5589906 := by exact prefixLift 5589906
  have htrace : WordTrace (prefixWord ++ tailWord_5589906) baseStart_5589906 baseEnd_5589906 := by
    simpa [prefixWord, tailWord_5589906, baseEnd_5589906] using wordTrace_append hprefix tailTrace_5589906
  have hstable : (prefixWord ++ tailWord_5589906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589906).length < 2 ^ (prefixWord ++ tailWord_5589906).sum := by decide
  have hdescent : baseEnd_5589906 < baseStart_5589906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589911 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_5589911 : Nat := 118140960795 + 5589911 * 2 ^ 59
def prefixEnd_5589911 : Nat := 4983230072969 + 3 ^ 40 * 5589911 * 2
def baseEnd_5589911 : Nat := 2870311158854984181204973

theorem tailTrace_5589911 : CollatzResearch.WordTrace tailWord_5589911 prefixEnd_5589911 2870311158854984181204973 := by
  unfold tailWord_5589911
  simp only [CollatzResearch.WordTrace]
  refine ⟨203880803651714602637889587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135920535767809735091926391 203880803651714602637889587)
  ·
    refine ⟨305821205477571903956834381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203880803651714602637889587 305821205477571903956834381)
    ·
      refine ⟨114682952054089463983812893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305821205477571903956834381 114682952054089463983812893)
      ·
        refine ⟨43006107020283548993929835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114682952054089463983812893 43006107020283548993929835)
        ·
          refine ⟨64509160530425323490894753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43006107020283548993929835 64509160530425323490894753)
          ·
            refine ⟨48381870397818992618171065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64509160530425323490894753 48381870397818992618171065)
            ·
              refine ⟨36286402798364244463628299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48381870397818992618171065 36286402798364244463628299)
              ·
                refine ⟨54429604197546366695442449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36286402798364244463628299 54429604197546366695442449)
                ·
                  refine ⟨40822203148159775021581837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54429604197546366695442449 40822203148159775021581837)
                  ·
                    refine ⟨15308326180559915633093189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40822203148159775021581837 15308326180559915633093189)
                    ·
                      refine ⟨2870311158854984181204973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15308326180559915633093189 2870311158854984181204973)
                      ·
                        rfl

theorem cell23_5589911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_5589911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589911 prefixEnd_5589911 := by exact prefixLift 5589911
  have htrace : WordTrace (prefixWord ++ tailWord_5589911) baseStart_5589911 baseEnd_5589911 := by
    simpa [prefixWord, tailWord_5589911, baseEnd_5589911] using wordTrace_append hprefix tailTrace_5589911
  have hstable : (prefixWord ++ tailWord_5589911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589911).length < 2 ^ (prefixWord ++ tailWord_5589911).sum := by decide
  have hdescent : baseEnd_5589911 < baseStart_5589911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589922 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_5589922 : Nat := 118140960795 + 5589922 * 2 ^ 59
def prefixEnd_5589922 : Nat := 4983230072969 + 3 ^ 40 * 5589922 * 2
def baseEnd_5589922 : Nat := 2870316807142183638167423

theorem tailTrace_5589922 : CollatzResearch.WordTrace tailWord_5589922 prefixEnd_5589922 2870316807142183638167423 := by
  unfold tailWord_5589922
  simp only [CollatzResearch.WordTrace]
  refine ⟨50970301213668687879135005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135920803236449834344360013 50970301213668687879135005)
  ·
    refine ⟨19113862955125757954675627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50970301213668687879135005 19113862955125757954675627)
    ·
      refine ⟨28670794432688636932013441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19113862955125757954675627 28670794432688636932013441)
      ·
        refine ⟨21503095824516477699010081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28670794432688636932013441 21503095824516477699010081)
        ·
          refine ⟨16127321868387358274257561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21503095824516477699010081 16127321868387358274257561)
          ·
            refine ⟨12095491401290518705693171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16127321868387358274257561 12095491401290518705693171)
            ·
              refine ⟨18143237101935778058539757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12095491401290518705693171 18143237101935778058539757)
              ·
                refine ⟨6803713913225916771952409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18143237101935778058539757 6803713913225916771952409)
                ·
                  refine ⟨5102785434919437578964307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803713913225916771952409 5102785434919437578964307)
                  ·
                    refine ⟨7654178152379156368446461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5102785434919437578964307 7654178152379156368446461)
                    ·
                      refine ⟨2870316807142183638167423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654178152379156368446461 2870316807142183638167423)
                      ·
                        rfl

theorem cell23_5589922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_5589922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589922 prefixEnd_5589922 := by exact prefixLift 5589922
  have htrace : WordTrace (prefixWord ++ tailWord_5589922) baseStart_5589922 baseEnd_5589922 := by
    simpa [prefixWord, tailWord_5589922, baseEnd_5589922] using wordTrace_append hprefix tailTrace_5589922
  have hstable : (prefixWord ++ tailWord_5589922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589922).length < 2 ^ (prefixWord ++ tailWord_5589922).sum := by decide
  have hdescent : baseEnd_5589922 < baseStart_5589922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589931 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 3]
def baseStart_5589931 : Nat := 118140960795 + 5589931 * 2 ^ 59
def prefixEnd_5589931 : Nat := 4983230072969 + 3 ^ 40 * 5589931 * 2
def baseEnd_5589931 : Nat := 2870321428468074102954881

theorem tailTrace_5589931 : CollatzResearch.WordTrace tailWord_5589931 prefixEnd_5589931 2870321428468074102954881 := by
  unfold tailWord_5589931
  simp only [CollatzResearch.WordTrace]
  refine ⟨203881533111642146053617647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135921022074428097369078431 203881533111642146053617647)
  ·
    refine ⟨305822299667463219080426471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203881533111642146053617647 305822299667463219080426471)
    ·
      refine ⟨458733449501194828620639707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305822299667463219080426471 458733449501194828620639707)
      ·
        refine ⟨688100174251792242930959561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458733449501194828620639707 688100174251792242930959561)
        ·
          refine ⟨516075130688844182198219671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688100174251792242930959561 516075130688844182198219671)
          ·
            refine ⟨774112696033266273297329507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516075130688844182198219671 774112696033266273297329507)
            ·
              refine ⟨1161169044049899409945994261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774112696033266273297329507 1161169044049899409945994261)
              ·
                refine ⟨54429798939839034841218481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1161169044049899409945994261 54429798939839034841218481)
                ·
                  refine ⟨40822349204879276130913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54429798939839034841218481 40822349204879276130913861)
                  ·
                    refine ⟨7654190475914864274546349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40822349204879276130913861 7654190475914864274546349)
                    ·
                      refine ⟨2870321428468074102954881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654190475914864274546349 2870321428468074102954881)
                      ·
                        rfl

theorem cell23_5589931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 3].length) (baseStart_5589931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589931 prefixEnd_5589931 := by exact prefixLift 5589931
  have htrace : WordTrace (prefixWord ++ tailWord_5589931) baseStart_5589931 baseEnd_5589931 := by
    simpa [prefixWord, tailWord_5589931, baseEnd_5589931] using wordTrace_append hprefix tailTrace_5589931
  have hstable : (prefixWord ++ tailWord_5589931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589931).length < 2 ^ (prefixWord ++ tailWord_5589931).sum := by decide
  have hdescent : baseEnd_5589931 < baseStart_5589931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589945 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 1, 4, 2]
def baseStart_5589945 : Nat := 118140960795 + 5589945 * 2 ^ 59
def prefixEnd_5589945 : Nat := 4983230072969 + 3 ^ 40 * 5589945 * 2
def baseEnd_5589945 : Nat := 2870328617197237048179817

theorem tailTrace_5589945 : CollatzResearch.WordTrace tailWord_5589945 prefixEnd_5589945 2870328617197237048179817 := by
  unfold tailWord_5589945
  simp only [CollatzResearch.WordTrace]
  refine ⟨203882043733591426444627289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135921362489060950963084859 203882043733591426444627289)
  ·
    refine ⟨152911532800193569833470467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203882043733591426444627289 152911532800193569833470467)
    ·
      refine ⟨229367299200290354750205701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152911532800193569833470467 229367299200290354750205701)
      ·
        refine ⟨43006368600054441515663569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229367299200290354750205701 43006368600054441515663569)
        ·
          refine ⟨32254776450040831136747677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43006368600054441515663569 32254776450040831136747677)
          ·
            refine ⟨12095541168765311676280379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32254776450040831136747677 12095541168765311676280379)
            ·
              refine ⟨18143311753147967514420569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12095541168765311676280379 18143311753147967514420569)
              ·
                refine ⟨13607483814860975635815427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18143311753147967514420569 13607483814860975635815427)
                ·
                  refine ⟨20411225722291463453723141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13607483814860975635815427 20411225722291463453723141)
                  ·
                    refine ⟨3827104822929649397573089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20411225722291463453723141 3827104822929649397573089)
                    ·
                      refine ⟨2870328617197237048179817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827104822929649397573089 2870328617197237048179817)
                      ·
                        rfl

theorem cell23_5589945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_5589945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589945 prefixEnd_5589945 := by exact prefixLift 5589945
  have htrace : WordTrace (prefixWord ++ tailWord_5589945) baseStart_5589945 baseEnd_5589945 := by
    simpa [prefixWord, tailWord_5589945, baseEnd_5589945] using wordTrace_append hprefix tailTrace_5589945
  have hstable : (prefixWord ++ tailWord_5589945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589945).length < 2 ^ (prefixWord ++ tailWord_5589945).sum := by decide
  have hdescent : baseEnd_5589945 < baseStart_5589945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589949 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_5589949 : Nat := 118140960795 + 5589949 * 2 ^ 59
def prefixEnd_5589949 : Nat := 4983230072969 + 3 ^ 40 * 5589949 * 2
def baseEnd_5589949 : Nat := 2870330671119855032529799

theorem tailTrace_5589949 : CollatzResearch.WordTrace tailWord_5589949 prefixEnd_5589949 2870330671119855032529799 := by
  unfold tailWord_5589949
  simp only [CollatzResearch.WordTrace]
  refine ⟨203882189625576935127772901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135921459750384623418515267 203882189625576935127772901)
  ·
    refine ⟨38227910554795675336457419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203882189625576935127772901 38227910554795675336457419)
    ·
      refine ⟨57341865832193513004686129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38227910554795675336457419 57341865832193513004686129)
      ·
        refine ⟨43006399374145134753514597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57341865832193513004686129 43006399374145134753514597)
        ·
          refine ⟨8063699882652212766283987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43006399374145134753514597 8063699882652212766283987)
          ·
            refine ⟨12095549823978319149425981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8063699882652212766283987 12095549823978319149425981)
            ·
              refine ⟨4535831183991869681034743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12095549823978319149425981 4535831183991869681034743)
              ·
                refine ⟨6803746775987804521552115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535831183991869681034743 6803746775987804521552115)
                ·
                  refine ⟨10205620163981706782328173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6803746775987804521552115 10205620163981706782328173)
                  ·
                    refine ⟨3827107561493140043373065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10205620163981706782328173 3827107561493140043373065)
                    ·
                      refine ⟨2870330671119855032529799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827107561493140043373065 2870330671119855032529799)
                      ·
                        rfl

theorem cell23_5589949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_5589949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589949 prefixEnd_5589949 := by exact prefixLift 5589949
  have htrace : WordTrace (prefixWord ++ tailWord_5589949) baseStart_5589949 baseEnd_5589949 := by
    simpa [prefixWord, tailWord_5589949, baseEnd_5589949] using wordTrace_append hprefix tailTrace_5589949
  have hstable : (prefixWord ++ tailWord_5589949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589949).length < 2 ^ (prefixWord ++ tailWord_5589949).sum := by decide
  have hdescent : baseEnd_5589949 < baseStart_5589949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589978 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_5589978 : Nat := 118140960795 + 5589978 * 2 ^ 59
def prefixEnd_5589978 : Nat := 4983230072969 + 3 ^ 40 * 5589978 * 2
def baseEnd_5589978 : Nat := 2870345562058835419067165

theorem tailTrace_5589978 : CollatzResearch.WordTrace tailWord_5589978 prefixEnd_5589978 2870345562058835419067165 := by
  unfold tailWord_5589978
  simp only [CollatzResearch.WordTrace]
  refine ⟨50970811835617968270144647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135922164894981248720385725 50970811835617968270144647)
  ·
    refine ⟨76456217753426952405216971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50970811835617968270144647 76456217753426952405216971)
    ·
      refine ⟨114684326630140428607825457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76456217753426952405216971 114684326630140428607825457)
      ·
        refine ⟨86013244972605321455869093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114684326630140428607825457 86013244972605321455869093)
        ·
          refine ⟨16127483432363497772975455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86013244972605321455869093 16127483432363497772975455)
          ·
            refine ⟨24191225148545246659463183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16127483432363497772975455 24191225148545246659463183)
            ·
              refine ⟨36286837722817869989194775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24191225148545246659463183 36286837722817869989194775)
              ·
                refine ⟨54430256584226804983792163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36286837722817869989194775 54430256584226804983792163)
                ·
                  refine ⟨81645384876340207475688245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54430256584226804983792163 81645384876340207475688245)
                  ·
                    refine ⟨7654254832156894450845773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81645384876340207475688245 7654254832156894450845773)
                    ·
                      refine ⟨2870345562058835419067165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654254832156894450845773 2870345562058835419067165)
                      ·
                        rfl

theorem cell23_5589978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_5589978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5589978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5589978 prefixEnd_5589978 := by exact prefixLift 5589978
  have htrace : WordTrace (prefixWord ++ tailWord_5589978) baseStart_5589978 baseEnd_5589978 := by
    simpa [prefixWord, tailWord_5589978, baseEnd_5589978] using wordTrace_append hprefix tailTrace_5589978
  have hstable : (prefixWord ++ tailWord_5589978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589978).length < 2 ^ (prefixWord ++ tailWord_5589978).sum := by decide
  have hdescent : baseEnd_5589978 < baseStart_5589978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590088 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_5590088 : Nat := 118140960795 + 5590088 * 2 ^ 59
def prefixEnd_5590088 : Nat := 4983230072969 + 3 ^ 40 * 5590088 * 2
def baseEnd_5590088 : Nat := 956800681643609996230553

theorem tailTrace_5590088 : CollatzResearch.WordTrace tailWord_5590088 prefixEnd_5590088 956800681643609996230553 := by
  unfold tailWord_5590088
  simp only [CollatzResearch.WordTrace]
  refine ⟨101943629686036680933541459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135924839581382241244721945 101943629686036680933541459)
  ·
    refine ⟨152915444529055021400312189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101943629686036680933541459 152915444529055021400312189)
    ·
      refine ⟨57343291698395633025117071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152915444529055021400312189 57343291698395633025117071)
      ·
        refine ⟨86014937547593449537675607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57343291698395633025117071 86014937547593449537675607)
        ·
          refine ⟨129022406321390174306513411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86014937547593449537675607 129022406321390174306513411)
          ·
            refine ⟨193533609482085261459770117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129022406321390174306513411 193533609482085261459770117)
            ·
              refine ⟨36287551777890986523706897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193533609482085261459770117 36287551777890986523706897)
              ·
                refine ⟨27215663833418239892780173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36287551777890986523706897 27215663833418239892780173)
                ·
                  refine ⟨10205873937531839959792565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27215663833418239892780173 10205873937531839959792565)
                  ·
                    refine ⟨956800681643609996230553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10205873937531839959792565 956800681643609996230553)
                    ·
                      rfl

theorem cell23_5590088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_5590088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590088 prefixEnd_5590088 := by exact prefixLift 5590088
  have htrace : WordTrace (prefixWord ++ tailWord_5590088) baseStart_5590088 baseEnd_5590088 := by
    simpa [prefixWord, tailWord_5590088, baseEnd_5590088] using wordTrace_append hprefix tailTrace_5590088
  have hstable : (prefixWord ++ tailWord_5590088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590088).length < 2 ^ (prefixWord ++ tailWord_5590088).sum := by decide
  have hdescent : baseEnd_5590088 < baseStart_5590088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590112 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 2, 3, 2]
def baseStart_5590112 : Nat := 118140960795 + 5590112 * 2 ^ 59
def prefixEnd_5590112 : Nat := 4983230072969 + 3 ^ 40 * 5590112 * 2
def baseEnd_5590112 : Nat := 2870414368466537894791549

theorem tailTrace_5590112 : CollatzResearch.WordTrace tailWord_5590112 prefixEnd_5590112 2870414368466537894791549 := by
  unfold tailWord_5590112
  simp only [CollatzResearch.WordTrace]
  refine ⟨101944067361993206982978295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135925423149324275977304393 101944067361993206982978295)
  ·
    refine ⟨152916101042989810474467443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101944067361993206982978295 152916101042989810474467443)
    ·
      refine ⟨229374151564484715711701165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152916101042989810474467443 229374151564484715711701165)
      ·
        refine ⟨86015306836681768391887937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229374151564484715711701165 86015306836681768391887937)
        ·
          refine ⟨64511480127511326293915953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86015306836681768391887937 64511480127511326293915953)
          ·
            refine ⟨48383610095633494720436965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64511480127511326293915953 48383610095633494720436965)
            ·
              refine ⟨9071926892931280260081931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48383610095633494720436965 9071926892931280260081931)
              ·
                refine ⟨13607890339396920390122897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9071926892931280260081931 13607890339396920390122897)
                ·
                  refine ⟨10205917754547690292592173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13607890339396920390122897 10205917754547690292592173)
                  ·
                    refine ⟨3827219157955383859722065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10205917754547690292592173 3827219157955383859722065)
                    ·
                      refine ⟨2870414368466537894791549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827219157955383859722065 2870414368466537894791549)
                      ·
                        rfl

theorem cell23_5590112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_5590112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590112 prefixEnd_5590112 := by exact prefixLift 5590112
  have htrace : WordTrace (prefixWord ++ tailWord_5590112) baseStart_5590112 baseEnd_5590112 := by
    simpa [prefixWord, tailWord_5590112, baseEnd_5590112] using wordTrace_append hprefix tailTrace_5590112
  have hstable : (prefixWord ++ tailWord_5590112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590112).length < 2 ^ (prefixWord ++ tailWord_5590112).sum := by decide
  have hdescent : baseEnd_5590112 < baseStart_5590112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590152 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 1, 6]
def baseStart_5590152 : Nat := 118140960795 + 5590152 * 2 ^ 59
def prefixEnd_5590152 : Nat := 4983230072969 + 3 ^ 40 * 5590152 * 2
def baseEnd_5590152 : Nat := 956811635897572579430455

theorem tailTrace_5590152 : CollatzResearch.WordTrace tailWord_5590152 prefixEnd_5590152 956811635897572579430455 := by
  unfold tailWord_5590152
  simp only [CollatzResearch.WordTrace]
  refine ⟨101944796821920750398706355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135926395762561000531608473 101944796821920750398706355)
  ·
    refine ⟨152917195232881125598059533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101944796821920750398706355 152917195232881125598059533)
    ·
      refine ⟨57343948212330422099272325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152917195232881125598059533 57343948212330422099272325)
      ·
        refine ⟨10751990289811954143613561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57343948212330422099272325 10751990289811954143613561)
        ·
          refine ⟨8063992717358965607710171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10751990289811954143613561 8063992717358965607710171)
          ·
            refine ⟨12095989076038448411565257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8063992717358965607710171 12095989076038448411565257)
            ·
              refine ⟨9071991807028836308673943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12095989076038448411565257 9071991807028836308673943)
              ·
                refine ⟨13607987710543254463010915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9071991807028836308673943 13607987710543254463010915)
                ·
                  refine ⟨20411981565814881694516373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13607987710543254463010915 20411981565814881694516373)
                  ·
                    refine ⟨956811635897572579430455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20411981565814881694516373 956811635897572579430455)
                    ·
                      rfl

theorem cell23_5590152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_5590152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590152 prefixEnd_5590152 := by exact prefixLift 5590152
  have htrace : WordTrace (prefixWord ++ tailWord_5590152) baseStart_5590152 baseEnd_5590152 := by
    simpa [prefixWord, tailWord_5590152, baseEnd_5590152] using wordTrace_append hprefix tailTrace_5590152
  have hstable : (prefixWord ++ tailWord_5590152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590152).length < 2 ^ (prefixWord ++ tailWord_5590152).sum := by decide
  have hdescent : baseEnd_5590152 < baseStart_5590152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590162 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5590162 : Nat := 118140960795 + 5590162 * 2 ^ 59
def prefixEnd_5590162 : Nat := 4983230072969 + 3 ^ 40 * 5590162 * 2
def baseEnd_5590162 : Nat := 2870440042499262699166319

theorem tailTrace_5590162 : CollatzResearch.WordTrace tailWord_5590162 prefixEnd_5590162 2870440042499262699166319 := by
  unfold tailWord_5590162
  simp only [CollatzResearch.WordTrace]
  refine ⟨50972489593451318126319185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135926638915870181670184493 50972489593451318126319185)
  ·
    refine ⟨38229367195088488594739389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50972489593451318126319185 38229367195088488594739389)
    ·
      refine ⟨14336012698158183223027271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38229367195088488594739389 14336012698158183223027271)
      ·
        refine ⟨21504019047237274834540907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14336012698158183223027271 21504019047237274834540907)
        ·
          refine ⟨32256028570855912251811361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21504019047237274834540907 32256028570855912251811361)
          ·
            refine ⟨24192021428141934188858521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32256028570855912251811361 24192021428141934188858521)
            ·
              refine ⟨18144016071106450641643891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24192021428141934188858521 18144016071106450641643891)
              ·
                refine ⟨27216024106659675962465837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18144016071106450641643891 27216024106659675962465837)
                ·
                  refine ⟨10206009039997378485924689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27216024106659675962465837 10206009039997378485924689)
                  ·
                    refine ⟨7654506779998033864443517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10206009039997378485924689 7654506779998033864443517)
                    ·
                      refine ⟨2870440042499262699166319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654506779998033864443517 2870440042499262699166319)
                      ·
                        rfl

theorem cell23_5590162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5590162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590162 prefixEnd_5590162 := by exact prefixLift 5590162
  have htrace : WordTrace (prefixWord ++ tailWord_5590162) baseStart_5590162 baseEnd_5590162 := by
    simpa [prefixWord, tailWord_5590162, baseEnd_5590162] using wordTrace_append hprefix tailTrace_5590162
  have hstable : (prefixWord ++ tailWord_5590162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590162).length < 2 ^ (prefixWord ++ tailWord_5590162).sum := by decide
  have hdescent : baseEnd_5590162 < baseStart_5590162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590176 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 1, 2, 2]
def baseStart_5590176 : Nat := 118140960795 + 5590176 * 2 ^ 59
def prefixEnd_5590176 : Nat := 4983230072969 + 3 ^ 40 * 5590176 * 2
def baseEnd_5590176 : Nat := 2870447231228425644391255

theorem tailTrace_5590176 : CollatzResearch.WordTrace tailWord_5590176 prefixEnd_5590176 2870447231228425644391255 := by
  unfold tailWord_5590176
  simp only [CollatzResearch.WordTrace]
  refine ⟨101945234497877276448143191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135926979330503035264190921 101945234497877276448143191)
  ·
    refine ⟨152917851746815914672214787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101945234497877276448143191 152917851746815914672214787)
    ·
      refine ⟨229376777620223872008322181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152917851746815914672214787 229376777620223872008322181)
      ·
        refine ⟨43008145803791976001560409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229376777620223872008322181 43008145803791976001560409)
        ·
          refine ⟨32256109352843982001170307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43008145803791976001560409 32256109352843982001170307)
          ·
            refine ⟨48384164029265973001755461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32256109352843982001170307 48384164029265973001755461)
            ·
              refine ⟨9072030755487369937829149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48384164029265973001755461 9072030755487369937829149)
              ·
                refine ⟨3402011533307763726685931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9072030755487369937829149 3402011533307763726685931)
                ·
                  refine ⟨5103017299961645590028897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402011533307763726685931 5103017299961645590028897)
                  ·
                    refine ⟨3827262974971234192521673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5103017299961645590028897 3827262974971234192521673)
                    ·
                      refine ⟨2870447231228425644391255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827262974971234192521673 2870447231228425644391255)
                      ·
                        rfl

theorem cell23_5590176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_5590176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590176 prefixEnd_5590176 := by exact prefixLift 5590176
  have htrace : WordTrace (prefixWord ++ tailWord_5590176) baseStart_5590176 baseEnd_5590176 := by
    simpa [prefixWord, tailWord_5590176, baseEnd_5590176] using wordTrace_append hprefix tailTrace_5590176
  have hstable : (prefixWord ++ tailWord_5590176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590176).length < 2 ^ (prefixWord ++ tailWord_5590176).sum := by decide
  have hdescent : baseEnd_5590176 < baseStart_5590176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590186 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5590186 : Nat := 118140960795 + 5590186 * 2 ^ 59
def prefixEnd_5590186 : Nat := 4983230072969 + 3 ^ 40 * 5590186 * 2
def baseEnd_5590186 : Nat := 956817455344990201755403

theorem tailTrace_5590186 : CollatzResearch.WordTrace tailWord_5590186 prefixEnd_5590186 956817455344990201755403 := by
  unfold tailWord_5590186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50972708431429581151037603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135927222483812216402766941 50972708431429581151037603)
  ·
    refine ⟨76459062647144371726556405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50972708431429581151037603 76459062647144371726556405)
    ·
      refine ⟨7168037123169784849364663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76459062647144371726556405 7168037123169784849364663)
      ·
        refine ⟨10752055684754677274046995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7168037123169784849364663 10752055684754677274046995)
        ·
          refine ⟨16128083527132015911070493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10752055684754677274046995 16128083527132015911070493)
          ·
            refine ⟨6048031322674505966651435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16128083527132015911070493 6048031322674505966651435)
            ·
              refine ⟨9072046984011758949977153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048031322674505966651435 9072046984011758949977153)
              ·
                refine ⟨6804035238008819212482865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9072046984011758949977153 6804035238008819212482865)
                ·
                  refine ⟨5103026428506614409362149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6804035238008819212482865 5103026428506614409362149)
                  ·
                    refine ⟨956817455344990201755403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5103026428506614409362149 956817455344990201755403)
                    ·
                      rfl

theorem cell23_5590186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5590186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590186 prefixEnd_5590186 := by exact prefixLift 5590186
  have htrace : WordTrace (prefixWord ++ tailWord_5590186) baseStart_5590186 baseEnd_5590186 := by
    simpa [prefixWord, tailWord_5590186, baseEnd_5590186] using wordTrace_append hprefix tailTrace_5590186
  have hstable : (prefixWord ++ tailWord_5590186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590186).length < 2 ^ (prefixWord ++ tailWord_5590186).sum := by decide
  have hdescent : baseEnd_5590186 < baseStart_5590186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590188 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_5590188 : Nat := 118140960795 + 5590188 * 2 ^ 59
def prefixEnd_5590188 : Nat := 4983230072969 + 3 ^ 40 * 5590188 * 2
def baseEnd_5590188 : Nat := 2870453392996279597441199

theorem tailTrace_5590188 : CollatzResearch.WordTrace tailWord_5590188 prefixEnd_5590188 2870453392996279597441199 := by
  unfold tailWord_5590188
  simp only [CollatzResearch.WordTrace]
  refine ⟨101945453335855539472861609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135927271114474052630482145 101945453335855539472861609)
  ·
    refine ⟨76459090001891654604646207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101945453335855539472861609 76459090001891654604646207)
    ·
      refine ⟨114688635002837481906969311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76459090001891654604646207 114688635002837481906969311)
      ·
        refine ⟨172032952504256222860453967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114688635002837481906969311 172032952504256222860453967)
        ·
          refine ⟨258049428756384334290680951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172032952504256222860453967 258049428756384334290680951)
          ·
            refine ⟨387074143134576501436021427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258049428756384334290680951 387074143134576501436021427)
            ·
              refine ⟨580611214701864752154032141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387074143134576501436021427 580611214701864752154032141)
              ·
                refine ⟨217729205513199282057762053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580611214701864752154032141 217729205513199282057762053)
                ·
                  refine ⟨40824226033724865385830385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217729205513199282057762053 40824226033724865385830385)
                  ·
                    refine ⟨30618169525293649039372789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40824226033724865385830385 30618169525293649039372789)
                    ·
                      refine ⟨2870453392996279597441199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30618169525293649039372789 2870453392996279597441199)
                      ·
                        rfl

theorem cell23_5590188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_5590188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590188 prefixEnd_5590188 := by exact prefixLift 5590188
  have htrace : WordTrace (prefixWord ++ tailWord_5590188) baseStart_5590188 baseEnd_5590188 := by
    simpa [prefixWord, tailWord_5590188, baseEnd_5590188] using wordTrace_append hprefix tailTrace_5590188
  have hstable : (prefixWord ++ tailWord_5590188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590188).length < 2 ^ (prefixWord ++ tailWord_5590188).sum := by decide
  have hdescent : baseEnd_5590188 < baseStart_5590188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590209 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5590209 : Nat := 118140960795 + 5590209 * 2 ^ 59
def prefixEnd_5590209 : Nat := 4983230072969 + 3 ^ 40 * 5590209 * 2
def baseEnd_5590209 : Nat := 2870464176090024015278603

theorem tailTrace_5590209 : CollatzResearch.WordTrace tailWord_5590209 prefixEnd_5590209 2870464176090024015278603 := by
  unfold tailWord_5590209
  simp only [CollatzResearch.WordTrace]
  refine ⟨203891672604634999532237681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135927781736423333021491787 203891672604634999532237681)
  ·
    refine ⟨152918754453476249649178261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203891672604634999532237681 152918754453476249649178261)
    ·
      refine ⟨7168066615006699202305231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152918754453476249649178261 7168066615006699202305231)
      ·
        refine ⟨10752099922510048803457847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7168066615006699202305231 10752099922510048803457847)
        ·
          refine ⟨16128149883765073205186771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10752099922510048803457847 16128149883765073205186771)
          ·
            refine ⟨24192224825647609807780157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16128149883765073205186771 24192224825647609807780157)
            ·
              refine ⟨9072084309617853677917559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24192224825647609807780157 9072084309617853677917559)
              ·
                refine ⟨13608126464426780516876339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9072084309617853677917559 13608126464426780516876339)
                ·
                  refine ⟨20412189696640170775314509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13608126464426780516876339 20412189696640170775314509)
                  ·
                    refine ⟨7654571136240064040742941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20412189696640170775314509 7654571136240064040742941)
                    ·
                      refine ⟨2870464176090024015278603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654571136240064040742941 2870464176090024015278603)
                      ·
                        rfl

theorem cell23_5590209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5590209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590209 prefixEnd_5590209 := by exact prefixLift 5590209
  have htrace : WordTrace (prefixWord ++ tailWord_5590209) baseStart_5590209 baseEnd_5590209 := by
    simpa [prefixWord, tailWord_5590209, baseEnd_5590209] using wordTrace_append hprefix tailTrace_5590209
  have hstable : (prefixWord ++ tailWord_5590209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590209).length < 2 ^ (prefixWord ++ tailWord_5590209).sum := by decide
  have hdescent : baseEnd_5590209 < baseStart_5590209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590260 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5590260 : Nat := 118140960795 + 5590260 * 2 ^ 59
def prefixEnd_5590260 : Nat := 4983230072969 + 3 ^ 40 * 5590260 * 2
def baseEnd_5590260 : Nat := 2870490363603403315740869

theorem tailTrace_5590260 : CollatzResearch.WordTrace tailWord_5590260 prefixEnd_5590260 2870490363603403315740869 := by
  unfold tailWord_5590260
  simp only [CollatzResearch.WordTrace]
  refine ⟨101946766363725117621172117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135929021818300156828229489 101946766363725117621172117)
  ·
    refine ⟨4778754673299614888492443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101946766363725117621172117 4778754673299614888492443)
    ·
      refine ⟨7168132009949422332738665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4778754673299614888492443 7168132009949422332738665)
      ·
        refine ⟨5376099007462066749553999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7168132009949422332738665 5376099007462066749553999)
        ·
          refine ⟨8064148511193100124330999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376099007462066749553999 8064148511193100124330999)
          ·
            refine ⟨12096222766789650186496499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064148511193100124330999 12096222766789650186496499)
            ·
              refine ⟨18144334150184475279744749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12096222766789650186496499 18144334150184475279744749)
              ·
                refine ⟨6804125306319178229904281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18144334150184475279744749 6804125306319178229904281)
                ·
                  refine ⟨5103093979739383672428211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6804125306319178229904281 5103093979739383672428211)
                  ·
                    refine ⟨7654640969609075508642317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5103093979739383672428211 7654640969609075508642317)
                    ·
                      refine ⟨2870490363603403315740869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654640969609075508642317 2870490363603403315740869)
                      ·
                        rfl

theorem cell23_5590260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5590260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590260 prefixEnd_5590260 := by exact prefixLift 5590260
  have htrace : WordTrace (prefixWord ++ tailWord_5590260) baseStart_5590260 baseEnd_5590260 := by
    simpa [prefixWord, tailWord_5590260, baseEnd_5590260] using wordTrace_append hprefix tailTrace_5590260
  have hstable : (prefixWord ++ tailWord_5590260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590260).length < 2 ^ (prefixWord ++ tailWord_5590260).sum := by decide
  have hdescent : baseEnd_5590260 < baseStart_5590260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590265 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_5590265 : Nat := 118140960795 + 5590265 * 2 ^ 59
def prefixEnd_5590265 : Nat := 4983230072969 + 3 ^ 40 * 5590265 * 2
def baseEnd_5590265 : Nat := 2870492931006675796178345

theorem tailTrace_5590265 : CollatzResearch.WordTrace tailWord_5590265 prefixEnd_5590265 2870492931006675796178345 := by
  unfold tailWord_5590265
  simp only [CollatzResearch.WordTrace]
  refine ⟨203893715092432121096276249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135929143394954747397517499 203893715092432121096276249)
  ·
    refine ⟨152920286319324090822207187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203893715092432121096276249 152920286319324090822207187)
    ·
      refine ⟨229380429478986136233310781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152920286319324090822207187 229380429478986136233310781)
      ·
        refine ⟨86017661054619801087491543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229380429478986136233310781 86017661054619801087491543)
        ·
          refine ⟨129026491581929701631237315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86017661054619801087491543 129026491581929701631237315)
          ·
            refine ⟨193539737372894552446855973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129026491581929701631237315 193539737372894552446855973)
            ·
              refine ⟨36288700757417728583785495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193539737372894552446855973 36288700757417728583785495)
              ·
                refine ⟨54433051136126592875678243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36288700757417728583785495 54433051136126592875678243)
                ·
                  refine ⟨81649576704189889313517365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54433051136126592875678243 81649576704189889313517365)
                  ·
                    refine ⟨7654647816017802123142253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81649576704189889313517365 7654647816017802123142253)
                    ·
                      refine ⟨2870492931006675796178345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654647816017802123142253 2870492931006675796178345)
                      ·
                        rfl

theorem cell23_5590265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_5590265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590265 prefixEnd_5590265 := by exact prefixLift 5590265
  have htrace : WordTrace (prefixWord ++ tailWord_5590265) baseStart_5590265 baseEnd_5590265 := by
    simpa [prefixWord, tailWord_5590265, baseEnd_5590265] using wordTrace_append hprefix tailTrace_5590265
  have hstable : (prefixWord ++ tailWord_5590265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590265).length < 2 ^ (prefixWord ++ tailWord_5590265).sum := by decide
  have hdescent : baseEnd_5590265 < baseStart_5590265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590295 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_5590295 : Nat := 118140960795 + 5590295 * 2 ^ 59
def prefixEnd_5590295 : Nat := 4983230072969 + 3 ^ 40 * 5590295 * 2
def baseEnd_5590295 : Nat := 2870508335426310678803207

theorem tailTrace_5590295 : CollatzResearch.WordTrace tailWord_5590295 prefixEnd_5590295 2870508335426310678803207 := by
  unfold tailWord_5590295
  simp only [CollatzResearch.WordTrace]
  refine ⟨203894809282323436219868339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135929872854882290813245559 203894809282323436219868339)
  ·
    refine ⟨305842213923485154329802509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203894809282323436219868339 305842213923485154329802509)
    ·
      refine ⟨114690830221306932873675941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305842213923485154329802509 114690830221306932873675941)
      ·
        refine ⟨21504530666495049913814239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114690830221306932873675941 21504530666495049913814239)
        ·
          refine ⟨32256795999742574870721359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21504530666495049913814239 32256795999742574870721359)
          ·
            refine ⟨48385193999613862306082039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32256795999742574870721359 48385193999613862306082039)
            ·
              refine ⟨72577790999420793459123059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48385193999613862306082039 72577790999420793459123059)
              ·
                refine ⟨108866686499131190188684589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72577790999420793459123059 108866686499131190188684589)
                ·
                  refine ⟨40825007437174196320756721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108866686499131190188684589 40825007437174196320756721)
                  ·
                    refine ⟨30618755577880647240567541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40825007437174196320756721 30618755577880647240567541)
                    ·
                      refine ⟨2870508335426310678803207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30618755577880647240567541 2870508335426310678803207)
                      ·
                        rfl

theorem cell23_5590295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_5590295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590295 prefixEnd_5590295 := by exact prefixLift 5590295
  have htrace : WordTrace (prefixWord ++ tailWord_5590295) baseStart_5590295 baseEnd_5590295 := by
    simpa [prefixWord, tailWord_5590295, baseEnd_5590295] using wordTrace_append hprefix tailTrace_5590295
  have hstable : (prefixWord ++ tailWord_5590295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590295).length < 2 ^ (prefixWord ++ tailWord_5590295).sum := by decide
  have hdescent : baseEnd_5590295 < baseStart_5590295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590305 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5590305 : Nat := 118140960795 + 5590305 * 2 ^ 59
def prefixEnd_5590305 : Nat := 4983230072969 + 3 ^ 40 * 5590305 * 2
def baseEnd_5590305 : Nat := 2870513470232855639678161

theorem tailTrace_5590305 : CollatzResearch.WordTrace tailWord_5590305 prefixEnd_5590305 2870513470232855639678161 := by
  unfold tailWord_5590305
  simp only [CollatzResearch.WordTrace]
  refine ⟨203895174012287207927732369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135930116008191471951821579 203895174012287207927732369)
  ·
    refine ⟨152921380509215405945799277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203895174012287207927732369 152921380509215405945799277)
    ·
      refine ⟨57345517690955777229674729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152921380509215405945799277 57345517690955777229674729)
      ·
        refine ⟨43009138268216832922256047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57345517690955777229674729 43009138268216832922256047)
        ·
          refine ⟨64513707402325249383384071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43009138268216832922256047 64513707402325249383384071)
          ·
            refine ⟨96770561103487874075076107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64513707402325249383384071 96770561103487874075076107)
            ·
              refine ⟨145155841655231811112614161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96770561103487874075076107 145155841655231811112614161)
              ·
                refine ⟨108866881241423858334460621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145155841655231811112614161 108866881241423858334460621)
                ·
                  refine ⟨40825080465533946875422733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108866881241423858334460621 40825080465533946875422733)
                  ·
                    refine ⟨15309405174575230078283525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40825080465533946875422733 15309405174575230078283525)
                    ·
                      refine ⟨2870513470232855639678161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15309405174575230078283525 2870513470232855639678161)
                      ·
                        rfl

theorem cell23_5590305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5590305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590305 prefixEnd_5590305 := by exact prefixLift 5590305
  have htrace : WordTrace (prefixWord ++ tailWord_5590305) baseStart_5590305 baseEnd_5590305 := by
    simpa [prefixWord, tailWord_5590305, baseEnd_5590305] using wordTrace_append hprefix tailTrace_5590305
  have hstable : (prefixWord ++ tailWord_5590305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590305).length < 2 ^ (prefixWord ++ tailWord_5590305).sum := by decide
  have hdescent : baseEnd_5590305 < baseStart_5590305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590312 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5590312 : Nat := 118140960795 + 5590312 * 2 ^ 59
def prefixEnd_5590312 : Nat := 4983230072969 + 3 ^ 40 * 5590312 * 2
def baseEnd_5590312 : Nat := 2870517064597437112290629

theorem tailTrace_5590312 : CollatzResearch.WordTrace tailWord_5590312 prefixEnd_5590312 2870517064597437112290629 := by
  unfold tailWord_5590312
  simp only [CollatzResearch.WordTrace]
  refine ⟨101947714661630924061618595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135930286215507898748824793 101947714661630924061618595)
  ·
    refine ⟨152921571992446386092427893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101947714661630924061618595 152921571992446386092427893)
    ·
      refine ⟨14336397374291848696165115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152921571992446386092427893 14336397374291848696165115)
      ·
        refine ⟨21504596061437773044247673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14336397374291848696165115 21504596061437773044247673)
        ·
          refine ⟨16128447046078329783185755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21504596061437773044247673 16128447046078329783185755)
          ·
            refine ⟨24192670569117494674778633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16128447046078329783185755 24192670569117494674778633)
            ·
              refine ⟨18144502926838121006083975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24192670569117494674778633 18144502926838121006083975)
              ·
                refine ⟨27216754390257181509125963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18144502926838121006083975 27216754390257181509125963)
                ·
                  refine ⟨40825131585385772263688945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27216754390257181509125963 40825131585385772263688945)
                  ·
                    refine ⟨30618848689039329197766709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40825131585385772263688945 30618848689039329197766709)
                    ·
                      refine ⟨2870517064597437112290629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30618848689039329197766709 2870517064597437112290629)
                      ·
                        rfl

theorem cell23_5590312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5590312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590312 prefixEnd_5590312 := by exact prefixLift 5590312
  have htrace : WordTrace (prefixWord ++ tailWord_5590312) baseStart_5590312 baseEnd_5590312 := by
    simpa [prefixWord, tailWord_5590312, baseEnd_5590312] using wordTrace_append hprefix tailTrace_5590312
  have hstable : (prefixWord ++ tailWord_5590312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590312).length < 2 ^ (prefixWord ++ tailWord_5590312).sum := by decide
  have hdescent : baseEnd_5590312 < baseStart_5590312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590332 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_5590332 : Nat := 118140960795 + 5590332 * 2 ^ 59
def prefixEnd_5590332 : Nat := 4983230072969 + 3 ^ 40 * 5590332 * 2
def baseEnd_5590332 : Nat := 956842444736842344680179

theorem tailTrace_5590332 : CollatzResearch.WordTrace tailWord_5590332 prefixEnd_5590332 956842444736842344680179 := by
  unfold tailWord_5590332
  simp only [CollatzResearch.WordTrace]
  refine ⟨101948079391594695769482625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135930772522126261025976833 101948079391594695769482625)
  ·
    refine ⟨76461059543696021827111969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101948079391594695769482625 76461059543696021827111969)
    ·
      refine ⟨57345794657772016370333977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76461059543696021827111969 57345794657772016370333977)
      ·
        refine ⟨43009345993329012277750483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57345794657772016370333977 43009345993329012277750483)
        ·
          refine ⟨64514018989993518416625725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43009345993329012277750483 64514018989993518416625725)
          ·
            refine ⟨24192757121247569406234647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64514018989993518416625725 24192757121247569406234647)
            ·
              refine ⟨36289135681871354109351971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24192757121247569406234647 36289135681871354109351971)
              ·
                refine ⟨54433703522807031164027957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36289135681871354109351971 54433703522807031164027957)
                ·
                  refine ⟨5103159705263159171627621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54433703522807031164027957 5103159705263159171627621)
                  ·
                    refine ⟨956842444736842344680179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5103159705263159171627621 956842444736842344680179)
                    ·
                      rfl

theorem cell23_5590332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_5590332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590332 prefixEnd_5590332 := by exact prefixLift 5590332
  have htrace : WordTrace (prefixWord ++ tailWord_5590332) baseStart_5590332 baseEnd_5590332 := by
    simpa [prefixWord, tailWord_5590332, baseEnd_5590332] using wordTrace_append hprefix tailTrace_5590332
  have hstable : (prefixWord ++ tailWord_5590332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590332).length < 2 ^ (prefixWord ++ tailWord_5590332).sum := by decide
  have hdescent : baseEnd_5590332 < baseStart_5590332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590362 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_5590362 : Nat := 118140960795 + 5590362 * 2 ^ 59
def prefixEnd_5590362 : Nat := 4983230072969 + 3 ^ 40 * 5590362 * 2
def baseEnd_5590362 : Nat := 318949193181129101851711

theorem tailTrace_5590362 : CollatzResearch.WordTrace tailWord_5590362 prefixEnd_5590362 318949193181129101851711 := by
  unfold tailWord_5590362
  simp only [CollatzResearch.WordTrace]
  refine ⟨50974313243270176665639335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135931501982053804441704893 50974313243270176665639335)
  ·
    refine ⟨76461469864905264998459003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50974313243270176665639335 76461469864905264998459003)
    ·
      refine ⟨114692204797357897497688505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76461469864905264998459003 114692204797357897497688505)
      ·
        refine ⟨86019153598018423123266379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114692204797357897497688505 86019153598018423123266379)
        ·
          refine ⟨129028730397027634684899569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86019153598018423123266379 129028730397027634684899569)
          ·
            refine ⟨96771547797770726013674677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129028730397027634684899569 96771547797770726013674677)
            ·
              refine ⟨9072332606041005563782001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96771547797770726013674677 9072332606041005563782001)
              ·
                refine ⟨6804249454530754172836501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9072332606041005563782001 6804249454530754172836501)
                ·
                  refine ⟨318949193181129101851711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6804249454530754172836501 318949193181129101851711)
                  ·
                    rfl

theorem cell23_5590362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_5590362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590362 prefixEnd_5590362 := by exact prefixLift 5590362
  have htrace : WordTrace (prefixWord ++ tailWord_5590362) baseStart_5590362 baseEnd_5590362 := by
    simpa [prefixWord, tailWord_5590362, baseEnd_5590362] using wordTrace_append hprefix tailTrace_5590362
  have hstable : (prefixWord ++ tailWord_5590362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590362).length < 2 ^ (prefixWord ++ tailWord_5590362).sum := by decide
  have hdescent : baseEnd_5590362 < baseStart_5590362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590385 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_5590385 : Nat := 118140960795 + 5590385 * 2 ^ 59
def prefixEnd_5590385 : Nat := 4983230072969 + 3 ^ 40 * 5590385 * 2
def baseEnd_5590385 : Nat := 2870554548685215326677793

theorem tailTrace_5590385 : CollatzResearch.WordTrace tailWord_5590385 prefixEnd_5590385 2870554548685215326677793 := by
  unfold tailWord_5590385
  simp only [CollatzResearch.WordTrace]
  refine ⟨203898091851997381590644609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135932061234664921060429739 203898091851997381590644609)
  ·
    refine ⟨152923568888998036192983457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203898091851997381590644609 152923568888998036192983457)
    ·
      refine ⟨114692676666748527144737593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152923568888998036192983457 114692676666748527144737593)
      ·
        refine ⟨86019507500061395358553195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114692676666748527144737593 86019507500061395358553195)
        ·
          refine ⟨129029261250092093037829793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86019507500061395358553195 129029261250092093037829793)
          ·
            refine ⟨96771945937569069778372345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129029261250092093037829793 96771945937569069778372345)
            ·
              refine ⟨72578959453176802333779259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96771945937569069778372345 72578959453176802333779259)
              ·
                refine ⟨108868439179765203500668889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72578959453176802333779259 108868439179765203500668889)
                ·
                  refine ⟨81651329384823902625501667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108868439179765203500668889 81651329384823902625501667)
                  ·
                    refine ⟨122476994077235853938252501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81651329384823902625501667 122476994077235853938252501)
                    ·
                      refine ⟨2870554548685215326677793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122476994077235853938252501 2870554548685215326677793)
                      ·
                        rfl

theorem cell23_5590385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_5590385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590385 prefixEnd_5590385 := by exact prefixLift 5590385
  have htrace : WordTrace (prefixWord ++ tailWord_5590385) baseStart_5590385 baseEnd_5590385 := by
    simpa [prefixWord, tailWord_5590385, baseEnd_5590385] using wordTrace_append hprefix tailTrace_5590385
  have hstable : (prefixWord ++ tailWord_5590385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590385).length < 2 ^ (prefixWord ++ tailWord_5590385).sum := by decide
  have hdescent : baseEnd_5590385 < baseStart_5590385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590430 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_5590430 : Nat := 118140960795 + 5590430 * 2 ^ 59
def prefixEnd_5590430 : Nat := 4983230072969 + 3 ^ 40 * 5590430 * 2
def baseEnd_5590430 : Nat := 318953072812740850068343

theorem tailTrace_5590430 : CollatzResearch.WordTrace tailWord_5590430 prefixEnd_5590430 318953072812740850068343 := by
  unfold tailWord_5590430
  simp only [CollatzResearch.WordTrace]
  refine ⟨25487466642104294284504093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135933155424556236184021829 25487466642104294284504093)
  ·
    refine ⟨9557799990789110356689035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25487466642104294284504093 9557799990789110356689035)
    ·
      refine ⟨14336699986183665535033553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9557799990789110356689035 14336699986183665535033553)
      ·
        refine ⟨10752524989637749151275165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14336699986183665535033553 10752524989637749151275165)
        ·
          refine ⟨4032196871114155931728187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10752524989637749151275165 4032196871114155931728187)
          ·
            refine ⟨6048295306671233897592281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032196871114155931728187 6048295306671233897592281)
            ·
              refine ⟨4536221480003425423194211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048295306671233897592281 4536221480003425423194211)
              ·
                refine ⟨6804332220005138134791317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536221480003425423194211 6804332220005138134791317)
                ·
                  refine ⟨318953072812740850068343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6804332220005138134791317 318953072812740850068343)
                  ·
                    rfl

theorem cell23_5590430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_5590430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590430 prefixEnd_5590430 := by exact prefixLift 5590430
  have htrace : WordTrace (prefixWord ++ tailWord_5590430) baseStart_5590430 baseEnd_5590430 := by
    simpa [prefixWord, tailWord_5590430, baseEnd_5590430] using wordTrace_append hprefix tailTrace_5590430
  have hstable : (prefixWord ++ tailWord_5590430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590430).length < 2 ^ (prefixWord ++ tailWord_5590430).sum := by decide
  have hdescent : baseEnd_5590430 < baseStart_5590430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590432 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_5590432 : Nat := 118140960795 + 5590432 * 2 ^ 59
def prefixEnd_5590432 : Nat := 4983230072969 + 3 ^ 40 * 5590432 * 2
def baseEnd_5590432 : Nat := 2870578682275976642790077

theorem tailTrace_5590432 : CollatzResearch.WordTrace tailWord_5590432 prefixEnd_5590432 2870578682275976642790077 := by
  unfold tailWord_5590432
  simp only [CollatzResearch.WordTrace]
  refine ⟨101949903041413554308802775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135933204055218072411737033 101949903041413554308802775)
  ·
    refine ⟨152924854562120331463204163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101949903041413554308802775 152924854562120331463204163)
    ·
      refine ⟨229387281843180497194806245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152924854562120331463204163 229387281843180497194806245)
      ·
        refine ⟨43010115345596343224026171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229387281843180497194806245 43010115345596343224026171)
        ·
          refine ⟨64515173018394514836039257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43010115345596343224026171 64515173018394514836039257)
          ·
            refine ⟨48386379763795886127029443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64515173018394514836039257 48386379763795886127029443)
            ·
              refine ⟨72579569645693829190544165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48386379763795886127029443 72579569645693829190544165)
              ·
                refine ⟨13608669308567592973227031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72579569645693829190544165 13608669308567592973227031)
                ·
                  refine ⟨20413003962851389459840547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13608669308567592973227031 20413003962851389459840547)
                  ·
                    refine ⟨30619505944277084189760821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20413003962851389459840547 30619505944277084189760821)
                    ·
                      refine ⟨2870578682275976642790077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30619505944277084189760821 2870578682275976642790077)
                      ·
                        rfl

theorem cell23_5590432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_5590432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590432 prefixEnd_5590432 := by exact prefixLift 5590432
  have htrace : WordTrace (prefixWord ++ tailWord_5590432) baseStart_5590432 baseEnd_5590432 := by
    simpa [prefixWord, tailWord_5590432, baseEnd_5590432] using wordTrace_append hprefix tailTrace_5590432
  have hstable : (prefixWord ++ tailWord_5590432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590432).length < 2 ^ (prefixWord ++ tailWord_5590432).sum := by decide
  have hdescent : baseEnd_5590432 < baseStart_5590432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590449 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5590449 : Nat := 118140960795 + 5590449 * 2 ^ 59
def prefixEnd_5590449 : Nat := 4983230072969 + 3 ^ 40 * 5590449 * 2
def baseEnd_5590449 : Nat := 2870587411447103076277499

theorem tailTrace_5590449 : CollatzResearch.WordTrace tailWord_5590449 prefixEnd_5590449 2870587411447103076277499 := by
  unfold tailWord_5590449
  simp only [CollatzResearch.WordTrace]
  refine ⟨203900426123765520520974401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135933617415843680347316267 203900426123765520520974401)
  ·
    refine ⟨152925319592824140390730801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203900426123765520520974401 152925319592824140390730801)
    ·
      refine ⟨114693989694618105293048101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152925319592824140390730801 114693989694618105293048101)
      ·
        refine ⟨21505123067740894742446519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114693989694618105293048101 21505123067740894742446519)
        ·
          refine ⟨32257684601611342113669779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21505123067740894742446519 32257684601611342113669779)
          ·
            refine ⟨48386526902417013170504669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32257684601611342113669779 48386526902417013170504669)
            ·
              refine ⟨18144947588406379938939251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48386526902417013170504669 18144947588406379938939251)
              ·
                refine ⟨27217421382609569908408877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18144947588406379938939251 27217421382609569908408877)
                ·
                  refine ⟨10206533018478588715653329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27217421382609569908408877 10206533018478588715653329)
                  ·
                    refine ⟨7654899763858941536739997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10206533018478588715653329 7654899763858941536739997)
                    ·
                      refine ⟨2870587411447103076277499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654899763858941536739997 2870587411447103076277499)
                      ·
                        rfl

theorem cell23_5590449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5590449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590449 prefixEnd_5590449 := by exact prefixLift 5590449
  have htrace : WordTrace (prefixWord ++ tailWord_5590449) baseStart_5590449 baseEnd_5590449 := by
    simpa [prefixWord, tailWord_5590449, baseEnd_5590449] using wordTrace_append hprefix tailTrace_5590449
  have hstable : (prefixWord ++ tailWord_5590449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590449).length < 2 ^ (prefixWord ++ tailWord_5590449).sum := by decide
  have hdescent : baseEnd_5590449 < baseStart_5590449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590479 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 3]
def baseStart_5590479 : Nat := 118140960795 + 5590479 * 2 ^ 59
def prefixEnd_5590479 : Nat := 4983230072969 + 3 ^ 40 * 5590479 * 2
def baseEnd_5590479 : Nat := 2870602815866737958902361

theorem tailTrace_5590479 : CollatzResearch.WordTrace tailWord_5590479 prefixEnd_5590479 2870602815866737958902361 := by
  unfold tailWord_5590479
  simp only [CollatzResearch.WordTrace]
  refine ⟨203901520313656835644566491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135934346875771223763044327 203901520313656835644566491)
  ·
    refine ⟨305852280470485253466849737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203901520313656835644566491 305852280470485253466849737)
    ·
      refine ⟨229389210352863940100137303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305852280470485253466849737 229389210352863940100137303)
      ·
        refine ⟨344083815529295910150205955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229389210352863940100137303 344083815529295910150205955)
        ·
          refine ⟨516125723293943865225308933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344083815529295910150205955 516125723293943865225308933)
          ·
            refine ⟨96773573117614474729745425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 516125723293943865225308933 96773573117614474729745425)
            ·
              refine ⟨72580179838210856047309069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96773573117614474729745425 72580179838210856047309069)
              ·
                refine ⟨27217567439329071017740901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72580179838210856047309069 27217567439329071017740901)
                ·
                  refine ⟨5103293894874200815826419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27217567439329071017740901 5103293894874200815826419)
                  ·
                    refine ⟨7654940842311301223739629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5103293894874200815826419 7654940842311301223739629)
                    ·
                      refine ⟨2870602815866737958902361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7654940842311301223739629 2870602815866737958902361)
                      ·
                        rfl

theorem cell23_5590479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_5590479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590479 prefixEnd_5590479 := by exact prefixLift 5590479
  have htrace : WordTrace (prefixWord ++ tailWord_5590479) baseStart_5590479 baseEnd_5590479 := by
    simpa [prefixWord, tailWord_5590479, baseEnd_5590479] using wordTrace_append hprefix tailTrace_5590479
  have hstable : (prefixWord ++ tailWord_5590479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590479).length < 2 ^ (prefixWord ++ tailWord_5590479).sum := by decide
  have hdescent : baseEnd_5590479 < baseStart_5590479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590486 : List Nat := [5, 2, 1, 1, 1, 4, 1, 8]
def baseStart_5590486 : Nat := 118140960795 + 5590486 * 2 ^ 59
def prefixEnd_5590486 : Nat := 4983230072969 + 3 ^ 40 * 5590486 * 2
def baseEnd_5590486 : Nat := 106318755934493312278327

theorem tailTrace_5590486 : CollatzResearch.WordTrace tailWord_5590486 prefixEnd_5590486 106318755934493312278327 := by
  unfold tailWord_5590486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12743860976539467240004457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135934517083087650560047541 12743860976539467240004457)
  ·
    refine ⟨9557895732404600430003343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12743860976539467240004457 9557895732404600430003343)
    ·
      refine ⟨14336843598606900645005015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9557895732404600430003343 14336843598606900645005015)
      ·
        refine ⟨21505265397910350967507523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14336843598606900645005015 21505265397910350967507523)
        ·
          refine ⟨32257898096865526451261285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21505265397910350967507523 32257898096865526451261285)
          ·
            refine ⟨6048355893162286209611491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32257898096865526451261285 6048355893162286209611491)
            ·
              refine ⟨9072533839743429314417237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048355893162286209611491 9072533839743429314417237)
              ·
                refine ⟨106318755934493312278327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9072533839743429314417237 106318755934493312278327)
                ·
                  rfl

theorem cell23_5590486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_5590486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590486 prefixEnd_5590486 := by exact prefixLift 5590486
  have htrace : WordTrace (prefixWord ++ tailWord_5590486) baseStart_5590486 baseEnd_5590486 := by
    simpa [prefixWord, tailWord_5590486, baseEnd_5590486] using wordTrace_append hprefix tailTrace_5590486
  have hstable : (prefixWord ++ tailWord_5590486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590486).length < 2 ^ (prefixWord ++ tailWord_5590486).sum := by decide
  have hdescent : baseEnd_5590486 < baseStart_5590486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590519 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 3, 4, 2]
def baseStart_5590519 : Nat := 118140960795 + 5590519 * 2 ^ 59
def prefixEnd_5590519 : Nat := 4983230072969 + 3 ^ 40 * 5590519 * 2
def baseEnd_5590519 : Nat := 2870623355092917802402177

theorem tailTrace_5590519 : CollatzResearch.WordTrace tailWord_5590519 prefixEnd_5590519 2870623355092917802402177 := by
  unfold tailWord_5590519
  simp only [CollatzResearch.WordTrace]
  refine ⟨203902979233511922476022611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135935319489007948317348407 203902979233511922476022611)
  ·
    refine ⟨305854468850267883714033917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203902979233511922476022611 305854468850267883714033917)
    ·
      refine ⟨114695425818850456392762719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305854468850267883714033917 114695425818850456392762719)
      ·
        refine ⟨172043138728275684589144079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114695425818850456392762719 172043138728275684589144079)
        ·
          refine ⟨258064708092413526883716119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172043138728275684589144079 258064708092413526883716119)
          ·
            refine ⟨387097062138620290325574179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258064708092413526883716119 387097062138620290325574179)
            ·
              refine ⟨580645593207930435488361269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387097062138620290325574179 580645593207930435488361269)
              ·
                refine ⟨54435524363243478327033869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 580645593207930435488361269 54435524363243478327033869)
                ·
                  refine ⟨20413321636216304372637701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54435524363243478327033869 20413321636216304372637701)
                  ·
                    refine ⟨3827497806790557069869569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20413321636216304372637701 3827497806790557069869569)
                    ·
                      refine ⟨2870623355092917802402177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827497806790557069869569 2870623355092917802402177)
                      ·
                        rfl

theorem cell23_5590519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_5590519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590519 prefixEnd_5590519 := by exact prefixLift 5590519
  have htrace : WordTrace (prefixWord ++ tailWord_5590519) baseStart_5590519 baseEnd_5590519 := by
    simpa [prefixWord, tailWord_5590519, baseEnd_5590519] using wordTrace_append hprefix tailTrace_5590519
  have hstable : (prefixWord ++ tailWord_5590519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590519).length < 2 ^ (prefixWord ++ tailWord_5590519).sum := by decide
  have hdescent : baseEnd_5590519 < baseStart_5590519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590522 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_5590522 : Nat := 118140960795 + 5590522 * 2 ^ 59
def prefixEnd_5590522 : Nat := 4983230072969 + 3 ^ 40 * 5590522 * 2
def baseEnd_5590522 : Nat := 2870624895534881290664663

theorem tailTrace_5590522 : CollatzResearch.WordTrace tailWord_5590522 prefixEnd_5590522 2870624895534881290664663 := by
  unfold tailWord_5590522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50975772163125263497095455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135935392435000702658921213 50975772163125263497095455)
  ·
    refine ⟨76463658244687895245643183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50975772163125263497095455 76463658244687895245643183)
    ·
      refine ⟨114695487367031842868464775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76463658244687895245643183 114695487367031842868464775)
      ·
        refine ⟨172043231050547764302697163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114695487367031842868464775 172043231050547764302697163)
        ·
          refine ⟨258064846575821646454045745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172043231050547764302697163 258064846575821646454045745)
          ·
            refine ⟨193548634931866234840534309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258064846575821646454045745 193548634931866234840534309)
            ·
              refine ⟨36290369049724919032600183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193548634931866234840534309 36290369049724919032600183)
              ·
                refine ⟨54435553574587378548900275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36290369049724919032600183 54435553574587378548900275)
                ·
                  refine ⟨81653330361881067823350413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54435553574587378548900275 81653330361881067823350413)
                  ·
                    refine ⟨30619998885705400433756405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81653330361881067823350413 30619998885705400433756405)
                    ·
                      refine ⟨2870624895534881290664663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30619998885705400433756405 2870624895534881290664663)
                      ·
                        rfl

theorem cell23_5590522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_5590522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590522 prefixEnd_5590522 := by exact prefixLift 5590522
  have htrace : WordTrace (prefixWord ++ tailWord_5590522) baseStart_5590522 baseEnd_5590522 := by
    simpa [prefixWord, tailWord_5590522, baseEnd_5590522] using wordTrace_append hprefix tailTrace_5590522
  have hstable : (prefixWord ++ tailWord_5590522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590522).length < 2 ^ (prefixWord ++ tailWord_5590522).sum := by decide
  have hdescent : baseEnd_5590522 < baseStart_5590522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590530 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5590530 : Nat := 118140960795 + 5590530 * 2 ^ 59
def prefixEnd_5590530 : Nat := 4983230072969 + 3 ^ 40 * 5590530 * 2
def baseEnd_5590530 : Nat := 2870629003380117259364627

theorem tailTrace_5590530 : CollatzResearch.WordTrace tailWord_5590530 prefixEnd_5590530 2870629003380117259364627 := by
  unfold tailWord_5590530
  simp only [CollatzResearch.WordTrace]
  refine ⟨50975845109118017838668261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135935586957648047569782029 50975845109118017838668261)
  ·
    refine ⟨9557970957959628344750299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50975845109118017838668261 9557970957959628344750299)
    ·
      refine ⟨14336956436939442517125449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9557970957959628344750299 14336956436939442517125449)
      ·
        refine ⟨10752717327704581887844087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14336956436939442517125449 10752717327704581887844087)
        ·
          refine ⟨16129075991556872831766131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10752717327704581887844087 16129075991556872831766131)
          ·
            refine ⟨24193613987335309247649197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16129075991556872831766131 24193613987335309247649197)
            ·
              refine ⟨9072605245250740967868449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24193613987335309247649197 9072605245250740967868449)
              ·
                refine ⟨6804453933938055725901337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9072605245250740967868449 6804453933938055725901337)
                ·
                  refine ⟨5103340450453541794426003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6804453933938055725901337 5103340450453541794426003)
                  ·
                    refine ⟨7655010675680312691639005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5103340450453541794426003 7655010675680312691639005)
                    ·
                      refine ⟨2870629003380117259364627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7655010675680312691639005 2870629003380117259364627)
                      ·
                        rfl

theorem cell23_5590530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5590530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590530 prefixEnd_5590530 := by exact prefixLift 5590530
  have htrace : WordTrace (prefixWord ++ tailWord_5590530) baseStart_5590530 baseEnd_5590530 := by
    simpa [prefixWord, tailWord_5590530, baseEnd_5590530] using wordTrace_append hprefix tailTrace_5590530
  have hstable : (prefixWord ++ tailWord_5590530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590530).length < 2 ^ (prefixWord ++ tailWord_5590530).sum := by decide
  have hdescent : baseEnd_5590530 < baseStart_5590530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590549 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_5590549 : Nat := 118140960795 + 5590549 * 2 ^ 59
def prefixEnd_5590549 : Nat := 4983230072969 + 3 ^ 40 * 5590549 * 2
def baseEnd_5590549 : Nat := 2870638759512552685027039

theorem tailTrace_5590549 : CollatzResearch.WordTrace tailWord_5590549 prefixEnd_5590549 2870638759512552685027039 := by
  unfold tailWord_5590549
  simp only [CollatzResearch.WordTrace]
  refine ⟨203904073423403237599614701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135936048948935491733076467 203904073423403237599614701)
  ·
    refine ⟨76464027533776214099855513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203904073423403237599614701 76464027533776214099855513)
    ·
      refine ⟨57348020650332160574891635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76464027533776214099855513 57348020650332160574891635)
      ·
        refine ⟨86022030975498240862337453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57348020650332160574891635 86022030975498240862337453)
        ·
          refine ⟨32258261615811840323376545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86022030975498240862337453 32258261615811840323376545)
          ·
            refine ⟨24193696211858880242532409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32258261615811840323376545 24193696211858880242532409)
            ·
              refine ⟨18145272158894160181899307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24193696211858880242532409 18145272158894160181899307)
              ·
                refine ⟨27217908238341240272848961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18145272158894160181899307 27217908238341240272848961)
                ·
                  refine ⟨20413431178755930204636721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27217908238341240272848961 20413431178755930204636721)
                  ·
                    refine ⟨15310073384066947653477541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20413431178755930204636721 15310073384066947653477541)
                    ·
                      refine ⟨2870638759512552685027039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15310073384066947653477541 2870638759512552685027039)
                      ·
                        rfl

theorem cell23_5590549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_5590549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590549 prefixEnd_5590549 := by exact prefixLift 5590549
  have htrace : WordTrace (prefixWord ++ tailWord_5590549) baseStart_5590549 baseEnd_5590549 := by
    simpa [prefixWord, tailWord_5590549, baseEnd_5590549] using wordTrace_append hprefix tailTrace_5590549
  have hstable : (prefixWord ++ tailWord_5590549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590549).length < 2 ^ (prefixWord ++ tailWord_5590549).sum := by decide
  have hdescent : baseEnd_5590549 < baseStart_5590549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590593 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 5]
def baseStart_5590593 : Nat := 118140960795 + 5590593 * 2 ^ 59
def prefixEnd_5590593 : Nat := 4983230072969 + 3 ^ 40 * 5590593 * 2
def baseEnd_5590593 : Nat := 318962372517927834764093

theorem tailTrace_5590593 : CollatzResearch.WordTrace tailWord_5590593 prefixEnd_5590593 318962372517927834764093 := by
  unfold tailWord_5590593
  simp only [CollatzResearch.WordTrace]
  refine ⟨203905678235243833114216433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135937118823495888742810955 203905678235243833114216433)
  ·
    refine ⟨152929258676432874835662325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203905678235243833114216433 152929258676432874835662325)
    ·
      refine ⟨14337118000915582015843343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152929258676432874835662325 14337118000915582015843343)
      ·
        refine ⟨21505677001373373023765015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14337118000915582015843343 21505677001373373023765015)
        ·
          refine ⟨32258515502060059535647523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21505677001373373023765015 32258515502060059535647523)
          ·
            refine ⟨48387773253090089303471285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32258515502060059535647523 48387773253090089303471285)
            ·
              refine ⟨4536353742477195872200433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48387773253090089303471285 4536353742477195872200433)
              ·
                refine ⟨3402265306857896904150325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4536353742477195872200433 3402265306857896904150325)
                ·
                  refine ⟨318962372517927834764093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3402265306857896904150325 318962372517927834764093)
                  ·
                    rfl

theorem cell23_5590593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 5].length) (baseStart_5590593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590593 prefixEnd_5590593 := by exact prefixLift 5590593
  have htrace : WordTrace (prefixWord ++ tailWord_5590593) baseStart_5590593 baseEnd_5590593 := by
    simpa [prefixWord, tailWord_5590593, baseEnd_5590593] using wordTrace_append hprefix tailTrace_5590593
  have hstable : (prefixWord ++ tailWord_5590593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590593).length < 2 ^ (prefixWord ++ tailWord_5590593).sum := by decide
  have hdescent : baseEnd_5590593 < baseStart_5590593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590609 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_5590609 : Nat := 118140960795 + 5590609 * 2 ^ 59
def prefixEnd_5590609 : Nat := 4983230072969 + 3 ^ 40 * 5590609 * 2
def baseEnd_5590609 : Nat := 2870669568351822450276763

theorem tailTrace_5590609 : CollatzResearch.WordTrace tailWord_5590609 prefixEnd_5590609 2870669568351822450276763 := by
  unfold tailWord_5590609
  simp only [CollatzResearch.WordTrace]
  refine ⟨203906261803185867846798881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135937507868790578564532587 203906261803185867846798881)
  ·
    refine ⟨152929696352389400885099161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203906261803185867846798881 152929696352389400885099161)
    ·
      refine ⟨114697272264292050663824371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152929696352389400885099161 114697272264292050663824371)
      ·
        refine ⟨172045908396438075995736557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114697272264292050663824371 172045908396438075995736557)
        ·
          refine ⟨64517215648664278498401209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172045908396438075995736557 64517215648664278498401209)
          ·
            refine ⟨48387911736498208873800907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64517215648664278498401209 48387911736498208873800907)
            ·
              refine ⟨72581867604747313310701361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48387911736498208873800907 72581867604747313310701361)
              ·
                refine ⟨54436400703560484983026021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72581867604747313310701361 54436400703560484983026021)
                ·
                  refine ⟨10206825131917590934317379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54436400703560484983026021 10206825131917590934317379)
                  ·
                    refine ⟨15310237697876386401476069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10206825131917590934317379 15310237697876386401476069)
                    ·
                      refine ⟨2870669568351822450276763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15310237697876386401476069 2870669568351822450276763)
                      ·
                        rfl

theorem cell23_5590609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_5590609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590609 prefixEnd_5590609 := by exact prefixLift 5590609
  have htrace : WordTrace (prefixWord ++ tailWord_5590609) baseStart_5590609 baseEnd_5590609 := by
    simpa [prefixWord, tailWord_5590609, baseEnd_5590609] using wordTrace_append hprefix tailTrace_5590609
  have hstable : (prefixWord ++ tailWord_5590609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590609).length < 2 ^ (prefixWord ++ tailWord_5590609).sum := by decide
  have hdescent : baseEnd_5590609 < baseStart_5590609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590659 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 3]
def baseStart_5590659 : Nat := 118140960795 + 5590659 * 2 ^ 59
def prefixEnd_5590659 : Nat := 4983230072969 + 3 ^ 40 * 5590659 * 2
def baseEnd_5590659 : Nat := 2870695242384547254651533

theorem tailTrace_5590659 : CollatzResearch.WordTrace tailWord_5590659 prefixEnd_5590659 2870695242384547254651533 := by
  unfold tailWord_5590659
  simp only [CollatzResearch.WordTrace]
  refine ⟨203908085453004726386119031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135938723635336484257412687 203908085453004726386119031)
  ·
    refine ⟨305862128179507089579178547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203908085453004726386119031 305862128179507089579178547)
    ·
      refine ⟨458793192269260634368767821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305862128179507089579178547 458793192269260634368767821)
      ·
        refine ⟨172047447100972737888287933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458793192269260634368767821 172047447100972737888287933)
        ·
          refine ⟨64517792662864776708107975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172047447100972737888287933 64517792662864776708107975)
          ·
            refine ⟨96776688994297165062161963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64517792662864776708107975 96776688994297165062161963)
            ·
              refine ⟨145165033491445747593242945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96776688994297165062161963 145165033491445747593242945)
              ·
                refine ⟨108873775118584310694932209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145165033491445747593242945 108873775118584310694932209)
                ·
                  refine ⟨81655331338938233021199157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108873775118584310694932209 81655331338938233021199157)
                  ·
                    refine ⟨7655187313025459345737421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81655331338938233021199157 7655187313025459345737421)
                    ·
                      refine ⟨2870695242384547254651533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7655187313025459345737421 2870695242384547254651533)
                      ·
                        rfl

theorem cell23_5590659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_5590659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590659 prefixEnd_5590659 := by exact prefixLift 5590659
  have htrace : WordTrace (prefixWord ++ tailWord_5590659) baseStart_5590659 baseEnd_5590659 := by
    simpa [prefixWord, tailWord_5590659, baseEnd_5590659] using wordTrace_append hprefix tailTrace_5590659
  have hstable : (prefixWord ++ tailWord_5590659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590659).length < 2 ^ (prefixWord ++ tailWord_5590659).sum := by decide
  have hdescent : baseEnd_5590659 < baseStart_5590659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590666 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_5590666 : Nat := 118140960795 + 5590666 * 2 ^ 59
def prefixEnd_5590666 : Nat := 4983230072969 + 3 ^ 40 * 5590666 * 2
def baseEnd_5590666 : Nat := 318966537416569858584889

theorem tailTrace_5590666 : CollatzResearch.WordTrace tailWord_5590666 prefixEnd_5590666 318966537416569858584889 := by
  unfold tailWord_5590666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50977085190994841645405963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135938893842652911054415901 50977085190994841645405963)
  ·
    refine ⟨76465627786492262468108945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50977085190994841645405963 76465627786492262468108945)
    ·
      refine ⟨57349220839869196851081709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76465627786492262468108945 57349220839869196851081709)
      ·
        refine ⟨21505957814950948819155641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57349220839869196851081709 21505957814950948819155641)
        ·
          refine ⟨16129468361213211614366731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21505957814950948819155641 16129468361213211614366731)
          ·
            refine ⟨24194202541819817421550097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16129468361213211614366731 24194202541819817421550097)
            ·
              refine ⟨18145651906364863066162573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24194202541819817421550097 18145651906364863066162573)
              ·
                refine ⟨6804619464886823649810965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18145651906364863066162573 6804619464886823649810965)
                ·
                  refine ⟨318966537416569858584889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6804619464886823649810965 318966537416569858584889)
                  ·
                    rfl

theorem cell23_5590666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_5590666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590666 prefixEnd_5590666 := by exact prefixLift 5590666
  have htrace : WordTrace (prefixWord ++ tailWord_5590666) baseStart_5590666 baseEnd_5590666 := by
    simpa [prefixWord, tailWord_5590666, baseEnd_5590666] using wordTrace_append hprefix tailTrace_5590666
  have hstable : (prefixWord ++ tailWord_5590666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590666).length < 2 ^ (prefixWord ++ tailWord_5590666).sum := by decide
  have hdescent : baseEnd_5590666 < baseStart_5590666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590687 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 1, 4]
def baseStart_5590687 : Nat := 118140960795 + 5590687 * 2 ^ 59
def prefixEnd_5590687 : Nat := 4983230072969 + 3 ^ 40 * 5590687 * 2
def baseEnd_5590687 : Nat := 956903206614291048367135

theorem tailTrace_5590687 : CollatzResearch.WordTrace tailWord_5590687 prefixEnd_5590687 956903206614291048367135 := by
  unfold tailWord_5590687
  simp only [CollatzResearch.WordTrace]
  refine ⟨203909106696903287168138315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135939404464602191445425543 203909106696903287168138315)
  ·
    refine ⟨305863660045354930752207473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203909106696903287168138315 305863660045354930752207473)
    ·
      refine ⟨229397745034016198064155605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305863660045354930752207473 229397745034016198064155605)
      ·
        refine ⟨5376509649234754642128647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 229397745034016198064155605 5376509649234754642128647)
        ·
          refine ⟨8064764473852131963192971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376509649234754642128647 8064764473852131963192971)
          ·
            refine ⟨12097146710778197944789457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064764473852131963192971 12097146710778197944789457)
            ·
              refine ⟨9072860033083648458592093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12097146710778197944789457 9072860033083648458592093)
              ·
                refine ⟨3402322512406368171972035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9072860033083648458592093 3402322512406368171972035)
                ·
                  refine ⟨5103483768609552257958053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402322512406368171972035 5103483768609552257958053)
                  ·
                    refine ⟨956903206614291048367135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5103483768609552257958053 956903206614291048367135)
                    ·
                      rfl

theorem cell23_5590687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 4].length) (baseStart_5590687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590687 prefixEnd_5590687 := by exact prefixLift 5590687
  have htrace : WordTrace (prefixWord ++ tailWord_5590687) baseStart_5590687 baseEnd_5590687 := by
    simpa [prefixWord, tailWord_5590687, baseEnd_5590687] using wordTrace_append hprefix tailTrace_5590687
  have hstable : (prefixWord ++ tailWord_5590687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590687).length < 2 ^ (prefixWord ++ tailWord_5590687).sum := by decide
  have hdescent : baseEnd_5590687 < baseStart_5590687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590753 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_5590753 : Nat := 118140960795 + 5590753 * 2 ^ 59
def prefixEnd_5590753 : Nat := 4983230072969 + 3 ^ 40 * 5590753 * 2
def baseEnd_5590753 : Nat := 2870743509566069886876101

theorem tailTrace_5590753 : CollatzResearch.WordTrace tailWord_5590753 prefixEnd_5590753 2870743509566069886876101 := by
  unfold tailWord_5590753
  simp only [CollatzResearch.WordTrace]
  refine ⟨203911513914664180440040913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135941009276442786960027275 203911513914664180440040913)
  ·
    refine ⟨152933635435998135330030685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203911513914664180440040913 152933635435998135330030685)
    ·
      refine ⟨57350113288499300748761507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152933635435998135330030685 57350113288499300748761507)
      ·
        refine ⟨86025169932748951123142261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57350113288499300748761507 86025169932748951123142261)
        ·
          refine ⟨8064859681195214167794587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86025169932748951123142261 8064859681195214167794587)
          ·
            refine ⟨12097289521792821251691881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064859681195214167794587 12097289521792821251691881)
            ·
              refine ⟨9072967141344615938768911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12097289521792821251691881 9072967141344615938768911)
              ·
                refine ⟨13609450712016923908153367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9072967141344615938768911 13609450712016923908153367)
                ·
                  refine ⟨20414176068025385862230051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13609450712016923908153367 20414176068025385862230051)
                  ·
                    refine ⟨30621264102038078793345077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20414176068025385862230051 30621264102038078793345077)
                    ·
                      refine ⟨2870743509566069886876101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30621264102038078793345077 2870743509566069886876101)
                      ·
                        rfl

theorem cell23_5590753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_5590753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590753 prefixEnd_5590753 := by exact prefixLift 5590753
  have htrace : WordTrace (prefixWord ++ tailWord_5590753) baseStart_5590753 baseEnd_5590753 := by
    simpa [prefixWord, tailWord_5590753, baseEnd_5590753] using wordTrace_append hprefix tailTrace_5590753
  have hstable : (prefixWord ++ tailWord_5590753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590753).length < 2 ^ (prefixWord ++ tailWord_5590753).sum := by decide
  have hdescent : baseEnd_5590753 < baseStart_5590753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590779 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_5590779 : Nat := 118140960795 + 5590779 * 2 ^ 59
def prefixEnd_5590779 : Nat := 4983230072969 + 3 ^ 40 * 5590779 * 2
def baseEnd_5590779 : Nat := 2870756860063086785150981

theorem tailTrace_5590779 : CollatzResearch.WordTrace tailWord_5590779 prefixEnd_5590779 2870756860063086785150981 := by
  unfold tailWord_5590779
  simp only [CollatzResearch.WordTrace]
  refine ⟨203912462212569986880487391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135941641475046657920324927 203912462212569986880487391)
  ·
    refine ⟨305868693318854980320731087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203912462212569986880487391 305868693318854980320731087)
    ·
      refine ⟨458803039978282470481096631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305868693318854980320731087 458803039978282470481096631)
      ·
        refine ⟨688204559967423705721644947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458803039978282470481096631 688204559967423705721644947)
        ·
          refine ⟨1032306839951135558582467421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688204559967423705721644947 1032306839951135558582467421)
          ·
            refine ⟨387115064981675834468425283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032306839951135558582467421 387115064981675834468425283)
            ·
              refine ⟨580672597472513751702637925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387115064981675834468425283 580672597472513751702637925)
              ·
                refine ⟨108876112026096328444244611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580672597472513751702637925 108876112026096328444244611)
                ·
                  refine ⟨163314168039144492666366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108876112026096328444244611 163314168039144492666366917)
                  ·
                    refine ⟨30621406507339592374943797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163314168039144492666366917 30621406507339592374943797)
                    ·
                      refine ⟨2870756860063086785150981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30621406507339592374943797 2870756860063086785150981)
                      ·
                        rfl

theorem cell23_5590779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_5590779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590779 prefixEnd_5590779 := by exact prefixLift 5590779
  have htrace : WordTrace (prefixWord ++ tailWord_5590779) baseStart_5590779 baseEnd_5590779 := by
    simpa [prefixWord, tailWord_5590779, baseEnd_5590779] using wordTrace_append hprefix tailTrace_5590779
  have hstable : (prefixWord ++ tailWord_5590779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590779).length < 2 ^ (prefixWord ++ tailWord_5590779).sum := by decide
  have hdescent : baseEnd_5590779 < baseStart_5590779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590789 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_5590789 : Nat := 118140960795 + 5590789 * 2 ^ 59
def prefixEnd_5590789 : Nat := 4983230072969 + 3 ^ 40 * 5590789 * 2
def baseEnd_5590789 : Nat := 2870761994869631746025935

theorem tailTrace_5590789 : CollatzResearch.WordTrace tailWord_5590789 prefixEnd_5590789 2870761994869631746025935 := by
  unfold tailWord_5590789
  simp only [CollatzResearch.WordTrace]
  refine ⟨203912826942533758588351421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135941884628355839058900947 203912826942533758588351421)
  ·
    refine ⟨76467310103450159470631783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203912826942533758588351421 76467310103450159470631783)
    ·
      refine ⟨114700965155175239205947675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76467310103450159470631783 114700965155175239205947675)
      ·
        refine ⟨172051447732762858808921513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114700965155175239205947675 172051447732762858808921513)
        ·
          refine ⟨129038585799572144106691135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172051447732762858808921513 129038585799572144106691135)
          ·
            refine ⟨193557878699358216160036703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129038585799572144106691135 193557878699358216160036703)
            ·
              refine ⟨290336818049037324240055055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193557878699358216160036703 290336818049037324240055055)
              ·
                refine ⟨435505227073555986360082583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290336818049037324240055055 435505227073555986360082583)
                ·
                  refine ⟨653257840610333979540123875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435505227073555986360082583 653257840610333979540123875)
                  ·
                    refine ⟨979886760915500969310185813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653257840610333979540123875 979886760915500969310185813)
                    ·
                      refine ⟨2870761994869631746025935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 979886760915500969310185813 2870761994869631746025935)
                      ·
                        rfl

theorem cell23_5590789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_5590789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590789 prefixEnd_5590789 := by exact prefixLift 5590789
  have htrace : WordTrace (prefixWord ++ tailWord_5590789) baseStart_5590789 baseEnd_5590789 := by
    simpa [prefixWord, tailWord_5590789, baseEnd_5590789] using wordTrace_append hprefix tailTrace_5590789
  have hstable : (prefixWord ++ tailWord_5590789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590789).length < 2 ^ (prefixWord ++ tailWord_5590789).sum := by decide
  have hdescent : baseEnd_5590789 < baseStart_5590789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590799 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 8]
def baseStart_5590799 : Nat := 118140960795 + 5590799 * 2 ^ 59
def prefixEnd_5590799 : Nat := 4983230072969 + 3 ^ 40 * 5590799 * 2
def baseEnd_5590799 : Nat := 956922376558725568966963

theorem tailTrace_5590799 : CollatzResearch.WordTrace tailWord_5590799 prefixEnd_5590799 956922376558725568966963 := by
  unfold tailWord_5590799
  simp only [CollatzResearch.WordTrace]
  refine ⟨203913191672497530296215451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135942127781665020197476967 203913191672497530296215451)
  ·
    refine ⟨305869787508746295444323177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203913191672497530296215451 305869787508746295444323177)
    ·
      refine ⟨229402340631559721583242383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305869787508746295444323177 229402340631559721583242383)
      ·
        refine ⟨344103510947339582374863575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229402340631559721583242383 344103510947339582374863575)
        ·
          refine ⟨516155266421009373562295363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344103510947339582374863575 516155266421009373562295363)
          ·
            refine ⟨774232899631514060343443045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516155266421009373562295363 774232899631514060343443045)
            ·
              refine ⟨145168668680908886314395571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 774232899631514060343443045 145168668680908886314395571)
              ·
                refine ⟨217753003021363329471593357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145168668680908886314395571 217753003021363329471593357)
                ·
                  refine ⟨81657376133011248551847509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217753003021363329471593357 81657376133011248551847509)
                  ·
                    refine ⟨956922376558725568966963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81657376133011248551847509 956922376558725568966963)
                    ·
                      rfl

theorem cell23_5590799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_5590799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590799 prefixEnd_5590799 := by exact prefixLift 5590799
  have htrace : WordTrace (prefixWord ++ tailWord_5590799) baseStart_5590799 baseEnd_5590799 := by
    simpa [prefixWord, tailWord_5590799, baseEnd_5590799] using wordTrace_append hprefix tailTrace_5590799
  have hstable : (prefixWord ++ tailWord_5590799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590799).length < 2 ^ (prefixWord ++ tailWord_5590799).sum := by decide
  have hdescent : baseEnd_5590799 < baseStart_5590799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590804 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5590804 : Nat := 118140960795 + 5590804 * 2 ^ 59
def prefixEnd_5590804 : Nat := 4983230072969 + 3 ^ 40 * 5590804 * 2
def baseEnd_5590804 : Nat := 2870769697079449187338367

theorem tailTrace_5590804 : CollatzResearch.WordTrace tailWord_5590804 prefixEnd_5590804 2870769697079449187338367 := by
  unfold tailWord_5590804
  simp only [CollatzResearch.WordTrace]
  refine ⟨101956687018739708075073733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135942249358319610766764977 101956687018739708075073733)
  ·
    refine ⟨19116878816013695264076325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101956687018739708075073733 19116878816013695264076325)
    ·
      refine ⟨3584414778002567862014311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19116878816013695264076325 3584414778002567862014311)
      ·
        refine ⟨5376622167003851793021467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584414778002567862014311 5376622167003851793021467)
        ·
          refine ⟨8064933250505777689532201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376622167003851793021467 8064933250505777689532201)
          ·
            refine ⟨6048699937879333267149151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8064933250505777689532201 6048699937879333267149151)
            ·
              refine ⟨9073049906818999900723727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048699937879333267149151 9073049906818999900723727)
              ·
                refine ⟨13609574860228499851085591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073049906818999900723727 13609574860228499851085591)
                ·
                  refine ⟨20414362290342749776628387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13609574860228499851085591 20414362290342749776628387)
                  ·
                    refine ⟨30621543435514124664942581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20414362290342749776628387 30621543435514124664942581)
                    ·
                      refine ⟨2870769697079449187338367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30621543435514124664942581 2870769697079449187338367)
                      ·
                        rfl

theorem cell23_5590804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5590804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590804 prefixEnd_5590804 := by exact prefixLift 5590804
  have htrace : WordTrace (prefixWord ++ tailWord_5590804) baseStart_5590804 baseEnd_5590804 := by
    simpa [prefixWord, tailWord_5590804, baseEnd_5590804] using wordTrace_append hprefix tailTrace_5590804
  have hstable : (prefixWord ++ tailWord_5590804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590804).length < 2 ^ (prefixWord ++ tailWord_5590804).sum := by decide
  have hdescent : baseEnd_5590804 < baseStart_5590804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590816 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_5590816 : Nat := 118140960795 + 5590816 * 2 ^ 59
def prefixEnd_5590816 : Nat := 4983230072969 + 3 ^ 40 * 5590816 * 2
def baseEnd_5590816 : Nat := 956925286282434380129437

theorem tailTrace_5590816 : CollatzResearch.WordTrace tailWord_5590816 prefixEnd_5590816 956925286282434380129437 := by
  unfold tailWord_5590816
  simp only [CollatzResearch.WordTrace]
  refine ⟨101956905856717971099792151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135942541142290628133056201 101956905856717971099792151)
  ·
    refine ⟨152935358785076956649688227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101956905856717971099792151 152935358785076956649688227)
    ·
      refine ⟨229403038177615434974532341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152935358785076956649688227 229403038177615434974532341)
      ·
        refine ⟨21506534829151447028862407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229403038177615434974532341 21506534829151447028862407)
        ·
          refine ⟨32259802243727170543293611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21506534829151447028862407 32259802243727170543293611)
          ·
            refine ⟨48389703365590755814940417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32259802243727170543293611 48389703365590755814940417)
            ·
              refine ⟨36292277524193066861205313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48389703365590755814940417 36292277524193066861205313)
              ·
                refine ⟨27219208143144800145903985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36292277524193066861205313 27219208143144800145903985)
                ·
                  refine ⟨20414406107358600109427989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27219208143144800145903985 20414406107358600109427989)
                  ·
                    refine ⟨956925286282434380129437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20414406107358600109427989 956925286282434380129437)
                    ·
                      rfl

theorem cell23_5590816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_5590816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590816 prefixEnd_5590816 := by exact prefixLift 5590816
  have htrace : WordTrace (prefixWord ++ tailWord_5590816) baseStart_5590816 baseEnd_5590816 := by
    simpa [prefixWord, tailWord_5590816, baseEnd_5590816] using wordTrace_append hprefix tailTrace_5590816
  have hstable : (prefixWord ++ tailWord_5590816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590816).length < 2 ^ (prefixWord ++ tailWord_5590816).sum := by decide
  have hdescent : baseEnd_5590816 < baseStart_5590816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590840 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 1, 4, 2]
def baseStart_5590840 : Nat := 118140960795 + 5590840 * 2 ^ 59
def prefixEnd_5590840 : Nat := 4983230072969 + 3 ^ 40 * 5590840 * 2
def baseEnd_5590840 : Nat := 2870788182383011046488201

theorem tailTrace_5590840 : CollatzResearch.WordTrace tailWord_5590840 prefixEnd_5590840 2870788182383011046488201 := by
  unfold tailWord_5590840
  simp only [CollatzResearch.WordTrace]
  refine ⟨101957343532674497149228987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135943124710232662865638649 101957343532674497149228987)
  ·
    refine ⟨152936015299011745723843481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101957343532674497149228987 152936015299011745723843481)
    ·
      refine ⟨114702011474258809292882611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152936015299011745723843481 114702011474258809292882611)
      ·
        refine ⟨172053017211388213939323917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114702011474258809292882611 172053017211388213939323917)
        ·
          refine ⟨64519881454270580227246469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172053017211388213939323917 64519881454270580227246469)
          ·
            refine ⟨12097477772675733792608713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64519881454270580227246469 12097477772675733792608713)
            ·
              refine ⟨9073108329506800344456535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12097477772675733792608713 9073108329506800344456535)
              ·
                refine ⟨13609662494260200516684803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073108329506800344456535 13609662494260200516684803)
                ·
                  refine ⟨20414493741390300775027205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13609662494260200516684803 20414493741390300775027205)
                  ·
                    refine ⟨3827717576510681395317601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20414493741390300775027205 3827717576510681395317601)
                    ·
                      refine ⟨2870788182383011046488201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827717576510681395317601 2870788182383011046488201)
                      ·
                        rfl

theorem cell23_5590840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_5590840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590840 prefixEnd_5590840 := by exact prefixLift 5590840
  have htrace : WordTrace (prefixWord ++ tailWord_5590840) baseStart_5590840 baseEnd_5590840 := by
    simpa [prefixWord, tailWord_5590840, baseEnd_5590840] using wordTrace_append hprefix tailTrace_5590840
  have hstable : (prefixWord ++ tailWord_5590840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590840).length < 2 ^ (prefixWord ++ tailWord_5590840).sum := by decide
  have hdescent : baseEnd_5590840 < baseStart_5590840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590861 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5590861 : Nat := 118140960795 + 5590861 * 2 ^ 59
def prefixEnd_5590861 : Nat := 4983230072969 + 3 ^ 40 * 5590861 * 2
def baseEnd_5590861 : Nat := 2870798965476755464325605

theorem tailTrace_5590861 : CollatzResearch.WordTrace tailWord_5590861 prefixEnd_5590861 2870798965476755464325605 := by
  unfold tailWord_5590861
  simp only [CollatzResearch.WordTrace]
  refine ⟨203915452998272914884972437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135943635332181943256648291 203915452998272914884972437)
  ·
    refine ⟨9558536859294042885233083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203915452998272914884972437 9558536859294042885233083)
    ·
      refine ⟨14337805288941064327849625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9558536859294042885233083 14337805288941064327849625)
      ·
        refine ⟨10753353966705798245887219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14337805288941064327849625 10753353966705798245887219)
        ·
          refine ⟨16130030950058697368830829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10753353966705798245887219 16130030950058697368830829)
          ·
            refine ⟨6048761606272011513311561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16130030950058697368830829 6048761606272011513311561)
            ·
              refine ⟨4536571204704008634983671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048761606272011513311561 4536571204704008634983671)
              ·
                refine ⟨6804856807056012952475507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536571204704008634983671 6804856807056012952475507)
                ·
                  refine ⟨10207285210584019428713261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6804856807056012952475507 10207285210584019428713261)
                  ·
                    refine ⟨3827731953969007285767473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10207285210584019428713261 3827731953969007285767473)
                    ·
                      refine ⟨2870798965476755464325605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827731953969007285767473 2870798965476755464325605)
                      ·
                        rfl

theorem cell23_5590861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5590861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590861 prefixEnd_5590861 := by exact prefixLift 5590861
  have htrace : WordTrace (prefixWord ++ tailWord_5590861) baseStart_5590861 baseEnd_5590861 := by
    simpa [prefixWord, tailWord_5590861, baseEnd_5590861] using wordTrace_append hprefix tailTrace_5590861
  have hstable : (prefixWord ++ tailWord_5590861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590861).length < 2 ^ (prefixWord ++ tailWord_5590861).sum := by decide
  have hdescent : baseEnd_5590861 < baseStart_5590861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590910 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5590910 : Nat := 118140960795 + 5590910 * 2 ^ 59
def prefixEnd_5590910 : Nat := 4983230072969 + 3 ^ 40 * 5590910 * 2
def baseEnd_5590910 : Nat := 956941375342941924204293

theorem tailTrace_5590910 : CollatzResearch.WordTrace tailWord_5590910 prefixEnd_5590910 956941375342941924204293 := by
  unfold tailWord_5590910
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489655021886924531688273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135944826783396930835670789 25489655021886924531688273)
  ·
    refine ⟨19117241266415193398766205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25489655021886924531688273 19117241266415193398766205)
    ·
      refine ⟨7168965474905697524537327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19117241266415193398766205 7168965474905697524537327)
      ·
        refine ⟨10753448212358546286805991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7168965474905697524537327 10753448212358546286805991)
        ·
          refine ⟨16130172318537819430208987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10753448212358546286805991 16130172318537819430208987)
          ·
            refine ⟨24195258477806729145313481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16130172318537819430208987 24195258477806729145313481)
            ·
              refine ⟨18146443858355046858985111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24195258477806729145313481 18146443858355046858985111)
              ·
                refine ⟨27219665787532570288477667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18146443858355046858985111 27219665787532570288477667)
                ·
                  refine ⟨40829498681298855432716501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27219665787532570288477667 40829498681298855432716501)
                  ·
                    refine ⟨956941375342941924204293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40829498681298855432716501 956941375342941924204293)
                    ·
                      rfl

theorem cell23_5590910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5590910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590910 prefixEnd_5590910 := by exact prefixLift 5590910
  have htrace : WordTrace (prefixWord ++ tailWord_5590910) baseStart_5590910 baseEnd_5590910 := by
    simpa [prefixWord, tailWord_5590910, baseEnd_5590910] using wordTrace_append hprefix tailTrace_5590910
  have hstable : (prefixWord ++ tailWord_5590910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590910).length < 2 ^ (prefixWord ++ tailWord_5590910).sum := by decide
  have hdescent : baseEnd_5590910 < baseStart_5590910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590930 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5590930 : Nat := 118140960795 + 5590930 * 2 ^ 59
def prefixEnd_5590930 : Nat := 4983230072969 + 3 ^ 40 * 5590930 * 2
def baseEnd_5590930 : Nat := 2870834395641915694362787

theorem tailTrace_5590930 : CollatzResearch.WordTrace tailWord_5590930 prefixEnd_5590930 2870834395641915694362787 := by
  unfold tailWord_5590930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50979492408755734917308561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135945313090015293112822829 50979492408755734917308561)
  ·
    refine ⟨38234619306566801187981421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50979492408755734917308561 38234619306566801187981421)
    ·
      refine ⟨14337982239962550445493033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38234619306566801187981421 14337982239962550445493033)
      ·
        refine ⟨10753486679971912834119775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14337982239962550445493033 10753486679971912834119775)
        ·
          refine ⟨16130230019957869251179663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10753486679971912834119775 16130230019957869251179663)
          ·
            refine ⟨24195345029936803876769495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16130230019957869251179663 24195345029936803876769495)
            ·
              refine ⟨36293017544905205815154243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24195345029936803876769495 36293017544905205815154243)
              ·
                refine ⟨54439526317357808722731365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36293017544905205815154243 54439526317357808722731365)
                ·
                  refine ⟨10207411184504589135512131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54439526317357808722731365 10207411184504589135512131)
                  ·
                    refine ⟨15311116776756883703268197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10207411184504589135512131 15311116776756883703268197)
                    ·
                      refine ⟨2870834395641915694362787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15311116776756883703268197 2870834395641915694362787)
                      ·
                        rfl

theorem cell23_5590930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5590930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590930 prefixEnd_5590930 := by exact prefixLift 5590930
  have htrace : WordTrace (prefixWord ++ tailWord_5590930) baseStart_5590930 baseEnd_5590930 := by
    simpa [prefixWord, tailWord_5590930, baseEnd_5590930] using wordTrace_append hprefix tailTrace_5590930
  have hstable : (prefixWord ++ tailWord_5590930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590930).length < 2 ^ (prefixWord ++ tailWord_5590930).sum := by decide
  have hdescent : baseEnd_5590930 < baseStart_5590930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5590964 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_5590964 : Nat := 118140960795 + 5590964 * 2 ^ 59
def prefixEnd_5590964 : Nat := 4983230072969 + 3 ^ 40 * 5590964 * 2
def baseEnd_5590964 : Nat := 2870851853984168561337631

theorem tailTrace_5590964 : CollatzResearch.WordTrace tailWord_5590964 prefixEnd_5590964 2870851853984168561337631 := by
  unfold tailWord_5590964
  simp only [CollatzResearch.WordTrace]
  refine ⟨101959604858449881737985973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135946139811266508983981297 101959604858449881737985973)
  ·
    refine ⟨9558712955479676412936185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101959604858449881737985973 9558712955479676412936185)
    ·
      refine ⟨7169034716609757309702139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9558712955479676412936185 7169034716609757309702139)
      ·
        refine ⟨10753552074914635964553209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169034716609757309702139 10753552074914635964553209)
        ·
          refine ⟨8065164056185976973414907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10753552074914635964553209 8065164056185976973414907)
          ·
            refine ⟨12097746084278965460122361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8065164056185976973414907 12097746084278965460122361)
            ·
              refine ⟨9073309563209224095091771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12097746084278965460122361 9073309563209224095091771)
              ·
                refine ⟨13609964344813836142637657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073309563209224095091771 13609964344813836142637657)
                ·
                  refine ⟨10207473258610377106978243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13609964344813836142637657 10207473258610377106978243)
                  ·
                    refine ⟨15311209887915565660467365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10207473258610377106978243 15311209887915565660467365)
                    ·
                      refine ⟨2870851853984168561337631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15311209887915565660467365 2870851853984168561337631)
                      ·
                        rfl

theorem cell23_5590964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_5590964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5590964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5590964 prefixEnd_5590964 := by exact prefixLift 5590964
  have htrace : WordTrace (prefixWord ++ tailWord_5590964) baseStart_5590964 baseEnd_5590964 := by
    simpa [prefixWord, tailWord_5590964, baseEnd_5590964] using wordTrace_append hprefix tailTrace_5590964
  have hstable : (prefixWord ++ tailWord_5590964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5590964).length < 2 ^ (prefixWord ++ tailWord_5590964).sum := by decide
  have hdescent : baseEnd_5590964 < baseStart_5590964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5590964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591037 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_5591037 : Nat := 118140960795 + 5591037 * 2 ^ 59
def prefixEnd_5591037 : Nat := 4983230072969 + 3 ^ 40 * 5591037 * 2
def baseEnd_5591037 : Nat := 2870889338071946775724795

theorem tailTrace_5591037 : CollatzResearch.WordTrace tailWord_5591037 prefixEnd_5591037 2870889338071946775724795 := by
  unfold tailWord_5591037
  simp only [CollatzResearch.WordTrace]
  refine ⟨203921872245635296943379365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135947914830423531295586243 203921872245635296943379365)
  ·
    refine ⟨38235351046056618176883631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203921872245635296943379365 38235351046056618176883631)
    ·
      refine ⟨57353026569084927265325447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38235351046056618176883631 57353026569084927265325447)
      ·
        refine ⟨86029539853627390897988171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57353026569084927265325447 86029539853627390897988171)
        ·
          refine ⟨129044309780441086346982257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86029539853627390897988171 129044309780441086346982257)
          ·
            refine ⟨96783232335330814760236693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129044309780441086346982257 96783232335330814760236693)
            ·
              refine ⟨4536714015718631941886095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96783232335330814760236693 4536714015718631941886095)
              ·
                refine ⟨6805071023577947912829143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536714015718631941886095 6805071023577947912829143)
                ·
                  refine ⟨10207606535366921869243715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6805071023577947912829143 10207606535366921869243715)
                  ·
                    refine ⟨15311409803050382803865573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10207606535366921869243715 15311409803050382803865573)
                    ·
                      refine ⟨2870889338071946775724795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15311409803050382803865573 2870889338071946775724795)
                      ·
                        rfl

theorem cell23_5591037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_5591037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591037 prefixEnd_5591037 := by exact prefixLift 5591037
  have htrace : WordTrace (prefixWord ++ tailWord_5591037) baseStart_5591037 baseEnd_5591037 := by
    simpa [prefixWord, tailWord_5591037, baseEnd_5591037] using wordTrace_append hprefix tailTrace_5591037
  have hstable : (prefixWord ++ tailWord_5591037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591037).length < 2 ^ (prefixWord ++ tailWord_5591037).sum := by decide
  have hdescent : baseEnd_5591037 < baseStart_5591037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591047 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 2, 4]
def baseStart_5591047 : Nat := 118140960795 + 5591047 * 2 ^ 59
def prefixEnd_5591047 : Nat := 4983230072969 + 3 ^ 40 * 5591047 * 2
def baseEnd_5591047 : Nat := 956964824292830578866583

theorem tailTrace_5591047 : CollatzResearch.WordTrace tailWord_5591047 prefixEnd_5591047 956964824292830578866583 := by
  unfold tailWord_5591047
  simp only [CollatzResearch.WordTrace]
  refine ⟨203922236975599068651243395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135948157983732712434162263 203922236975599068651243395)
  ·
    refine ⟨305883355463398602976865093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203922236975599068651243395 305883355463398602976865093)
    ·
      refine ⟨57353129149387238058162205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305883355463398602976865093 57353129149387238058162205)
      ·
        refine ⟨21507423431020214271810827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57353129149387238058162205 21507423431020214271810827)
        ·
          refine ⟨32261135146530321407716241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21507423431020214271810827 32261135146530321407716241)
          ·
            refine ⟨24195851359897741055787181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32261135146530321407716241 24195851359897741055787181)
            ·
              refine ⟨9073444259961652895920193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24195851359897741055787181 9073444259961652895920193)
              ·
                refine ⟨6805083194971239671940145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9073444259961652895920193 6805083194971239671940145)
                ·
                  refine ⟨5103812396228429753955109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6805083194971239671940145 5103812396228429753955109)
                  ·
                    refine ⟨956964824292830578866583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5103812396228429753955109 956964824292830578866583)
                    ·
                      rfl

theorem cell23_5591047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_5591047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591047 prefixEnd_5591047 := by exact prefixLift 5591047
  have htrace : WordTrace (prefixWord ++ tailWord_5591047) baseStart_5591047 baseEnd_5591047 := by
    simpa [prefixWord, tailWord_5591047, baseEnd_5591047] using wordTrace_append hprefix tailTrace_5591047
  have hstable : (prefixWord ++ tailWord_5591047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591047).length < 2 ^ (prefixWord ++ tailWord_5591047).sum := by decide
  have hdescent : baseEnd_5591047 < baseStart_5591047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591054 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5591054 : Nat := 118140960795 + 5591054 * 2 ^ 59
def prefixEnd_5591054 : Nat := 4983230072969 + 3 ^ 40 * 5591054 * 2
def baseEnd_5591054 : Nat := 2870898067243073209212217

theorem tailTrace_5591054 : CollatzResearch.WordTrace tailWord_5591054 prefixEnd_5591054 2870898067243073209212217 := by
  unfold tailWord_5591054
  simp only [CollatzResearch.WordTrace]
  refine ⟨25490311535821713605843527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135948328191049139231165477 25490311535821713605843527)
  ·
    refine ⟨38235467303732570408765291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25490311535821713605843527 38235467303732570408765291)
    ·
      refine ⟨57353200955598855613147937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38235467303732570408765291 57353200955598855613147937)
      ·
        refine ⟨43014900716699141709860953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57353200955598855613147937 43014900716699141709860953)
        ·
          refine ⟨32261175537524356282395715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43014900716699141709860953 32261175537524356282395715)
          ·
            refine ⟨48391763306286534423593573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32261175537524356282395715 48391763306286534423593573)
            ·
              refine ⟨9073455619928725204423795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48391763306286534423593573 9073455619928725204423795)
              ·
                refine ⟨13610183429893087806635693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073455619928725204423795 13610183429893087806635693)
                ·
                  refine ⟨5103818786209907927488385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13610183429893087806635693 5103818786209907927488385)
                  ·
                    refine ⟨3827864089657430945616289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5103818786209907927488385 3827864089657430945616289)
                    ·
                      refine ⟨2870898067243073209212217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827864089657430945616289 2870898067243073209212217)
                      ·
                        rfl

theorem cell23_5591054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5591054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591054 prefixEnd_5591054 := by exact prefixLift 5591054
  have htrace : WordTrace (prefixWord ++ tailWord_5591054) baseStart_5591054 baseEnd_5591054 := by
    simpa [prefixWord, tailWord_5591054, baseEnd_5591054] using wordTrace_append hprefix tailTrace_5591054
  have hstable : (prefixWord ++ tailWord_5591054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591054).length < 2 ^ (prefixWord ++ tailWord_5591054).sum := by decide
  have hdescent : baseEnd_5591054 < baseStart_5591054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591103 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 4, 6]
def baseStart_5591103 : Nat := 118140960795 + 5591103 * 2 ^ 59
def prefixEnd_5591103 : Nat := 4983230072969 + 3 ^ 40 * 5591103 * 2
def baseEnd_5591103 : Nat := 956974409265047839166497

theorem tailTrace_5591103 : CollatzResearch.WordTrace tailWord_5591103 prefixEnd_5591103 956974409265047839166497 := by
  unfold tailWord_5591103
  simp only [CollatzResearch.WordTrace]
  refine ⟨203924279463396190215281963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135949519642264126810187975 203924279463396190215281963)
  ·
    refine ⟨305886419195094285322922945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203924279463396190215281963 305886419195094285322922945)
    ·
      refine ⟨229414814396320713992192209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305886419195094285322922945 229414814396320713992192209)
      ·
        refine ⟨172061110797240535494144157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229414814396320713992192209 172061110797240535494144157)
        ·
          refine ⟨64522916548965200810304059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172061110797240535494144157 64522916548965200810304059)
          ·
            refine ⟨96784374823447801215456089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64522916548965200810304059 96784374823447801215456089)
            ·
              refine ⟨72588281117585850911592067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96784374823447801215456089 72588281117585850911592067)
              ·
                refine ⟨108882421676378776367388101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72588281117585850911592067 108882421676378776367388101)
                ·
                  refine ⟨20415454064321020568885269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108882421676378776367388101 20415454064321020568885269)
                  ·
                    refine ⟨956974409265047839166497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20415454064321020568885269 956974409265047839166497)
                    ·
                      rfl

theorem cell23_5591103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_5591103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591103 prefixEnd_5591103 := by exact prefixLift 5591103
  have htrace : WordTrace (prefixWord ++ tailWord_5591103) baseStart_5591103 baseEnd_5591103 := by
    simpa [prefixWord, tailWord_5591103, baseEnd_5591103] using wordTrace_append hprefix tailTrace_5591103
  have hstable : (prefixWord ++ tailWord_5591103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591103).length < 2 ^ (prefixWord ++ tailWord_5591103).sum := by decide
  have hdescent : baseEnd_5591103 < baseStart_5591103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591113 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_5591113 : Nat := 118140960795 + 5591113 * 2 ^ 59
def prefixEnd_5591113 : Nat := 4983230072969 + 3 ^ 40 * 5591113 * 2
def baseEnd_5591113 : Nat := 2870928362601688478374445

theorem tailTrace_5591113 : CollatzResearch.WordTrace tailWord_5591113 prefixEnd_5591113 2870928362601688478374445 := by
  unfold tailWord_5591113
  simp only [CollatzResearch.WordTrace]
  refine ⟨203924644193359961923145993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135949762795573307948763995 203924644193359961923145993)
  ·
    refine ⟨152943483145019971442359495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203924644193359961923145993 152943483145019971442359495)
    ·
      refine ⟨229415224717529957163539243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152943483145019971442359495 229415224717529957163539243)
      ·
        refine ⟨344122837076294935745308865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229415224717529957163539243 344122837076294935745308865)
        ·
          refine ⟨258092127807221201808981649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344122837076294935745308865 258092127807221201808981649)
          ·
            refine ⟨193569095855415901356736237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258092127807221201808981649 193569095855415901356736237)
            ·
              refine ⟨72588410945780963008776089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193569095855415901356736237 72588410945780963008776089)
              ·
                refine ⟨54441308209335722256582067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72588410945780963008776089 54441308209335722256582067)
                ·
                  refine ⟨81661962314003583384873101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54441308209335722256582067 81661962314003583384873101)
                  ·
                    refine ⟨30623235867751343769327413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81661962314003583384873101 30623235867751343769327413)
                    ·
                      refine ⟨2870928362601688478374445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30623235867751343769327413 2870928362601688478374445)
                      ·
                        rfl

theorem cell23_5591113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_5591113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591113 prefixEnd_5591113 := by exact prefixLift 5591113
  have htrace : WordTrace (prefixWord ++ tailWord_5591113) baseStart_5591113 baseEnd_5591113 := by
    simpa [prefixWord, tailWord_5591113, baseEnd_5591113] using wordTrace_append hprefix tailTrace_5591113
  have hstable : (prefixWord ++ tailWord_5591113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591113).length < 2 ^ (prefixWord ++ tailWord_5591113).sum := by decide
  have hdescent : baseEnd_5591113 < baseStart_5591113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591160 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_5591160 : Nat := 118140960795 + 5591160 * 2 ^ 59
def prefixEnd_5591160 : Nat := 4983230072969 + 3 ^ 40 * 5591160 * 2
def baseEnd_5591160 : Nat := 2870952496192449794486729

theorem tailTrace_5591160 : CollatzResearch.WordTrace tailWord_5591160 prefixEnd_5591160 2870952496192449794486729 := by
  unfold tailWord_5591160
  simp only [CollatzResearch.WordTrace]
  refine ⟨101963179212094844475053467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135950905616126459300071289 101963179212094844475053467)
  ·
    refine ⟨152944768818142266712580201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101963179212094844475053467 152944768818142266712580201)
    ·
      refine ⟨114708576613606700034435151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152944768818142266712580201 114708576613606700034435151)
      ·
        refine ⟨172062864920410050051652727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114708576613606700034435151 172062864920410050051652727)
        ·
          refine ⟨258094297380615075077479091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172062864920410050051652727 258094297380615075077479091)
          ·
            refine ⟨387141446070922612616218637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258094297380615075077479091 387141446070922612616218637)
            ·
              refine ⟨145178042276595979731081989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387141446070922612616218637 145178042276595979731081989)
              ·
                refine ⟨27220882926861746199577873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145178042276595979731081989 27220882926861746199577873)
                ·
                  refine ⟨20415662195146309649683405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27220882926861746199577873 20415662195146309649683405)
                  ·
                    refine ⟨7655873323179866118631277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20415662195146309649683405 7655873323179866118631277)
                    ·
                      refine ⟨2870952496192449794486729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7655873323179866118631277 2870952496192449794486729)
                      ·
                        rfl

theorem cell23_5591160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_5591160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591160 prefixEnd_5591160 := by exact prefixLift 5591160
  have htrace : WordTrace (prefixWord ++ tailWord_5591160) baseStart_5591160 baseEnd_5591160 := by
    simpa [prefixWord, tailWord_5591160, baseEnd_5591160] using wordTrace_append hprefix tailTrace_5591160
  have hstable : (prefixWord ++ tailWord_5591160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591160).length < 2 ^ (prefixWord ++ tailWord_5591160).sum := by decide
  have hdescent : baseEnd_5591160 < baseStart_5591160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591161 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 2, 2, 2]
def baseStart_5591161 : Nat := 118140960795 + 5591161 * 2 ^ 59
def prefixEnd_5591161 : Nat := 4983230072969 + 3 ^ 40 * 5591161 * 2
def baseEnd_5591161 : Nat := 2870953009673104290574225

theorem tailTrace_5591161 : CollatzResearch.WordTrace tailWord_5591161 prefixEnd_5591161 2870953009673104290574225 := by
  unfold tailWord_5591161
  simp only [CollatzResearch.WordTrace]
  refine ⟨203926394897186066120893337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135950929931457377413928891 203926394897186066120893337)
  ·
    refine ⟨152944796172889549590670003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203926394897186066120893337 152944796172889549590670003)
    ·
      refine ⟨229417194259334324386005005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152944796172889549590670003 229417194259334324386005005)
      ·
        refine ⟨86031447847250371644751877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229417194259334324386005005 86031447847250371644751877)
        ·
          refine ⟨16130896471359444683390977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86031447847250371644751877 16130896471359444683390977)
          ·
            refine ⟨12098172353519583512543233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16130896471359444683390977 12098172353519583512543233)
            ·
              refine ⟨9073629265139687634407425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12098172353519583512543233 9073629265139687634407425)
              ·
                refine ⟨6805221948854765725805569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9073629265139687634407425 6805221948854765725805569)
                ·
                  refine ⟨5103916461641074294354177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6805221948854765725805569 5103916461641074294354177)
                  ·
                    refine ⟨3827937346230805720765633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5103916461641074294354177 3827937346230805720765633)
                    ·
                      refine ⟨2870953009673104290574225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3827937346230805720765633 2870953009673104290574225)
                      ·
                        rfl

theorem cell23_5591161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_5591161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591161 prefixEnd_5591161 := by exact prefixLift 5591161
  have htrace : WordTrace (prefixWord ++ tailWord_5591161) baseStart_5591161 baseEnd_5591161 := by
    simpa [prefixWord, tailWord_5591161, baseEnd_5591161] using wordTrace_append hprefix tailTrace_5591161
  have hstable : (prefixWord ++ tailWord_5591161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591161).length < 2 ^ (prefixWord ++ tailWord_5591161).sum := by decide
  have hdescent : baseEnd_5591161 < baseStart_5591161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591163 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 5, 7]
def baseStart_5591163 : Nat := 118140960795 + 5591163 * 2 ^ 59
def prefixEnd_5591163 : Nat := 4983230072969 + 3 ^ 40 * 5591163 * 2
def baseEnd_5591163 : Nat := 956984678878137760916405

theorem tailTrace_5591163 : CollatzResearch.WordTrace tailWord_5591163 prefixEnd_5591163 956984678878137760916405 := by
  unfold tailWord_5591163
  simp only [CollatzResearch.WordTrace]
  refine ⟨203926467843178820462466143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135950978562119213641644095 203926467843178820462466143)
  ·
    refine ⟨305889701764768230693699215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203926467843178820462466143 305889701764768230693699215)
    ·
      refine ⟨458834552647152346040548823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305889701764768230693699215 458834552647152346040548823)
      ·
        refine ⟨688251828970728519060823235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458834552647152346040548823 688251828970728519060823235)
        ·
          refine ⟨1032377743456092778591234853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688251828970728519060823235 1032377743456092778591234853)
          ·
            refine ⟨193570826898017395985856535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1032377743456092778591234853 193570826898017395985856535)
            ·
              refine ⟨290356240347026093978784803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193570826898017395985856535 290356240347026093978784803)
              ·
                refine ⟨435534360520539140968177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290356240347026093978784803 435534360520539140968177205)
                ·
                  refine ⟨40831346298800544465766613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 435534360520539140968177205 40831346298800544465766613)
                  ·
                    refine ⟨956984678878137760916405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40831346298800544465766613 956984678878137760916405)
                    ·
                      rfl

theorem cell23_5591163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_5591163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591163 prefixEnd_5591163 := by exact prefixLift 5591163
  have htrace : WordTrace (prefixWord ++ tailWord_5591163) baseStart_5591163 baseEnd_5591163 := by
    simpa [prefixWord, tailWord_5591163, baseEnd_5591163] using wordTrace_append hprefix tailTrace_5591163
  have hstable : (prefixWord ++ tailWord_5591163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591163).length < 2 ^ (prefixWord ++ tailWord_5591163).sum := by decide
  have hdescent : baseEnd_5591163 < baseStart_5591163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591183 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_5591183 : Nat := 118140960795 + 5591183 * 2 ^ 59
def prefixEnd_5591183 : Nat := 4983230072969 + 3 ^ 40 * 5591183 * 2
def baseEnd_5591183 : Nat := 2870964306247503204499123

theorem tailTrace_5591183 : CollatzResearch.WordTrace tailWord_5591183 prefixEnd_5591183 2870964306247503204499123 := by
  unfold tailWord_5591183
  simp only [CollatzResearch.WordTrace]
  refine ⟨203927197303106363878194203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135951464868737575918796135 203927197303106363878194203)
  ·
    refine ⟨305890795954659545817291305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203927197303106363878194203 305890795954659545817291305)
    ·
      refine ⟨229418096965994659362968479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305890795954659545817291305 229418096965994659362968479)
      ·
        refine ⟨344127145448991989044452719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229418096965994659362968479 344127145448991989044452719)
        ·
          refine ⟨516190718173487983566679079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344127145448991989044452719 516190718173487983566679079)
          ·
            refine ⟨774286077260231975350018619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516190718173487983566679079 774286077260231975350018619)
            ·
              refine ⟨1161429115890347963025027929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774286077260231975350018619 1161429115890347963025027929)
              ·
                refine ⟨871071836917760972268770947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161429115890347963025027929 871071836917760972268770947)
                ·
                  refine ⟨1306607755376641458403156421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871071836917760972268770947 1306607755376641458403156421)
                  ·
                    refine ⟨244988954133120273450591829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306607755376641458403156421 244988954133120273450591829)
                    ·
                      refine ⟨2870964306247503204499123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 244988954133120273450591829 2870964306247503204499123)
                      ·
                        rfl

theorem cell23_5591183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_5591183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591183 prefixEnd_5591183 := by exact prefixLift 5591183
  have htrace : WordTrace (prefixWord ++ tailWord_5591183) baseStart_5591183 baseEnd_5591183 := by
    simpa [prefixWord, tailWord_5591183, baseEnd_5591183] using wordTrace_append hprefix tailTrace_5591183
  have hstable : (prefixWord ++ tailWord_5591183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591183).length < 2 ^ (prefixWord ++ tailWord_5591183).sum := by decide
  have hdescent : baseEnd_5591183 < baseStart_5591183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591197 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_5591197 : Nat := 118140960795 + 5591197 * 2 ^ 59
def prefixEnd_5591197 : Nat := 4983230072969 + 3 ^ 40 * 5591197 * 2
def baseEnd_5591197 : Nat := 956990498325555383241353

theorem tailTrace_5591197 : CollatzResearch.WordTrace tailWord_5591197 prefixEnd_5591197 956990498325555383241353 := by
  unfold tailWord_5591197
  simp only [CollatzResearch.WordTrace]
  refine ⟨203927707925055644269203845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135951805283370429512802563 203927707925055644269203845)
  ·
    refine ⟨38236445235947933300475721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203927707925055644269203845 38236445235947933300475721)
    ·
      refine ⟨28677333926960949975356791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38236445235947933300475721 28677333926960949975356791)
      ·
        refine ⟨43016000890441424963035187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28677333926960949975356791 43016000890441424963035187)
        ·
          refine ⟨64524001335662137444552781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43016000890441424963035187 64524001335662137444552781)
          ·
            refine ⟨24196500500873301541707293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64524001335662137444552781 24196500500873301541707293)
            ·
              refine ⟨9073687687827488078140235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24196500500873301541707293 9073687687827488078140235)
              ·
                refine ⟨13610531531741232117210353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073687687827488078140235 13610531531741232117210353)
                ·
                  refine ⟨10207898648805924087907765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13610531531741232117210353 10207898648805924087907765)
                  ·
                    refine ⟨956990498325555383241353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10207898648805924087907765 956990498325555383241353)
                    ·
                      rfl

theorem cell23_5591197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_5591197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591197 prefixEnd_5591197 := by exact prefixLift 5591197
  have htrace : WordTrace (prefixWord ++ tailWord_5591197) baseStart_5591197 baseEnd_5591197 := by
    simpa [prefixWord, tailWord_5591197, baseEnd_5591197] using wordTrace_append hprefix tailTrace_5591197
  have hstable : (prefixWord ++ tailWord_5591197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591197).length < 2 ^ (prefixWord ++ tailWord_5591197).sum := by decide
  have hdescent : baseEnd_5591197 < baseStart_5591197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591227 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 3, 4]
def baseStart_5591227 : Nat := 118140960795 + 5591227 * 2 ^ 59
def prefixEnd_5591227 : Nat := 4983230072969 + 3 ^ 40 * 5591227 * 2
def baseEnd_5591227 : Nat := 956995633132100344116307

theorem tailTrace_5591227 : CollatzResearch.WordTrace tailWord_5591227 prefixEnd_5591227 956995633132100344116307 := by
  unfold tailWord_5591227
  simp only [CollatzResearch.WordTrace]
  refine ⟨203928802114946959392795935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135952534743297972928530623 203928802114946959392795935)
  ·
    refine ⟨305893203172420439089193903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203928802114946959392795935 305893203172420439089193903)
    ·
      refine ⟨458839804758630658633790855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305893203172420439089193903 458839804758630658633790855)
      ·
        refine ⟨688259707137945987950686283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458839804758630658633790855 688259707137945987950686283)
        ·
          refine ⟨1032389560706918981926029425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688259707137945987950686283 1032389560706918981926029425)
          ·
            refine ⟨774292170530189236444522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032389560706918981926029425 774292170530189236444522069)
            ·
              refine ⟨9073736373400655114584243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 774292170530189236444522069 9073736373400655114584243)
              ·
                refine ⟨13610604560100982671876365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073736373400655114584243 13610604560100982671876365)
                ·
                  refine ⟨5103976710037868501953637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13610604560100982671876365 5103976710037868501953637)
                  ·
                    refine ⟨956995633132100344116307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5103976710037868501953637 956995633132100344116307)
                    ·
                      rfl

theorem cell23_5591227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 4].length) (baseStart_5591227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591227 prefixEnd_5591227 := by exact prefixLift 5591227
  have htrace : WordTrace (prefixWord ++ tailWord_5591227) baseStart_5591227 baseEnd_5591227 := by
    simpa [prefixWord, tailWord_5591227, baseEnd_5591227] using wordTrace_append hprefix tailTrace_5591227
  have hstable : (prefixWord ++ tailWord_5591227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591227).length < 2 ^ (prefixWord ++ tailWord_5591227).sum := by decide
  have hdescent : baseEnd_5591227 < baseStart_5591227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591304 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 1, 5]
def baseStart_5591304 : Nat := 118140960795 + 5591304 * 2 ^ 59
def prefixEnd_5591304 : Nat := 4983230072969 + 3 ^ 40 * 5591304 * 2
def baseEnd_5591304 : Nat := 957008812468899077028689

theorem tailTrace_5591304 : CollatzResearch.WordTrace tailWord_5591304 prefixEnd_5591304 957008812468899077028689 := by
  unfold tailWord_5591304
  simp only [CollatzResearch.WordTrace]
  refine ⟨101965805267834000771674483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135954407023778667695565977 101965805267834000771674483)
  ·
    refine ⟨152948707901751001157511725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101965805267834000771674483 152948707901751001157511725)
    ·
      refine ⟨57355765463156625434066897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152948707901751001157511725 57355765463156625434066897)
      ·
        refine ⟨43016824097367469075550173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57355765463156625434066897 43016824097367469075550173)
        ·
          refine ⟨16131309036512800903331315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43016824097367469075550173 16131309036512800903331315)
          ·
            refine ⟨24196963554769201354996973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16131309036512800903331315 24196963554769201354996973)
            ·
              refine ⟨9073861333038450508123865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24196963554769201354996973 9073861333038450508123865)
              ·
                refine ⟨6805395999778837881092899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9073861333038450508123865 6805395999778837881092899)
                ·
                  refine ⟨10208093999668256821639349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6805395999778837881092899 10208093999668256821639349)
                  ·
                    refine ⟨957008812468899077028689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10208093999668256821639349 957008812468899077028689)
                    ·
                      rfl

theorem cell23_5591304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_5591304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591304 prefixEnd_5591304 := by exact prefixLift 5591304
  have htrace : WordTrace (prefixWord ++ tailWord_5591304) baseStart_5591304 baseEnd_5591304 := by
    simpa [prefixWord, tailWord_5591304, baseEnd_5591304] using wordTrace_append hprefix tailTrace_5591304
  have hstable : (prefixWord ++ tailWord_5591304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591304).length < 2 ^ (prefixWord ++ tailWord_5591304).sum := by decide
  have hdescent : baseEnd_5591304 < baseStart_5591304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591307 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 4]
def baseStart_5591307 : Nat := 118140960795 + 5591307 * 2 ^ 59
def prefixEnd_5591307 : Nat := 4983230072969 + 3 ^ 40 * 5591307 * 2
def baseEnd_5591307 : Nat := 2871027977848660719348553

theorem tailTrace_5591307 : CollatzResearch.WordTrace tailWord_5591307 prefixEnd_5591307 2871027977848660719348553 := by
  unfold tailWord_5591307
  simp only [CollatzResearch.WordTrace]
  refine ⟨203931719954657133055708175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135954479969771422037138783 203931719954657133055708175)
  ·
    refine ⟨305897579931985699583562263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203931719954657133055708175 305897579931985699583562263)
    ·
      refine ⟨458846369897978549375343395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305897579931985699583562263 458846369897978549375343395)
      ·
        refine ⟨688269554846967824063015093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458846369897978549375343395 688269554846967824063015093)
        ·
          refine ⟨64525270766903233505907665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 688269554846967824063015093 64525270766903233505907665)
          ·
            refine ⟨48393953075177425129430749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64525270766903233505907665 48393953075177425129430749)
            ·
              refine ⟨18147732403191534423536531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48393953075177425129430749 18147732403191534423536531)
              ·
                refine ⟨27221598604787301635304797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18147732403191534423536531 27221598604787301635304797)
                ·
                  refine ⟨10208099476795238113239299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27221598604787301635304797 10208099476795238113239299)
                  ·
                    refine ⟨15312149215192857169858949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10208099476795238113239299 15312149215192857169858949)
                    ·
                      refine ⟨2871027977848660719348553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15312149215192857169858949 2871027977848660719348553)
                      ·
                        rfl

theorem cell23_5591307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 4].length) (baseStart_5591307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591307 prefixEnd_5591307 := by exact prefixLift 5591307
  have htrace : WordTrace (prefixWord ++ tailWord_5591307) baseStart_5591307 baseEnd_5591307 := by
    simpa [prefixWord, tailWord_5591307, baseEnd_5591307] using wordTrace_append hprefix tailTrace_5591307
  have hstable : (prefixWord ++ tailWord_5591307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591307).length < 2 ^ (prefixWord ++ tailWord_5591307).sum := by decide
  have hdescent : baseEnd_5591307 < baseStart_5591307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591317 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_5591317 : Nat := 118140960795 + 5591317 * 2 ^ 59
def prefixEnd_5591317 : Nat := 4983230072969 + 3 ^ 40 * 5591317 * 2
def baseEnd_5591317 : Nat := 957011037551735226741169

theorem tailTrace_5591317 : CollatzResearch.WordTrace tailWord_5591317 prefixEnd_5591317 957011037551735226741169 := by
  unfold tailWord_5591317
  simp only [CollatzResearch.WordTrace]
  refine ⟨203932084684620904763572205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135954723123080603175714803 203932084684620904763572205)
  ·
    refine ⟨76474531756732839286339577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203932084684620904763572205 76474531756732839286339577)
    ·
      refine ⟨57355898817549629464754683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76474531756732839286339577 57355898817549629464754683)
      ·
        refine ⟨86033848226324444197132025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57355898817549629464754683 86033848226324444197132025)
        ·
          refine ⟨64525386169743333147849019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86033848226324444197132025 64525386169743333147849019)
          ·
            refine ⟨96788079254614999721773529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64525386169743333147849019 96788079254614999721773529)
            ·
              refine ⟨72591059440961249791330147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96788079254614999721773529 72591059440961249791330147)
              ·
                refine ⟨108886589161441874686995221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72591059440961249791330147 108886589161441874686995221)
                ·
                  refine ⟨5104058866942587875952901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108886589161441874686995221 5104058866942587875952901)
                  ·
                    refine ⟨957011037551735226741169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104058866942587875952901 957011037551735226741169)
                    ·
                      rfl

theorem cell23_5591317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_5591317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591317 prefixEnd_5591317 := by exact prefixLift 5591317
  have htrace : WordTrace (prefixWord ++ tailWord_5591317) baseStart_5591317 baseEnd_5591317 := by
    simpa [prefixWord, tailWord_5591317, baseEnd_5591317] using wordTrace_append hprefix tailTrace_5591317
  have hstable : (prefixWord ++ tailWord_5591317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591317).length < 2 ^ (prefixWord ++ tailWord_5591317).sum := by decide
  have hdescent : baseEnd_5591317 < baseStart_5591317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591354 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_5591354 : Nat := 118140960795 + 5591354 * 2 ^ 59
def prefixEnd_5591354 : Nat := 4983230072969 + 3 ^ 40 * 5591354 * 2
def baseEnd_5591354 : Nat := 2871052111439422035460837

theorem tailTrace_5591354 : CollatzResearch.WordTrace tailWord_5591354 prefixEnd_5591354 2871052111439422035460837 := by
  unfold tailWord_5591354
  simp only [CollatzResearch.WordTrace]
  refine ⟨50983358546371715020667279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135955622790324573388446077 50983358546371715020667279)
  ·
    refine ⟨76475037819557572531000919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50983358546371715020667279 76475037819557572531000919)
    ·
      refine ⟨114712556729336358796501379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76475037819557572531000919 114712556729336358796501379)
      ·
        refine ⟨172068835094004538194752069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114712556729336358796501379 172068835094004538194752069)
        ·
          refine ⟨32262906580125850911516013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172068835094004538194752069 32262906580125850911516013)
          ·
            refine ⟨12098589967547194091818505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32262906580125850911516013 12098589967547194091818505)
            ·
              refine ⟨9073942475660395568863879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12098589967547194091818505 9073942475660395568863879)
              ·
                refine ⟨13610913713490593353295819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073942475660395568863879 13610913713490593353295819)
                ·
                  refine ⟨20416370570235890029943729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13610913713490593353295819 20416370570235890029943729)
                  ·
                    refine ⟨15312277927676917522457797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20416370570235890029943729 15312277927676917522457797)
                    ·
                      refine ⟨2871052111439422035460837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15312277927676917522457797 2871052111439422035460837)
                      ·
                        rfl

theorem cell23_5591354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_5591354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591354 prefixEnd_5591354 := by exact prefixLift 5591354
  have htrace : WordTrace (prefixWord ++ tailWord_5591354) baseStart_5591354 baseEnd_5591354 := by
    simpa [prefixWord, tailWord_5591354, baseEnd_5591354] using wordTrace_append hprefix tailTrace_5591354
  have hstable : (prefixWord ++ tailWord_5591354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591354).length < 2 ^ (prefixWord ++ tailWord_5591354).sum := by decide
  have hdescent : baseEnd_5591354 < baseStart_5591354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591358 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_5591358 : Nat := 118140960795 + 5591358 * 2 ^ 59
def prefixEnd_5591358 : Nat := 4983230072969 + 3 ^ 40 * 5591358 * 2
def baseEnd_5591358 : Nat := 2871054165362040019810819

theorem tailTrace_5591358 : CollatzResearch.WordTrace tailWord_5591358 prefixEnd_5591358 2871054165362040019810819 := by
  unfold tailWord_5591358
  simp only [CollatzResearch.WordTrace]
  refine ⟨25491697509684046095726841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135955720051648245843876485 25491697509684046095726841)
  ·
    refine ⟨19118773132263034571795131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25491697509684046095726841 19118773132263034571795131)
    ·
      refine ⟨28678159698394551857692697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19118773132263034571795131 28678159698394551857692697)
      ·
        refine ⟨21508619773795913893269523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28678159698394551857692697 21508619773795913893269523)
        ·
          refine ⟨32262929660693870839904285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21508619773795913893269523 32262929660693870839904285)
          ·
            refine ⟨12098598622760201564964107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32262929660693870839904285 12098598622760201564964107)
            ·
              refine ⟨18147897934140302347446161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12098598622760201564964107 18147897934140302347446161)
              ·
                refine ⟨13610923450605226760584621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18147897934140302347446161 13610923450605226760584621)
                ·
                  refine ⟨5104096293976960035219233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13610923450605226760584621 5104096293976960035219233)
                  ·
                    refine ⟨3828072220482720026414425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104096293976960035219233 3828072220482720026414425)
                    ·
                      refine ⟨2871054165362040019810819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828072220482720026414425 2871054165362040019810819)
                      ·
                        rfl

theorem cell23_5591358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_5591358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591358 prefixEnd_5591358 := by exact prefixLift 5591358
  have htrace : WordTrace (prefixWord ++ tailWord_5591358) baseStart_5591358 baseEnd_5591358 := by
    simpa [prefixWord, tailWord_5591358, baseEnd_5591358] using wordTrace_append hprefix tailTrace_5591358
  have hstable : (prefixWord ++ tailWord_5591358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591358).length < 2 ^ (prefixWord ++ tailWord_5591358).sum := by decide
  have hdescent : baseEnd_5591358 < baseStart_5591358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591384 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 5, 3, 2]
def baseStart_5591384 : Nat := 118140960795 + 5591384 * 2 ^ 59
def prefixEnd_5591384 : Nat := 4983230072969 + 3 ^ 40 * 5591384 * 2
def baseEnd_5591384 : Nat := 2871067515859056918085699

theorem tailTrace_5591384 : CollatzResearch.WordTrace tailWord_5591384 prefixEnd_5591384 2871067515859056918085699 := by
  unfold tailWord_5591384
  simp only [CollatzResearch.WordTrace]
  refine ⟨101967264187689087603130603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135956352250252116804174137 101967264187689087603130603)
  ·
    refine ⟨152950896281533631404695905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101967264187689087603130603 152950896281533631404695905)
    ·
      refine ⟨114713172211150223553521929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152950896281533631404695905 114713172211150223553521929)
      ·
        refine ⟨86034879158362667665141447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114713172211150223553521929 86034879158362667665141447)
        ·
          refine ⟨129052318737544001497712171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86034879158362667665141447 129052318737544001497712171)
          ·
            refine ⟨193578478106316002246568257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129052318737544001497712171 193578478106316002246568257)
            ·
              refine ⟨145183858579737001684926193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193578478106316002246568257 145183858579737001684926193)
              ·
                refine ⟨108887893934802751263694645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145183858579737001684926193 108887893934802751263694645)
                ·
                  refine ⟨10208240056387757930971373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108887893934802751263694645 10208240056387757930971373)
                  ·
                    refine ⟨3828090021145409224114265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10208240056387757930971373 3828090021145409224114265)
                    ·
                      refine ⟨2871067515859056918085699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828090021145409224114265 2871067515859056918085699)
                      ·
                        rfl

theorem cell23_5591384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_5591384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591384 prefixEnd_5591384 := by exact prefixLift 5591384
  have htrace : WordTrace (prefixWord ++ tailWord_5591384) baseStart_5591384 baseEnd_5591384 := by
    simpa [prefixWord, tailWord_5591384, baseEnd_5591384] using wordTrace_append hprefix tailTrace_5591384
  have hstable : (prefixWord ++ tailWord_5591384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591384).length < 2 ^ (prefixWord ++ tailWord_5591384).sum := by decide
  have hdescent : baseEnd_5591384 < baseStart_5591384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591391 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 3]
def baseStart_5591391 : Nat := 118140960795 + 5591391 * 2 ^ 59
def prefixEnd_5591391 : Nat := 4983230072969 + 3 ^ 40 * 5591391 * 2
def baseEnd_5591391 : Nat := 2871071110223638390698167

theorem tailTrace_5591391 : CollatzResearch.WordTrace tailWord_5591391 prefixEnd_5591391 2871071110223638390698167 := by
  unfold tailWord_5591391
  simp only [CollatzResearch.WordTrace]
  refine ⟨203934783686352815401766027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135956522457568543601177351 203934783686352815401766027)
  ·
    refine ⟨305902175529529223102649041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203934783686352815401766027 305902175529529223102649041)
    ·
      refine ⟨229426631647146917326986781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305902175529529223102649041 229426631647146917326986781)
      ·
        refine ⟨86034986867680093997620043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229426631647146917326986781 86034986867680093997620043)
        ·
          refine ⟨129052480301520140996430065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86034986867680093997620043 129052480301520140996430065)
          ·
            refine ⟨96789360226140105747322549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129052480301520140996430065 96789360226140105747322549)
            ·
              refine ⟨9074002521200634913811489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96789360226140105747322549 9074002521200634913811489)
              ·
                refine ⟨6805501890900476185358617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9074002521200634913811489 6805501890900476185358617)
                ·
                  refine ⟨5104126418175357139018963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6805501890900476185358617 5104126418175357139018963)
                  ·
                    refine ⟨7656189627263035708528445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104126418175357139018963 7656189627263035708528445)
                    ·
                      refine ⟨2871071110223638390698167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656189627263035708528445 2871071110223638390698167)
                      ·
                        rfl

theorem cell23_5591391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_5591391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591391 prefixEnd_5591391 := by exact prefixLift 5591391
  have htrace : WordTrace (prefixWord ++ tailWord_5591391) baseStart_5591391 baseEnd_5591391 := by
    simpa [prefixWord, tailWord_5591391, baseEnd_5591391] using wordTrace_append hprefix tailTrace_5591391
  have hstable : (prefixWord ++ tailWord_5591391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591391).length < 2 ^ (prefixWord ++ tailWord_5591391).sum := by decide
  have hdescent : baseEnd_5591391 < baseStart_5591391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591408 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 2, 1, 3]
def baseStart_5591408 : Nat := 118140960795 + 5591408 * 2 ^ 59
def prefixEnd_5591408 : Nat := 4983230072969 + 3 ^ 40 * 5591408 * 2
def baseEnd_5591408 : Nat := 2871079839394764824185589

theorem tailTrace_5591408 : CollatzResearch.WordTrace tailWord_5591408 prefixEnd_5591408 2871079839394764824185589 := by
  unfold tailWord_5591408
  simp only [CollatzResearch.WordTrace]
  refine ⟨101967701863645613652567439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135956935818194151536756585 101967701863645613652567439)
  ·
    refine ⟨152951552795468420478851159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101967701863645613652567439 152951552795468420478851159)
    ·
      refine ⟨229427329193202630718276739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152951552795468420478851159 229427329193202630718276739)
      ·
        refine ⟨344140993789803946077415109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229427329193202630718276739 344140993789803946077415109)
        ·
          refine ⟨64526436335588239889515333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344140993789803946077415109 64526436335588239889515333)
          ·
            refine ⟨12098706812922794979284125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64526436335588239889515333 12098706812922794979284125)
            ·
              refine ⟨4537015054846048117231547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12098706812922794979284125 4537015054846048117231547)
              ·
                refine ⟨6805522582269072175847321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537015054846048117231547 6805522582269072175847321)
                ·
                  refine ⟨5104141936701804131885491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6805522582269072175847321 5104141936701804131885491)
                  ·
                    refine ⟨7656212905052706197828237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104141936701804131885491 7656212905052706197828237)
                    ·
                      refine ⟨2871079839394764824185589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656212905052706197828237 2871079839394764824185589)
                      ·
                        rfl

theorem cell23_5591408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 1, 3].length) (baseStart_5591408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591408 prefixEnd_5591408 := by exact prefixLift 5591408
  have htrace : WordTrace (prefixWord ++ tailWord_5591408) baseStart_5591408 baseEnd_5591408 := by
    simpa [prefixWord, tailWord_5591408, baseEnd_5591408] using wordTrace_append hprefix tailTrace_5591408
  have hstable : (prefixWord ++ tailWord_5591408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591408).length < 2 ^ (prefixWord ++ tailWord_5591408).sum := by decide
  have hdescent : baseEnd_5591408 < baseStart_5591408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591417 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_5591417 : Nat := 118140960795 + 5591417 * 2 ^ 59
def prefixEnd_5591417 : Nat := 4983230072969 + 3 ^ 40 * 5591417 * 2
def baseEnd_5591417 : Nat := 2871084460720655288973047

theorem tailTrace_5591417 : CollatzResearch.WordTrace tailWord_5591417 prefixEnd_5591417 2871084460720655288973047 := by
  unfold tailWord_5591417
  simp only [CollatzResearch.WordTrace]
  refine ⟨203935731984258621842212505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135957154656172414561475003 203935731984258621842212505)
  ·
    refine ⟨152951798988193966381659379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203935731984258621842212505 152951798988193966381659379)
    ·
      refine ⟨229427698482290949572489069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152951798988193966381659379 229427698482290949572489069)
      ·
        refine ⟨86035386930859106089683401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229427698482290949572489069 86035386930859106089683401)
        ·
          refine ⟨64526540198144329567262551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86035386930859106089683401 64526540198144329567262551)
          ·
            refine ⟨96789810297216494350893827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64526540198144329567262551 96789810297216494350893827)
            ·
              refine ⟨145184715445824741526340741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96789810297216494350893827 145184715445824741526340741)
              ·
                refine ⟨27222134146092139036188889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145184715445824741526340741 27222134146092139036188889)
                ·
                  refine ⟨20416600609569104277141667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27222134146092139036188889 20416600609569104277141667)
                  ·
                    refine ⟨30624900914353656415712501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20416600609569104277141667 30624900914353656415712501)
                    ·
                      refine ⟨2871084460720655288973047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30624900914353656415712501 2871084460720655288973047)
                      ·
                        rfl

theorem cell23_5591417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_5591417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591417 prefixEnd_5591417 := by exact prefixLift 5591417
  have htrace : WordTrace (prefixWord ++ tailWord_5591417) baseStart_5591417 baseEnd_5591417 := by
    simpa [prefixWord, tailWord_5591417, baseEnd_5591417] using wordTrace_append hprefix tailTrace_5591417
  have hstable : (prefixWord ++ tailWord_5591417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591417).length < 2 ^ (prefixWord ++ tailWord_5591417).sum := by decide
  have hdescent : baseEnd_5591417 < baseStart_5591417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591426 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5591426 : Nat := 118140960795 + 5591426 * 2 ^ 59
def prefixEnd_5591426 : Nat := 4983230072969 + 3 ^ 40 * 5591426 * 2
def baseEnd_5591426 : Nat := 2871089082046545753760507

theorem tailTrace_5591426 : CollatzResearch.WordTrace tailWord_5591426 prefixEnd_5591426 2871089082046545753760507 := by
  unfold tailWord_5591426
  simp only [CollatzResearch.WordTrace]
  refine ⟨50984015060306504094822533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135957373494150677586193421 50984015060306504094822533)
  ·
    refine ⟨9559502823807469517779225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50984015060306504094822533 9559502823807469517779225)
    ·
      refine ⟨7169627117855602138334419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9559502823807469517779225 7169627117855602138334419)
      ·
        refine ⟨10754440676783403207501629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169627117855602138334419 10754440676783403207501629)
        ·
          refine ⟨4032915253793776202813111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10754440676783403207501629 4032915253793776202813111)
          ·
            refine ⟨6049372880690664304219667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032915253793776202813111 6049372880690664304219667)
            ·
              refine ⟨9074059321035996456329501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049372880690664304219667 9074059321035996456329501)
              ·
                refine ⟨3402772245388498671123563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9074059321035996456329501 3402772245388498671123563)
                ·
                  refine ⟨5104158368082748006685345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402772245388498671123563 5104158368082748006685345)
                  ·
                    refine ⟨3828118776062061005014009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104158368082748006685345 3828118776062061005014009)
                    ·
                      refine ⟨2871089082046545753760507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828118776062061005014009 2871089082046545753760507)
                      ·
                        rfl

theorem cell23_5591426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5591426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591426 prefixEnd_5591426 := by exact prefixLift 5591426
  have htrace : WordTrace (prefixWord ++ tailWord_5591426) baseStart_5591426 baseEnd_5591426 := by
    simpa [prefixWord, tailWord_5591426, baseEnd_5591426] using wordTrace_append hprefix tailTrace_5591426
  have hstable : (prefixWord ++ tailWord_5591426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591426).length < 2 ^ (prefixWord ++ tailWord_5591426).sum := by decide
  have hdescent : baseEnd_5591426 < baseStart_5591426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591431 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_5591431 : Nat := 118140960795 + 5591431 * 2 ^ 59
def prefixEnd_5591431 : Nat := 4983230072969 + 3 ^ 40 * 5591431 * 2
def baseEnd_5591431 : Nat := 2871091649449818234197983

theorem tailTrace_5591431 : CollatzResearch.WordTrace tailWord_5591431 prefixEnd_5591431 2871091649449818234197983 := by
  unfold tailWord_5591431
  simp only [CollatzResearch.WordTrace]
  refine ⟨203936242606207902233222147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135957495070805268155481431 203936242606207902233222147)
  ·
    refine ⟨305904363909311853349833221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203936242606207902233222147 305904363909311853349833221)
    ·
      refine ⟨57357068232995972503093729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305904363909311853349833221 57357068232995972503093729)
      ·
        refine ⟨43017801174746979377320297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57357068232995972503093729 43017801174746979377320297)
        ·
          refine ⟨32263350881060234532990223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43017801174746979377320297 32263350881060234532990223)
          ·
            refine ⟨48395026321590351799485335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32263350881060234532990223 48395026321590351799485335)
            ·
              refine ⟨72592539482385527699228003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48395026321590351799485335 72592539482385527699228003)
              ·
                refine ⟨108888809223578291548842005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72592539482385527699228003 108888809223578291548842005)
                ·
                  refine ⟨5104162932355232416351969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108888809223578291548842005 5104162932355232416351969)
                  ·
                    refine ⟨3828122199266424312263977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104162932355232416351969 3828122199266424312263977)
                    ·
                      refine ⟨2871091649449818234197983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828122199266424312263977 2871091649449818234197983)
                      ·
                        rfl

theorem cell23_5591431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_5591431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591431 prefixEnd_5591431 := by exact prefixLift 5591431
  have htrace : WordTrace (prefixWord ++ tailWord_5591431) baseStart_5591431 baseEnd_5591431 := by
    simpa [prefixWord, tailWord_5591431, baseEnd_5591431] using wordTrace_append hprefix tailTrace_5591431
  have hstable : (prefixWord ++ tailWord_5591431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591431).length < 2 ^ (prefixWord ++ tailWord_5591431).sum := by decide
  have hdescent : baseEnd_5591431 < baseStart_5591431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591448 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5591448 : Nat := 118140960795 + 5591448 * 2 ^ 59
def prefixEnd_5591448 : Nat := 4983230072969 + 3 ^ 40 * 5591448 * 2
def baseEnd_5591448 : Nat := 2871100378620944667685405

theorem tailTrace_5591448 : CollatzResearch.WordTrace tailWord_5591448 prefixEnd_5591448 2871100378620944667685405 := by
  unfold tailWord_5591448
  simp only [CollatzResearch.WordTrace]
  refine ⟨101968431323573157068295499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135957908431430876091060665 101968431323573157068295499)
  ·
    refine ⟨152952646985359735602443249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101968431323573157068295499 152952646985359735602443249)
    ·
      refine ⟨114714485239019801701832437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152952646985359735602443249 114714485239019801701832437)
      ·
        refine ⟨10754482991158106409546791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114714485239019801701832437 10754482991158106409546791)
        ·
          refine ⟨16131724486737159614320187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10754482991158106409546791 16131724486737159614320187)
          ·
            refine ⟨24197586730105739421480281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16131724486737159614320187 24197586730105739421480281)
            ·
              refine ⟨18148190047579304566110211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24197586730105739421480281 18148190047579304566110211)
              ·
                refine ⟨27222285071368956849165317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18148190047579304566110211 27222285071368956849165317)
                ·
                  refine ⟨5104178450881679409218497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27222285071368956849165317 5104178450881679409218497)
                  ·
                    refine ⟨3828133838161259556913873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104178450881679409218497 3828133838161259556913873)
                    ·
                      refine ⟨2871100378620944667685405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828133838161259556913873 2871100378620944667685405)
                      ·
                        rfl

theorem cell23_5591448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5591448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591448 prefixEnd_5591448 := by exact prefixLift 5591448
  have htrace : WordTrace (prefixWord ++ tailWord_5591448) baseStart_5591448 baseEnd_5591448 := by
    simpa [prefixWord, tailWord_5591448, baseEnd_5591448] using wordTrace_append hprefix tailTrace_5591448
  have hstable : (prefixWord ++ tailWord_5591448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591448).length < 2 ^ (prefixWord ++ tailWord_5591448).sum := by decide
  have hdescent : baseEnd_5591448 < baseStart_5591448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591521 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_5591521 : Nat := 118140960795 + 5591521 * 2 ^ 59
def prefixEnd_5591521 : Nat := 4983230072969 + 3 ^ 40 * 5591521 * 2
def baseEnd_5591521 : Nat := 2871137862708722882072569

theorem tailTrace_5591521 : CollatzResearch.WordTrace tailWord_5591521 prefixEnd_5591521 2871137862708722882072569 := by
  unfold tailWord_5591521
  simp only [CollatzResearch.WordTrace]
  refine ⟨203939525175881847603998417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135959683450587898402665611 203939525175881847603998417)
  ·
    refine ⟨152954643881911385702998813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203939525175881847603998417 152954643881911385702998813)
    ·
      refine ⟨57357991455716769638624555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152954643881911385702998813 57357991455716769638624555)
      ·
        refine ⟨86036987183575154457936833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57357991455716769638624555 86036987183575154457936833)
        ·
          refine ⟨64527740387681365843452625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86036987183575154457936833 64527740387681365843452625)
          ·
            refine ⟨48395805290761024382589469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64527740387681365843452625 48395805290761024382589469)
            ·
              refine ⟨18148426984035384143471051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48395805290761024382589469 18148426984035384143471051)
              ·
                refine ⟨27222640476053076215206577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18148426984035384143471051 27222640476053076215206577)
                ·
                  refine ⟨20416980357039807161404933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27222640476053076215206577 20416980357039807161404933)
                  ·
                    refine ⟨3828183816944963842763425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20416980357039807161404933 3828183816944963842763425)
                    ·
                      refine ⟨2871137862708722882072569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828183816944963842763425 2871137862708722882072569)
                      ·
                        rfl

theorem cell23_5591521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_5591521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591521 prefixEnd_5591521 := by exact prefixLift 5591521
  have htrace : WordTrace (prefixWord ++ tailWord_5591521) baseStart_5591521 baseEnd_5591521 := by
    simpa [prefixWord, tailWord_5591521, baseEnd_5591521] using wordTrace_append hprefix tailTrace_5591521
  have hstable : (prefixWord ++ tailWord_5591521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591521).length < 2 ^ (prefixWord ++ tailWord_5591521).sum := by decide
  have hdescent : baseEnd_5591521 < baseStart_5591521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591547 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_5591547 : Nat := 118140960795 + 5591547 * 2 ^ 59
def prefixEnd_5591547 : Nat := 4983230072969 + 3 ^ 40 * 5591547 * 2
def baseEnd_5591547 : Nat := 2871151213205739780347449

theorem tailTrace_5591547 : CollatzResearch.WordTrace tailWord_5591547 prefixEnd_5591547 2871151213205739780347449 := by
  unfold tailWord_5591547
  simp only [CollatzResearch.WordTrace]
  refine ⟨203940473473787654044444895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135960315649191769362963263 203940473473787654044444895)
  ·
    refine ⟨305910710210681481066667343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203940473473787654044444895 305910710210681481066667343)
    ·
      refine ⟨458866065316022221600001015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305910710210681481066667343 458866065316022221600001015)
      ·
        refine ⟨688299097974033332400001523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458866065316022221600001015 688299097974033332400001523)
        ·
          refine ⟨1032448646961049998600002285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688299097974033332400001523 1032448646961049998600002285)
          ·
            refine ⟨387168242610393749475000857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032448646961049998600002285 387168242610393749475000857)
            ·
              refine ⟨290376181957795312106250643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387168242610393749475000857 290376181957795312106250643)
              ·
                refine ⟨435564272936692968159375965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290376181957795312106250643 435564272936692968159375965)
                ·
                  refine ⟨163336602351259863059765987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435564272936692968159375965 163336602351259863059765987)
                  ·
                    refine ⟨245004903526889794589648981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163336602351259863059765987 245004903526889794589648981)
                    ·
                      refine ⟨2871151213205739780347449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 245004903526889794589648981 2871151213205739780347449)
                      ·
                        rfl

theorem cell23_5591547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_5591547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591547 prefixEnd_5591547 := by exact prefixLift 5591547
  have htrace : WordTrace (prefixWord ++ tailWord_5591547) baseStart_5591547 baseEnd_5591547 := by
    simpa [prefixWord, tailWord_5591547, baseEnd_5591547] using wordTrace_append hprefix tailTrace_5591547
  have hstable : (prefixWord ++ tailWord_5591547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591547).length < 2 ^ (prefixWord ++ tailWord_5591547).sum := by decide
  have hdescent : baseEnd_5591547 < baseStart_5591547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591564 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5591564 : Nat := 118140960795 + 5591564 * 2 ^ 59
def prefixEnd_5591564 : Nat := 4983230072969 + 3 ^ 40 * 5591564 * 2
def baseEnd_5591564 : Nat := 2871159942376866213834871

theorem tailTrace_5591564 : CollatzResearch.WordTrace tailWord_5591564 prefixEnd_5591564 2871159942376866213834871 := by
  unfold tailWord_5591564
  simp only [CollatzResearch.WordTrace]
  refine ⟨101970546757363032973906873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135960729009817377298542497 101970546757363032973906873)
  ·
    refine ⟨76477910068022274730430155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101970546757363032973906873 76477910068022274730430155)
    ·
      refine ⟨114716865102033412095645233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76477910068022274730430155 114716865102033412095645233)
      ·
        refine ⟨86037648826525059071733925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114716865102033412095645233 86037648826525059071733925)
        ·
          refine ⟨16132059154973448575950111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86037648826525059071733925 16132059154973448575950111)
          ·
            refine ⟨24198088732460172863925167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16132059154973448575950111 24198088732460172863925167)
            ·
              refine ⟨36297133098690259295887751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24198088732460172863925167 36297133098690259295887751)
              ·
                refine ⟨54445699648035388943831627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36297133098690259295887751 54445699648035388943831627)
                ·
                  refine ⟨81668549472053083415747441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54445699648035388943831627 81668549472053083415747441)
                  ·
                    refine ⟨61251412104039812561810581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81668549472053083415747441 61251412104039812561810581)
                    ·
                      refine ⟨2871159942376866213834871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61251412104039812561810581 2871159942376866213834871)
                      ·
                        rfl

theorem cell23_5591564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5591564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591564 prefixEnd_5591564 := by exact prefixLift 5591564
  have htrace : WordTrace (prefixWord ++ tailWord_5591564) baseStart_5591564 baseEnd_5591564 := by
    simpa [prefixWord, tailWord_5591564, baseEnd_5591564] using wordTrace_append hprefix tailTrace_5591564
  have hstable : (prefixWord ++ tailWord_5591564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591564).length < 2 ^ (prefixWord ++ tailWord_5591564).sum := by decide
  have hdescent : baseEnd_5591564 < baseStart_5591564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591565 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5591565 : Nat := 118140960795 + 5591565 * 2 ^ 59
def prefixEnd_5591565 : Nat := 4983230072969 + 3 ^ 40 * 5591565 * 2
def baseEnd_5591565 : Nat := 957053485285840236640789

theorem tailTrace_5591565 : CollatzResearch.WordTrace tailWord_5591565 prefixEnd_5591565 957053485285840236640789 := by
  unfold tailWord_5591565
  simp only [CollatzResearch.WordTrace]
  refine ⟨203941129987722443118600149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135960753325148295412400099 203941129987722443118600149)
  ·
    refine ⟨4779870234087244760592191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 203941129987722443118600149 4779870234087244760592191)
    ·
      refine ⟨7169805351130867140888287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779870234087244760592191 7169805351130867140888287)
      ·
        refine ⟨10754708026696300711332431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169805351130867140888287 10754708026696300711332431)
        ·
          refine ⟨16132062040044451066998647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10754708026696300711332431 16132062040044451066998647)
          ·
            refine ⟨24198093060066676600497971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16132062040044451066998647 24198093060066676600497971)
            ·
              refine ⟨36297139590100014900746957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24198093060066676600497971 36297139590100014900746957)
              ·
                refine ⟨13611427346287505587780109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36297139590100014900746957 13611427346287505587780109)
                ·
                  refine ⟨5104285254857814595417541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13611427346287505587780109 5104285254857814595417541)
                  ·
                    refine ⟨957053485285840236640789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104285254857814595417541 957053485285840236640789)
                    ·
                      rfl

theorem cell23_5591565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5591565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591565 prefixEnd_5591565 := by exact prefixLift 5591565
  have htrace : WordTrace (prefixWord ++ tailWord_5591565) baseStart_5591565 baseEnd_5591565 := by
    simpa [prefixWord, tailWord_5591565, baseEnd_5591565] using wordTrace_append hprefix tailTrace_5591565
  have hstable : (prefixWord ++ tailWord_5591565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591565).length < 2 ^ (prefixWord ++ tailWord_5591565).sum := by decide
  have hdescent : baseEnd_5591565 < baseStart_5591565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591621 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_5591621 : Nat := 118140960795 + 5591621 * 2 ^ 59
def prefixEnd_5591621 : Nat := 4983230072969 + 3 ^ 40 * 5591621 * 2
def baseEnd_5591621 : Nat := 957063070258057496940703

theorem tailTrace_5591621 : CollatzResearch.WordTrace tailWord_5591621 prefixEnd_5591621 957063070258057496940703 := by
  unfold tailWord_5591621
  simp only [CollatzResearch.WordTrace]
  refine ⟨203943172475519564682638717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135962114983679709788425811 203943172475519564682638717)
  ·
    refine ⟨76478689678319836755989519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203943172475519564682638717 76478689678319836755989519)
    ·
      refine ⟨114718034517479755133984279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76478689678319836755989519 114718034517479755133984279)
      ·
        refine ⟨172077051776219632700976419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114718034517479755133984279 172077051776219632700976419)
        ·
          refine ⟨258115577664329449051464629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172077051776219632700976419 258115577664329449051464629)
          ·
            refine ⟨24198335406030885848574809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258115577664329449051464629 24198335406030885848574809)
            ·
              refine ⟨18148751554523164386431107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24198335406030885848574809 18148751554523164386431107)
              ·
                refine ⟨27223127331784746579646661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18148751554523164386431107 27223127331784746579646661)
                ·
                  refine ⟨5104336374709639983683749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27223127331784746579646661 5104336374709639983683749)
                  ·
                    refine ⟨957063070258057496940703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104336374709639983683749 957063070258057496940703)
                    ·
                      rfl

theorem cell23_5591621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_5591621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591621 prefixEnd_5591621 := by exact prefixLift 5591621
  have htrace : WordTrace (prefixWord ++ tailWord_5591621) baseStart_5591621 baseEnd_5591621 := by
    simpa [prefixWord, tailWord_5591621, baseEnd_5591621] using wordTrace_append hprefix tailTrace_5591621
  have hstable : (prefixWord ++ tailWord_5591621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591621).length < 2 ^ (prefixWord ++ tailWord_5591621).sum := by decide
  have hdescent : baseEnd_5591621 < baseStart_5591621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591622 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5591622 : Nat := 118140960795 + 5591622 * 2 ^ 59
def prefixEnd_5591622 : Nat := 4983230072969 + 3 ^ 40 * 5591622 * 2
def baseEnd_5591622 : Nat := 2871189724254826986909605

theorem tailTrace_5591622 : CollatzResearch.WordTrace tailWord_5591622 prefixEnd_5591622 2871189724254826986909605 := by
  unfold tailWord_5591622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373225279641123182919535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135962139299010627902283413 6373225279641123182919535)
  ·
    refine ⟨9559837919461684774379303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373225279641123182919535 9559837919461684774379303)
    ·
      refine ⟨14339756879192527161568955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9559837919461684774379303 14339756879192527161568955)
      ·
        refine ⟨21509635318788790742353433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14339756879192527161568955 21509635318788790742353433)
        ·
          refine ⟨16132226489091593056765075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21509635318788790742353433 16132226489091593056765075)
          ·
            refine ⟨24198339733637389585147613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16132226489091593056765075 24198339733637389585147613)
            ·
              refine ⟨9074377400114021094430355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24198339733637389585147613 9074377400114021094430355)
              ·
                refine ⟨13611566100171031641645533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074377400114021094430355 13611566100171031641645533)
                ·
                  refine ⟨5104337287564136865617075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13611566100171031641645533 5104337287564136865617075)
                  ·
                    refine ⟨7656505931346205298425613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104337287564136865617075 7656505931346205298425613)
                    ·
                      refine ⟨2871189724254826986909605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656505931346205298425613 2871189724254826986909605)
                      ·
                        rfl

theorem cell23_5591622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5591622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591622 prefixEnd_5591622 := by exact prefixLift 5591622
  have htrace : WordTrace (prefixWord ++ tailWord_5591622) baseStart_5591622 baseEnd_5591622 := by
    simpa [prefixWord, tailWord_5591622, baseEnd_5591622] using wordTrace_append hprefix tailTrace_5591622
  have hstable : (prefixWord ++ tailWord_5591622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591622).length < 2 ^ (prefixWord ++ tailWord_5591622).sum := by decide
  have hdescent : baseEnd_5591622 < baseStart_5591622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591648 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3]
def baseStart_5591648 : Nat := 118140960795 + 5591648 * 2 ^ 59
def prefixEnd_5591648 : Nat := 4983230072969 + 3 ^ 40 * 5591648 * 2
def baseEnd_5591648 : Nat := 2871203074751843885184485

theorem tailTrace_5591648 : CollatzResearch.WordTrace tailWord_5591648 prefixEnd_5591648 2871203074751843885184485 := by
  unfold tailWord_5591648
  simp only [CollatzResearch.WordTrace]
  refine ⟨101972078623210874146935799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135962771497614498862581065 101972078623210874146935799)
  ·
    refine ⟨152958117934816311220403699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101972078623210874146935799 152958117934816311220403699)
    ·
      refine ⟨229437176902224466830605549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152958117934816311220403699 229437176902224466830605549)
      ·
        refine ⟨86038941338334175061477081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229437176902224466830605549 86038941338334175061477081)
        ·
          refine ⟨64529206003750631296107811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86038941338334175061477081 64529206003750631296107811)
          ·
            refine ⟨96793809005625946944161717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64529206003750631296107811 96793809005625946944161717)
            ·
              refine ⟨9074419594277432526015161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96793809005625946944161717 9074419594277432526015161)
              ·
                refine ⟨6805814695708074394511371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9074419594277432526015161 6805814695708074394511371)
                ·
                  refine ⟨10208722043562111591767057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6805814695708074394511371 10208722043562111591767057)
                  ·
                    refine ⟨7656541532671583693825293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10208722043562111591767057 7656541532671583693825293)
                    ·
                      refine ⟨2871203074751843885184485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656541532671583693825293 2871203074751843885184485)
                      ·
                        rfl

theorem cell23_5591648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_5591648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591648 prefixEnd_5591648 := by exact prefixLift 5591648
  have htrace : WordTrace (prefixWord ++ tailWord_5591648) baseStart_5591648 baseEnd_5591648 := by
    simpa [prefixWord, tailWord_5591648, baseEnd_5591648] using wordTrace_append hprefix tailTrace_5591648
  have hstable : (prefixWord ++ tailWord_5591648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591648).length < 2 ^ (prefixWord ++ tailWord_5591648).sum := by decide
  have hdescent : baseEnd_5591648 < baseStart_5591648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591674 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_5591674 : Nat := 118140960795 + 5591674 * 2 ^ 59
def prefixEnd_5591674 : Nat := 4983230072969 + 3 ^ 40 * 5591674 * 2
def baseEnd_5591674 : Nat := 2871216425248860783459365

theorem tailTrace_5591674 : CollatzResearch.WordTrace tailWord_5591674 prefixEnd_5591674 2871216425248860783459365 := by
  unfold tailWord_5591674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50986276386081888683579519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135963403696218369822878717 50986276386081888683579519)
  ·
    refine ⟨76479414579122833025369279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50986276386081888683579519 76479414579122833025369279)
    ·
      refine ⟨114719121868684249538053919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76479414579122833025369279 114719121868684249538053919)
      ·
        refine ⟨172078682803026374307080879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114719121868684249538053919 172078682803026374307080879)
        ·
          refine ⟨258118024204539561460621319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172078682803026374307080879 258118024204539561460621319)
          ·
            refine ⟨387177036306809342190931979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258118024204539561460621319 387177036306809342190931979)
            ·
              refine ⟨580765554460214013286397969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387177036306809342190931979 580765554460214013286397969)
              ·
                refine ⟨435574165845160509964798477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580765554460214013286397969 435574165845160509964798477)
                ·
                  refine ⟨163340312191935191236799429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435574165845160509964798477 163340312191935191236799429)
                  ·
                    refine ⟨30626308535987848356899893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163340312191935191236799429 30626308535987848356899893)
                    ·
                      refine ⟨2871216425248860783459365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30626308535987848356899893 2871216425248860783459365)
                      ·
                        rfl

theorem cell23_5591674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_5591674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591674 prefixEnd_5591674 := by exact prefixLift 5591674
  have htrace : WordTrace (prefixWord ++ tailWord_5591674) baseStart_5591674 baseEnd_5591674 := by
    simpa [prefixWord, tailWord_5591674, baseEnd_5591674] using wordTrace_append hprefix tailTrace_5591674
  have hstable : (prefixWord ++ tailWord_5591674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591674).length < 2 ^ (prefixWord ++ tailWord_5591674).sum := by decide
  have hdescent : baseEnd_5591674 < baseStart_5591674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591729 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5591729 : Nat := 118140960795 + 5591729 * 2 ^ 59
def prefixEnd_5591729 : Nat := 4983230072969 + 3 ^ 40 * 5591729 * 2
def baseEnd_5591729 : Nat := 2871244666684858068271613

theorem tailTrace_5591729 : CollatzResearch.WordTrace tailWord_5591729 prefixEnd_5591729 2871244666684858068271613 := by
  unfold tailWord_5591729
  simp only [CollatzResearch.WordTrace]
  refine ⟨203947111559128299127570241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135964741039418866085046827 203947111559128299127570241)
  ·
    refine ⟨152960333669346224345677681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203947111559128299127570241 152960333669346224345677681)
    ·
      refine ⟨114720250252009668259258261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152960333669346224345677681 114720250252009668259258261)
      ·
        refine ⟨5377511730562953199652731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114720250252009668259258261 5377511730562953199652731)
        ·
          refine ⟨8066267595844429799479097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377511730562953199652731 8066267595844429799479097)
          ·
            refine ⟨6049700696883322349609323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8066267595844429799479097 6049700696883322349609323)
            ·
              refine ⟨9074551045324983524413985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049700696883322349609323 9074551045324983524413985)
              ·
                refine ⟨6805913283993737643310489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9074551045324983524413985 6805913283993737643310489)
                ·
                  refine ⟨5104434962995303232482867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6805913283993737643310489 5104434962995303232482867)
                  ·
                    refine ⟨7656652444492954848724301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104434962995303232482867 7656652444492954848724301)
                    ·
                      refine ⟨2871244666684858068271613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656652444492954848724301 2871244666684858068271613)
                      ·
                        rfl

theorem cell23_5591729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5591729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591729 prefixEnd_5591729 := by exact prefixLift 5591729
  have htrace : WordTrace (prefixWord ++ tailWord_5591729) baseStart_5591729 baseEnd_5591729 := by
    simpa [prefixWord, tailWord_5591729, baseEnd_5591729] using wordTrace_append hprefix tailTrace_5591729
  have hstable : (prefixWord ++ tailWord_5591729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591729).length < 2 ^ (prefixWord ++ tailWord_5591729).sum := by decide
  have hdescent : baseEnd_5591729 < baseStart_5591729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591731 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4]
def baseStart_5591731 : Nat := 118140960795 + 5591731 * 2 ^ 59
def prefixEnd_5591731 : Nat := 4983230072969 + 3 ^ 40 * 5591731 * 2
def baseEnd_5591731 : Nat := 2871245693646167060446603

theorem tailTrace_5591731 : CollatzResearch.WordTrace tailWord_5591731 prefixEnd_5591731 2871245693646167060446603 := by
  unfold tailWord_5591731
  simp only [CollatzResearch.WordTrace]
  refine ⟨203947184505121053469143047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135964789670080702312762031 203947184505121053469143047)
  ·
    refine ⟨305920776757681580203714571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203947184505121053469143047 305920776757681580203714571)
    ·
      refine ⟨458881165136522370305571857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305920776757681580203714571 458881165136522370305571857)
      ·
        refine ⟨344160873852391777729178893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458881165136522370305571857 344160873852391777729178893)
        ·
          refine ⟨129060327694646916648442085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344160873852391777729178893 129060327694646916648442085)
          ·
            refine ⟨24198811442746296871582891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129060327694646916648442085 24198811442746296871582891)
            ·
              refine ⟨36298217164119445307374337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24198811442746296871582891 36298217164119445307374337)
              ·
                refine ⟨27223662873089583980530753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36298217164119445307374337 27223662873089583980530753)
                ·
                  refine ⟨20417747154817187985398065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27223662873089583980530753 20417747154817187985398065)
                  ·
                    refine ⟨15313310366112890989048549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20417747154817187985398065 15313310366112890989048549)
                    ·
                      refine ⟨2871245693646167060446603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15313310366112890989048549 2871245693646167060446603)
                      ·
                        rfl

theorem cell23_5591731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_5591731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591731 prefixEnd_5591731 := by exact prefixLift 5591731
  have htrace : WordTrace (prefixWord ++ tailWord_5591731) baseStart_5591731 baseEnd_5591731 := by
    simpa [prefixWord, tailWord_5591731, baseEnd_5591731] using wordTrace_append hprefix tailTrace_5591731
  have hstable : (prefixWord ++ tailWord_5591731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591731).length < 2 ^ (prefixWord ++ tailWord_5591731).sum := by decide
  have hdescent : baseEnd_5591731 < baseStart_5591731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591741 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 7]
def baseStart_5591741 : Nat := 118140960795 + 5591741 * 2 ^ 59
def prefixEnd_5591741 : Nat := 4983230072969 + 3 ^ 40 * 5591741 * 2
def baseEnd_5591741 : Nat := 319027869828079113480173

theorem tailTrace_5591741 : CollatzResearch.WordTrace tailWord_5591741 prefixEnd_5591741 319027869828079113480173 := by
  unfold tailWord_5591741
  simp only [CollatzResearch.WordTrace]
  refine ⟨203947549235084825177007077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135965032823389883451338051 203947549235084825177007077)
  ·
    refine ⟨38240165481578404720688827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203947549235084825177007077 38240165481578404720688827)
    ·
      refine ⟨57360248222367607081033241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38240165481578404720688827 57360248222367607081033241)
      ·
        refine ⟨43020186166775705310774931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57360248222367607081033241 43020186166775705310774931)
        ·
          refine ⟨64530279250163557966162397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43020186166775705310774931 64530279250163557966162397)
          ·
            refine ⟨24198854718811334237310899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64530279250163557966162397 24198854718811334237310899)
            ·
              refine ⟨36298282078217001355966349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24198854718811334237310899 36298282078217001355966349)
              ·
                refine ⟨13611855779331375508487381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36298282078217001355966349 13611855779331375508487381)
                ·
                  refine ⟨319027869828079113480173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13611855779331375508487381 319027869828079113480173)
                  ·
                    rfl

theorem cell23_5591741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_5591741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591741 prefixEnd_5591741 := by exact prefixLift 5591741
  have htrace : WordTrace (prefixWord ++ tailWord_5591741) baseStart_5591741 baseEnd_5591741 := by
    simpa [prefixWord, tailWord_5591741, baseEnd_5591741] using wordTrace_append hprefix tailTrace_5591741
  have hstable : (prefixWord ++ tailWord_5591741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591741).length < 2 ^ (prefixWord ++ tailWord_5591741).sum := by decide
  have hdescent : baseEnd_5591741 < baseStart_5591741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591748 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5591748 : Nat := 118140960795 + 5591748 * 2 ^ 59
def prefixEnd_5591748 : Nat := 4983230072969 + 3 ^ 40 * 5591748 * 2
def baseEnd_5591748 : Nat := 2871254422817293493934025

theorem tailTrace_5591748 : CollatzResearch.WordTrace tailWord_5591748 prefixEnd_5591748 2871254422817293493934025 := by
  unfold tailWord_5591748
  simp only [CollatzResearch.WordTrace]
  refine ⟨101973902273029732686255949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135965203030706310248341265 101973902273029732686255949)
  ·
    refine ⟨38240213352386149757345981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101973902273029732686255949 38240213352386149757345981)
    ·
      refine ⟨14340080007144806159004743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38240213352386149757345981 14340080007144806159004743)
      ·
        refine ⟨21510120010717209238507115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340080007144806159004743 21510120010717209238507115)
        ·
          refine ⟨32265180016075813857760673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21510120010717209238507115 32265180016075813857760673)
          ·
            refine ⟨24198885012056860393320505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32265180016075813857760673 24198885012056860393320505)
            ·
              refine ⟨18149163759042645294990379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24198885012056860393320505 18149163759042645294990379)
              ·
                refine ⟨27223745638563967942485569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18149163759042645294990379 27223745638563967942485569)
                ·
                  refine ⟨20417809228922975956864177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27223745638563967942485569 20417809228922975956864177)
                  ·
                    refine ⟨15313356921692231967648133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20417809228922975956864177 15313356921692231967648133)
                    ·
                      refine ⟨2871254422817293493934025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15313356921692231967648133 2871254422817293493934025)
                      ·
                        rfl

theorem cell23_5591748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5591748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591748 prefixEnd_5591748 := by exact prefixLift 5591748
  have htrace : WordTrace (prefixWord ++ tailWord_5591748) baseStart_5591748 baseEnd_5591748 := by
    simpa [prefixWord, tailWord_5591748, baseEnd_5591748] using wordTrace_append hprefix tailTrace_5591748
  have hstable : (prefixWord ++ tailWord_5591748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591748).length < 2 ^ (prefixWord ++ tailWord_5591748).sum := by decide
  have hdescent : baseEnd_5591748 < baseStart_5591748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591751 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_5591751 : Nat := 118140960795 + 5591751 * 2 ^ 59
def prefixEnd_5591751 : Nat := 4983230072969 + 3 ^ 40 * 5591751 * 2
def baseEnd_5591751 : Nat := 2871255963259256982196511

theorem tailTrace_5591751 : CollatzResearch.WordTrace tailWord_5591751 prefixEnd_5591751 2871255963259256982196511 := by
  unfold tailWord_5591751
  simp only [CollatzResearch.WordTrace]
  refine ⟨203947913965048596884871107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135965275976699064589914071 203947913965048596884871107)
  ·
    refine ⟨305921870947572895327306661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203947913965048596884871107 305921870947572895327306661)
    ·
      refine ⟨57360350802669917873869999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305921870947572895327306661 57360350802669917873869999)
      ·
        refine ⟨86040526204004876810804999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57360350802669917873869999 86040526204004876810804999)
        ·
          refine ⟨129060789306007315216207499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86040526204004876810804999 129060789306007315216207499)
          ·
            refine ⟨193591183959010972824311249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129060789306007315216207499 193591183959010972824311249)
            ·
              refine ⟨145193387969258229618233437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193591183959010972824311249 145193387969258229618233437)
              ·
                refine ⟨54447520488471836106837539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145193387969258229618233437 54447520488471836106837539)
                ·
                  refine ⟨81671280732707754160256309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54447520488471836106837539 81671280732707754160256309)
                  ·
                    refine ⟨7656682568691351952524029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81671280732707754160256309 7656682568691351952524029)
                    ·
                      refine ⟨2871255963259256982196511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656682568691351952524029 2871255963259256982196511)
                      ·
                        rfl

theorem cell23_5591751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_5591751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591751 prefixEnd_5591751 := by exact prefixLift 5591751
  have htrace : WordTrace (prefixWord ++ tailWord_5591751) baseStart_5591751 baseEnd_5591751 := by
    simpa [prefixWord, tailWord_5591751, baseEnd_5591751] using wordTrace_append hprefix tailTrace_5591751
  have hstable : (prefixWord ++ tailWord_5591751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591751).length < 2 ^ (prefixWord ++ tailWord_5591751).sum := by decide
  have hdescent : baseEnd_5591751 < baseStart_5591751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591775 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 5]
def baseStart_5591775 : Nat := 118140960795 + 5591775 * 2 ^ 59
def prefixEnd_5591775 : Nat := 4983230072969 + 3 ^ 40 * 5591775 * 2
def baseEnd_5591775 : Nat := 319029809643884987588489

theorem tailTrace_5591775 : CollatzResearch.WordTrace tailWord_5591775 prefixEnd_5591775 319029809643884987588489 := by
  unfold tailWord_5591775
  simp only [CollatzResearch.WordTrace]
  refine ⟨203948789316961648983744779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135965859544641099322496519 203948789316961648983744779)
  ·
    refine ⟨305923183975442473475617169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203948789316961648983744779 305923183975442473475617169)
    ·
      refine ⟨229442387981581855106712877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305923183975442473475617169 229442387981581855106712877)
      ·
        refine ⟨86040895493093195665017329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229442387981581855106712877 86040895493093195665017329)
        ·
          refine ⟨64530671619819896748762997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86040895493093195665017329 64530671619819896748762997)
          ·
            refine ⟨6049750464358115320196531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64530671619819896748762997 6049750464358115320196531)
            ·
              refine ⟨9074625696537172980294797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049750464358115320196531 9074625696537172980294797)
              ·
                refine ⟨3402984636201439867610549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9074625696537172980294797 3402984636201439867610549)
                ·
                  refine ⟨319029809643884987588489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3402984636201439867610549 319029809643884987588489)
                  ·
                    rfl

theorem cell23_5591775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 5].length) (baseStart_5591775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591775 prefixEnd_5591775 := by exact prefixLift 5591775
  have htrace : WordTrace (prefixWord ++ tailWord_5591775) baseStart_5591775 baseEnd_5591775 := by
    simpa [prefixWord, tailWord_5591775, baseEnd_5591775] using wordTrace_append hprefix tailTrace_5591775
  have hstable : (prefixWord ++ tailWord_5591775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591775).length < 2 ^ (prefixWord ++ tailWord_5591775).sum := by decide
  have hdescent : baseEnd_5591775 < baseStart_5591775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591798 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5591798 : Nat := 118140960795 + 5591798 * 2 ^ 59
def prefixEnd_5591798 : Nat := 4983230072969 + 3 ^ 40 * 5591798 * 2
def baseEnd_5591798 : Nat := 2871280096850018298308795

theorem tailTrace_5591798 : CollatzResearch.WordTrace tailWord_5591798 prefixEnd_5591798 2871280096850018298308795 := by
  unfold tailWord_5591798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12746851762242395244489503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135966418797252215941221365 12746851762242395244489503)
  ·
    refine ⟨19120277643363592866734255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12746851762242395244489503 19120277643363592866734255)
    ·
      refine ⟨28680416465045389300101383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19120277643363592866734255 28680416465045389300101383)
      ·
        refine ⟨43020624697568083950152075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28680416465045389300101383 43020624697568083950152075)
        ·
          refine ⟨64530937046352125925228113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43020624697568083950152075 64530937046352125925228113)
          ·
            refine ⟨48398202784764094443921085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64530937046352125925228113 48398202784764094443921085)
            ·
              refine ⟨18149326044286535416470407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48398202784764094443921085 18149326044286535416470407)
              ·
                refine ⟨27223989066429803124705611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18149326044286535416470407 27223989066429803124705611)
                ·
                  refine ⟨40835983599644704687058417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27223989066429803124705611 40835983599644704687058417)
                  ·
                    refine ⟨30626987699733528515293813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40835983599644704687058417 30626987699733528515293813)
                    ·
                      refine ⟨2871280096850018298308795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30626987699733528515293813 2871280096850018298308795)
                      ·
                        rfl

theorem cell23_5591798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5591798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591798 prefixEnd_5591798 := by exact prefixLift 5591798
  have htrace : WordTrace (prefixWord ++ tailWord_5591798) baseStart_5591798 baseEnd_5591798 := by
    simpa [prefixWord, tailWord_5591798, baseEnd_5591798] using wordTrace_append hprefix tailTrace_5591798
  have hstable : (prefixWord ++ tailWord_5591798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591798).length < 2 ^ (prefixWord ++ tailWord_5591798).sum := by decide
  have hdescent : baseEnd_5591798 < baseStart_5591798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591818 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_5591818 : Nat := 118140960795 + 5591818 * 2 ^ 59
def prefixEnd_5591818 : Nat := 4983230072969 + 3 ^ 40 * 5591818 * 2
def baseEnd_5591818 : Nat := 957096788821036073352901

theorem tailTrace_5591818 : CollatzResearch.WordTrace tailWord_5591818 prefixEnd_5591818 957096788821036073352901 := by
  unfold tailWord_5591818
  simp only [CollatzResearch.WordTrace]
  refine ⟨50987589413951466831890027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135966905103870578218373405 50987589413951466831890027)
  ·
    refine ⟨76481384120927200247835041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50987589413951466831890027 76481384120927200247835041)
    ·
      refine ⟨57361038090695400185876281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76481384120927200247835041 57361038090695400185876281)
      ·
        refine ⟨43020778568021550139407211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57361038090695400185876281 43020778568021550139407211)
        ·
          refine ⟨64531167852032325209110817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43020778568021550139407211 64531167852032325209110817)
          ·
            refine ⟨48398375889024243906833113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64531167852032325209110817 48398375889024243906833113)
            ·
              refine ⟨36298781916768182930124835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48398375889024243906833113 36298781916768182930124835)
              ·
                refine ⟨54448172875152274395187253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36298781916768182930124835 54448172875152274395187253)
                ·
                  refine ⟨5104516207045525724548805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54448172875152274395187253 5104516207045525724548805)
                  ·
                    refine ⟨957096788821036073352901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104516207045525724548805 957096788821036073352901)
                    ·
                      rfl

theorem cell23_5591818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_5591818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591818 prefixEnd_5591818 := by exact prefixLift 5591818
  have htrace : WordTrace (prefixWord ++ tailWord_5591818) baseStart_5591818 baseEnd_5591818 := by
    simpa [prefixWord, tailWord_5591818, baseEnd_5591818] using wordTrace_append hprefix tailTrace_5591818
  have hstable : (prefixWord ++ tailWord_5591818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591818).length < 2 ^ (prefixWord ++ tailWord_5591818).sum := by decide
  have hdescent : baseEnd_5591818 < baseStart_5591818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591875 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 3]
def baseStart_5591875 : Nat := 118140960795 + 5591875 * 2 ^ 59
def prefixEnd_5591875 : Nat := 4983230072969 + 3 ^ 40 * 5591875 * 2
def baseEnd_5591875 : Nat := 2871319634860414497045941

theorem tailTrace_5591875 : CollatzResearch.WordTrace tailWord_5591875 prefixEnd_5591875 2871319634860414497045941 := by
  unfold tailWord_5591875
  simp only [CollatzResearch.WordTrace]
  refine ⟨203952436616599366062385079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135968291077732910708256719 203952436616599366062385079)
  ·
    refine ⟨305928654924899049093577619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203952436616599366062385079 305928654924899049093577619)
    ·
      refine ⟨458892982387348573640366429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305928654924899049093577619 458892982387348573640366429)
      ·
        refine ⟨172084868395255715115137411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458892982387348573640366429 172084868395255715115137411)
        ·
          refine ⟨258127302592883572672706117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172084868395255715115137411 258127302592883572672706117)
          ·
            refine ⟨48398869236165669876132397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258127302592883572672706117 48398869236165669876132397)
            ·
              refine ⟨18149575963562126203549649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48398869236165669876132397 18149575963562126203549649)
              ·
                refine ⟨13612181972671594652662237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18149575963562126203549649 13612181972671594652662237)
                ·
                  refine ⟨5104568239751847994748339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13612181972671594652662237 5104568239751847994748339)
                  ·
                    refine ⟨7656852359627771992122509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104568239751847994748339 7656852359627771992122509)
                    ·
                      refine ⟨2871319634860414497045941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656852359627771992122509 2871319634860414497045941)
                      ·
                        rfl

theorem cell23_5591875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_5591875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591875 prefixEnd_5591875 := by exact prefixLift 5591875
  have htrace : WordTrace (prefixWord ++ tailWord_5591875) baseStart_5591875 baseEnd_5591875 := by
    simpa [prefixWord, tailWord_5591875, baseEnd_5591875] using wordTrace_append hprefix tailTrace_5591875
  have hstable : (prefixWord ++ tailWord_5591875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591875).length < 2 ^ (prefixWord ++ tailWord_5591875).sum := by decide
  have hdescent : baseEnd_5591875 < baseStart_5591875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591876 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5591876 : Nat := 118140960795 + 5591876 * 2 ^ 59
def prefixEnd_5591876 : Nat := 4983230072969 + 3 ^ 40 * 5591876 * 2
def baseEnd_5591876 : Nat := 2871320148341068993133437

theorem tailTrace_5591876 : CollatzResearch.WordTrace tailWord_5591876 prefixEnd_5591876 2871320148341068993133437 := by
  unfold tailWord_5591876
  simp only [CollatzResearch.WordTrace]
  refine ⟨101976236544797871616585741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135968315393063828822114321 101976236544797871616585741)
  ·
    refine ⟨38241088704299201856219653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101976236544797871616585741 38241088704299201856219653)
    ·
      refine ⟨7170204132056100348041185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38241088704299201856219653 7170204132056100348041185)
      ·
        refine ⟨5377653099042075261030889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7170204132056100348041185 5377653099042075261030889)
        ·
          refine ⟨4033239824281556445773167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5377653099042075261030889 4033239824281556445773167)
          ·
            refine ⟨6049859736422334668659751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033239824281556445773167 6049859736422334668659751)
            ·
              refine ⟨9074789604633502002989627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049859736422334668659751 9074789604633502002989627)
              ·
                refine ⟨13612184406950253004484441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074789604633502002989627 13612184406950253004484441)
                ·
                  refine ⟨10209138305212689753363331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13612184406950253004484441 10209138305212689753363331)
                  ·
                    refine ⟨15313707457819034630044997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10209138305212689753363331 15313707457819034630044997)
                    ·
                      refine ⟨2871320148341068993133437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15313707457819034630044997 2871320148341068993133437)
                      ·
                        rfl

theorem cell23_5591876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5591876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591876 prefixEnd_5591876 := by exact prefixLift 5591876
  have htrace : WordTrace (prefixWord ++ tailWord_5591876) baseStart_5591876 baseEnd_5591876 := by
    simpa [prefixWord, tailWord_5591876, baseEnd_5591876] using wordTrace_append hprefix tailTrace_5591876
  have hstable : (prefixWord ++ tailWord_5591876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591876).length < 2 ^ (prefixWord ++ tailWord_5591876).sum := by decide
  have hdescent : baseEnd_5591876 < baseStart_5591876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591895 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 1, 5]
def baseStart_5591895 : Nat := 118140960795 + 5591895 * 2 ^ 59
def prefixEnd_5591895 : Nat := 4983230072969 + 3 ^ 40 * 5591895 * 2
def baseEnd_5591895 : Nat := 957109968157834806265283

theorem tailTrace_5591895 : CollatzResearch.WordTrace tailWord_5591895 prefixEnd_5591895 957109968157834806265283 := by
  unfold tailWord_5591895
  simp only [CollatzResearch.WordTrace]
  refine ⟨203953166076526909478113139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135968777384351272985408759 203953166076526909478113139)
  ·
    refine ⟨305929749114790364217169709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203953166076526909478113139 305929749114790364217169709)
    ·
      refine ⟨114723655918046386581438641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305929749114790364217169709 114723655918046386581438641)
      ·
        refine ⟨86042741938534789936078981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114723655918046386581438641 86042741938534789936078981)
        ·
          refine ⟨16133014113475273113014809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86042741938534789936078981 16133014113475273113014809)
          ·
            refine ⟨12099760585106454834761107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16133014113475273113014809 12099760585106454834761107)
            ·
              refine ⟨18149640877659682252141661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12099760585106454834761107 18149640877659682252141661)
              ·
                refine ⟨6806115329122380844553123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18149640877659682252141661 6806115329122380844553123)
                ·
                  refine ⟨10209172993683571266829685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806115329122380844553123 10209172993683571266829685)
                  ·
                    refine ⟨957109968157834806265283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10209172993683571266829685 957109968157834806265283)
                    ·
                      rfl

theorem cell23_5591895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_5591895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591895 prefixEnd_5591895 := by exact prefixLift 5591895
  have htrace : WordTrace (prefixWord ++ tailWord_5591895) baseStart_5591895 baseEnd_5591895 := by
    simpa [prefixWord, tailWord_5591895, baseEnd_5591895] using wordTrace_append hprefix tailTrace_5591895
  have hstable : (prefixWord ++ tailWord_5591895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591895).length < 2 ^ (prefixWord ++ tailWord_5591895).sum := by decide
  have hdescent : baseEnd_5591895 < baseStart_5591895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591925 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5591925 : Nat := 118140960795 + 5591925 * 2 ^ 59
def prefixEnd_5591925 : Nat := 4983230072969 + 3 ^ 40 * 5591925 * 2
def baseEnd_5591925 : Nat := 957115102964379767140237

theorem tailTrace_5591925 : CollatzResearch.WordTrace tailWord_5591925 prefixEnd_5591925 957115102964379767140237 := by
  unfold tailWord_5591925
  simp only [CollatzResearch.WordTrace]
  refine ⟨203954260266418224601705229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135969506844278816401136819 203954260266418224601705229)
  ·
    refine ⟨76482847599906834225639461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203954260266418224601705229 76482847599906834225639461)
    ·
      refine ⟨14340533924982531417307399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76482847599906834225639461 14340533924982531417307399)
      ·
        refine ⟨21510800887473797125961099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340533924982531417307399 21510800887473797125961099)
        ·
          refine ⟨32266201331210695688941649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21510800887473797125961099 32266201331210695688941649)
          ·
            refine ⟨24199650998408021766706237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32266201331210695688941649 24199650998408021766706237)
            ·
              refine ⟨9074869124403008162514839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24199650998408021766706237 9074869124403008162514839)
              ·
                refine ⟨13612303686604512243772259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074869124403008162514839 13612303686604512243772259)
                ·
                  refine ⟨20418455529906768365658389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13612303686604512243772259 20418455529906768365658389)
                  ·
                    refine ⟨957115102964379767140237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20418455529906768365658389 957115102964379767140237)
                    ·
                      rfl

theorem cell23_5591925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5591925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591925 prefixEnd_5591925 := by exact prefixLift 5591925
  have htrace : WordTrace (prefixWord ++ tailWord_5591925) baseStart_5591925 baseEnd_5591925 := by
    simpa [prefixWord, tailWord_5591925, baseEnd_5591925] using wordTrace_append hprefix tailTrace_5591925
  have hstable : (prefixWord ++ tailWord_5591925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591925).length < 2 ^ (prefixWord ++ tailWord_5591925).sum := by decide
  have hdescent : baseEnd_5591925 < baseStart_5591925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591928 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_5591928 : Nat := 118140960795 + 5591928 * 2 ^ 59
def prefixEnd_5591928 : Nat := 4983230072969 + 3 ^ 40 * 5591928 * 2
def baseEnd_5591928 : Nat := 2871346849335102789683197

theorem tailTrace_5591928 : CollatzResearch.WordTrace tailWord_5591928 prefixEnd_5591928 2871346849335102789683197 := by
  unfold tailWord_5591928
  simp only [CollatzResearch.WordTrace]
  refine ⟨101977184842703678057032219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135969579790271570742709625 101977184842703678057032219)
  ·
    refine ⟨152965777264055517085548329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101977184842703678057032219 152965777264055517085548329)
    ·
      refine ⟨114724332948041637814161247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152965777264055517085548329 114724332948041637814161247)
      ·
        refine ⟨172086499422062456721241871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114724332948041637814161247 172086499422062456721241871)
        ·
          refine ⟨258129749133093685081862807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172086499422062456721241871 258129749133093685081862807)
          ·
            refine ⟨387194623699640527622794211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258129749133093685081862807 387194623699640527622794211)
            ·
              refine ⟨580791935549460791434191317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387194623699640527622794211 580791935549460791434191317)
              ·
                refine ⟨13612310989440487299238859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 580791935549460791434191317 13612310989440487299238859)
                ·
                  refine ⟨20418466484160730948858289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13612310989440487299238859 20418466484160730948858289)
                  ·
                    refine ⟨15313849863120548211643717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20418466484160730948858289 15313849863120548211643717)
                    ·
                      refine ⟨2871346849335102789683197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15313849863120548211643717 2871346849335102789683197)
                      ·
                        rfl

theorem cell23_5591928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_5591928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591928 prefixEnd_5591928 := by exact prefixLift 5591928
  have htrace : WordTrace (prefixWord ++ tailWord_5591928) baseStart_5591928 baseEnd_5591928 := by
    simpa [prefixWord, tailWord_5591928, baseEnd_5591928] using wordTrace_append hprefix tailTrace_5591928
  have hstable : (prefixWord ++ tailWord_5591928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591928).length < 2 ^ (prefixWord ++ tailWord_5591928).sum := by decide
  have hdescent : baseEnd_5591928 < baseStart_5591928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591935 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 3]
def baseStart_5591935 : Nat := 118140960795 + 5591935 * 2 ^ 59
def prefixEnd_5591935 : Nat := 4983230072969 + 3 ^ 40 * 5591935 * 2
def baseEnd_5591935 : Nat := 2871350443699684262295665

theorem tailTrace_5591935 : CollatzResearch.WordTrace tailWord_5591935 prefixEnd_5591935 2871350443699684262295665 := by
  unfold tailWord_5591935
  simp only [CollatzResearch.WordTrace]
  refine ⟨203954624996381996309569259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135969749997587997539712839 203954624996381996309569259)
  ·
    refine ⟨305931937494572994464353889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203954624996381996309569259 305931937494572994464353889)
    ·
      refine ⟨229448953120929745848265417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305931937494572994464353889 229448953120929745848265417)
      ·
        refine ⟨172086714840697309386199063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229448953120929745848265417 172086714840697309386199063)
        ·
          refine ⟨258130072261045964079298595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172086714840697309386199063 258130072261045964079298595)
          ·
            refine ⟨387195108391568946118947893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258130072261045964079298595 387195108391568946118947893)
            ·
              refine ⟨36299541411709588698651365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 387195108391568946118947893 36299541411709588698651365)
              ·
                refine ⟨6806164014695547880997131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36299541411709588698651365 6806164014695547880997131)
                ·
                  refine ⟨10209246022043321821495697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806164014695547880997131 10209246022043321821495697)
                  ·
                    refine ⟨7656934516532491366121773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10209246022043321821495697 7656934516532491366121773)
                    ·
                      refine ⟨2871350443699684262295665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7656934516532491366121773 2871350443699684262295665)
                      ·
                        rfl

theorem cell23_5591935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_5591935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591935 prefixEnd_5591935 := by exact prefixLift 5591935
  have htrace : WordTrace (prefixWord ++ tailWord_5591935) baseStart_5591935 baseEnd_5591935 := by
    simpa [prefixWord, tailWord_5591935, baseEnd_5591935] using wordTrace_append hprefix tailTrace_5591935
  have hstable : (prefixWord ++ tailWord_5591935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591935).length < 2 ^ (prefixWord ++ tailWord_5591935).sum := by decide
  have hdescent : baseEnd_5591935 < baseStart_5591935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5591992 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 3, 3, 2]
def baseStart_5591992 : Nat := 118140960795 + 5591992 * 2 ^ 59
def prefixEnd_5591992 : Nat := 4983230072969 + 3 ^ 40 * 5591992 * 2
def baseEnd_5591992 : Nat := 2871379712096990539282903

theorem tailTrace_5591992 : CollatzResearch.WordTrace tailWord_5591992 prefixEnd_5591992 2871379712096990539282903 := by
  unfold tailWord_5591992
  simp only [CollatzResearch.WordTrace]
  refine ⟨101978351978587747522197115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135971135971450330029596153 101978351978587747522197115)
  ·
    refine ⟨152967527967881621283295673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101978351978587747522197115 152967527967881621283295673)
    ·
      refine ⟨114725645975911215962471755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152967527967881621283295673 114725645975911215962471755)
      ·
        refine ⟨172088468963866823943707633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114725645975911215962471755 172088468963866823943707633)
        ·
          refine ⟨129066351722900117957780725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172088468963866823943707633 129066351722900117957780725)
          ·
            refine ⟨12099970474021886058541943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129066351722900117957780725 12099970474021886058541943)
            ·
              refine ⟨18149955711032829087812915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12099970474021886058541943 18149955711032829087812915)
              ·
                refine ⟨27224933566549243631719373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18149955711032829087812915 27224933566549243631719373)
                ·
                  refine ⟨10209350087455966361894765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27224933566549243631719373 10209350087455966361894765)
                  ·
                    refine ⟨3828506282795987385710537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10209350087455966361894765 3828506282795987385710537)
                    ·
                      refine ⟨2871379712096990539282903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828506282795987385710537 2871379712096990539282903)
                      ·
                        rfl

theorem cell23_5591992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_5591992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5591992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5591992 prefixEnd_5591992 := by exact prefixLift 5591992
  have htrace : WordTrace (prefixWord ++ tailWord_5591992) baseStart_5591992 baseEnd_5591992 := by
    simpa [prefixWord, tailWord_5591992, baseEnd_5591992] using wordTrace_append hprefix tailTrace_5591992
  have hstable : (prefixWord ++ tailWord_5591992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5591992).length < 2 ^ (prefixWord ++ tailWord_5591992).sum := by decide
  have hdescent : baseEnd_5591992 < baseStart_5591992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5591992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592006 : List Nat := [6, 1, 3, 1, 2, 10]
def baseStart_5592006 : Nat := 118140960795 + 5592006 * 2 ^ 59
def prefixEnd_5592006 : Nat := 4983230072969 + 3 ^ 40 * 5592006 * 2
def baseEnd_5592006 : Nat := 11816406999284582240773

theorem tailTrace_5592006 : CollatzResearch.WordTrace tailWord_5592006 prefixEnd_5592006 11816406999284582240773 := by
  unfold tailWord_5592006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373662955597649232356371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135971476386083183623602581 6373662955597649232356371)
  ·
    refine ⟨9560494433396473848534557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373662955597649232356371 9560494433396473848534557)
    ·
      refine ⟨3585185412523677693200459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9560494433396473848534557 3585185412523677693200459)
      ·
        refine ⟨5377778118785516539800689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585185412523677693200459 5377778118785516539800689)
        ·
          refine ⟨4033333589089137404850517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5377778118785516539800689 4033333589089137404850517)
          ·
            refine ⟨11816406999284582240773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4033333589089137404850517 11816406999284582240773)
            ·
              rfl

theorem cell23_5592006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 10].length) (baseStart_5592006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592006 prefixEnd_5592006 := by exact prefixLift 5592006
  have htrace : WordTrace (prefixWord ++ tailWord_5592006) baseStart_5592006 baseEnd_5592006 := by
    simpa [prefixWord, tailWord_5592006, baseEnd_5592006] using wordTrace_append hprefix tailTrace_5592006
  have hstable : (prefixWord ++ tailWord_5592006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592006).length < 2 ^ (prefixWord ++ tailWord_5592006).sum := by decide
  have hdescent : baseEnd_5592006 < baseStart_5592006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592022 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5592022 : Nat := 118140960795 + 5592022 * 2 ^ 59
def prefixEnd_5592022 : Nat := 4983230072969 + 3 ^ 40 * 5592022 * 2
def baseEnd_5592022 : Nat := 2871395116516625421907765

theorem tailTrace_5592022 : CollatzResearch.WordTrace tailWord_5592022 prefixEnd_5592022 2871395116516625421907765 := by
  unfold tailWord_5592022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747362384191675635499145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135971865431377873445324213 12747362384191675635499145)
  ·
    refine ⟨9560521788143756726624359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12747362384191675635499145 9560521788143756726624359)
    ·
      refine ⟨14340782682215635089936539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9560521788143756726624359 14340782682215635089936539)
      ·
        refine ⟨21511174023323452634904809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340782682215635089936539 21511174023323452634904809)
        ·
          refine ⟨16133380517492589476178607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21511174023323452634904809 16133380517492589476178607)
          ·
            refine ⟨24200070776238884214267911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16133380517492589476178607 24200070776238884214267911)
            ·
              refine ⟨36300106164358326321401867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24200070776238884214267911 36300106164358326321401867)
              ·
                refine ⟨54450159246537489482102801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36300106164358326321401867 54450159246537489482102801)
                ·
                  refine ⟨40837619434903117111577101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54450159246537489482102801 40837619434903117111577101)
                  ·
                    refine ⟨15314107288088668916841413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40837619434903117111577101 15314107288088668916841413)
                    ·
                      refine ⟨2871395116516625421907765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15314107288088668916841413 2871395116516625421907765)
                      ·
                        rfl

theorem cell23_5592022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5592022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592022 prefixEnd_5592022 := by exact prefixLift 5592022
  have htrace : WordTrace (prefixWord ++ tailWord_5592022) baseStart_5592022 baseEnd_5592022 := by
    simpa [prefixWord, tailWord_5592022, baseEnd_5592022] using wordTrace_append hprefix tailTrace_5592022
  have hstable : (prefixWord ++ tailWord_5592022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592022).length < 2 ^ (prefixWord ++ tailWord_5592022).sum := by decide
  have hdescent : baseEnd_5592022 < baseStart_5592022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592025 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_5592025 : Nat := 118140960795 + 5592025 * 2 ^ 59
def prefixEnd_5592025 : Nat := 4983230072969 + 3 ^ 40 * 5592025 * 2
def baseEnd_5592025 : Nat := 2871396656958588910170251

theorem tailTrace_5592025 : CollatzResearch.WordTrace tailWord_5592025 prefixEnd_5592025 2871396656958588910170251 := by
  unfold tailWord_5592025
  simp only [CollatzResearch.WordTrace]
  refine ⟨203957907566055941680345529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135971938377370627786897019 203957907566055941680345529)
  ·
    refine ⟨152968430674541956260259147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203957907566055941680345529 152968430674541956260259147)
    ·
      refine ⟨229452646011812934390388721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152968430674541956260259147 229452646011812934390388721)
      ·
        refine ⟨172089484508859700792791541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229452646011812934390388721 172089484508859700792791541)
        ·
          refine ⟨16133389172705596949324207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172089484508859700792791541 16133389172705596949324207)
          ·
            refine ⟨24200083759058395423986311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16133389172705596949324207 24200083759058395423986311)
            ·
              refine ⟨36300125638587593135979467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24200083759058395423986311 36300125638587593135979467)
              ·
                refine ⟨54450188457881389703969201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36300125638587593135979467 54450188457881389703969201)
                ·
                  refine ⟨40837641343411042277976901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54450188457881389703969201 40837641343411042277976901)
                  ·
                    refine ⟨7657057751889570427120669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40837641343411042277976901 7657057751889570427120669)
                    ·
                      refine ⟨2871396656958588910170251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7657057751889570427120669 2871396656958588910170251)
                      ·
                        rfl

theorem cell23_5592025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_5592025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592025 prefixEnd_5592025 := by exact prefixLift 5592025
  have htrace : WordTrace (prefixWord ++ tailWord_5592025) baseStart_5592025 baseEnd_5592025 := by
    simpa [prefixWord, tailWord_5592025, baseEnd_5592025] using wordTrace_append hprefix tailTrace_5592025
  have hstable : (prefixWord ++ tailWord_5592025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592025).length < 2 ^ (prefixWord ++ tailWord_5592025).sum := by decide
  have hdescent : baseEnd_5592025 < baseStart_5592025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592035 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5592035 : Nat := 118140960795 + 5592035 * 2 ^ 59
def prefixEnd_5592035 : Nat := 4983230072969 + 3 ^ 40 * 5592035 * 2
def baseEnd_5592035 : Nat := 2871401791765133871045205

theorem tailTrace_5592035 : CollatzResearch.WordTrace tailWord_5592035 prefixEnd_5592035 2871401791765133871045205 := by
  unfold tailWord_5592035
  simp only [CollatzResearch.WordTrace]
  refine ⟨203958272296019713388209559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135972181530679808925473039 203958272296019713388209559)
  ·
    refine ⟨305937408444029570082314339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203958272296019713388209559 305937408444029570082314339)
    ·
      refine ⟨458906112666044355123471509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305937408444029570082314339 458906112666044355123471509)
      ·
        refine ⟨21511224031220829146412727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 458906112666044355123471509 21511224031220829146412727)
        ·
          refine ⟨32266836046831243719619091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21511224031220829146412727 32266836046831243719619091)
          ·
            refine ⟨48400254070246865579428637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32266836046831243719619091 48400254070246865579428637)
            ·
              refine ⟨18150095276342574592285739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48400254070246865579428637 18150095276342574592285739)
              ·
                refine ⟨27225142914513861888428609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18150095276342574592285739 27225142914513861888428609)
                ·
                  refine ⟨20418857185885396416321457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27225142914513861888428609 20418857185885396416321457)
                  ·
                    refine ⟨15314142889414047312241093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20418857185885396416321457 15314142889414047312241093)
                    ·
                      refine ⟨2871401791765133871045205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15314142889414047312241093 2871401791765133871045205)
                      ·
                        rfl

theorem cell23_5592035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5592035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592035 prefixEnd_5592035 := by exact prefixLift 5592035
  have htrace : WordTrace (prefixWord ++ tailWord_5592035) baseStart_5592035 baseEnd_5592035 := by
    simpa [prefixWord, tailWord_5592035, baseEnd_5592035] using wordTrace_append hprefix tailTrace_5592035
  have hstable : (prefixWord ++ tailWord_5592035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592035).length < 2 ^ (prefixWord ++ tailWord_5592035).sum := by decide
  have hdescent : baseEnd_5592035 < baseStart_5592035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592039 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5592039 : Nat := 118140960795 + 5592039 * 2 ^ 59
def prefixEnd_5592039 : Nat := 4983230072969 + 3 ^ 40 * 5592039 * 2
def baseEnd_5592039 : Nat := 2871403845687751855395187

theorem tailTrace_5592039 : CollatzResearch.WordTrace tailWord_5592039 prefixEnd_5592039 2871403845687751855395187 := by
  unfold tailWord_5592039
  simp only [CollatzResearch.WordTrace]
  refine ⟨203958418188005222071355171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135972278792003481380903447 203958418188005222071355171)
  ·
    refine ⟨305937627282007833107032757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203958418188005222071355171 305937627282007833107032757)
    ·
      refine ⟨28681652557688234353784321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 305937627282007833107032757 28681652557688234353784321)
      ·
        refine ⟨21511239418266175765338241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28681652557688234353784321 21511239418266175765338241)
        ·
          refine ⟨16133429563699631824003681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21511239418266175765338241 16133429563699631824003681)
          ·
            refine ⟨12100072172774723868002761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16133429563699631824003681 12100072172774723868002761)
            ·
              refine ⟨9075054129581042901002071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12100072172774723868002761 9075054129581042901002071)
              ·
                refine ⟨13612581194371564351503107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9075054129581042901002071 13612581194371564351503107)
                ·
                  refine ⟨20418871791557346527254661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13612581194371564351503107 20418871791557346527254661)
                  ·
                    refine ⟨3828538460917002473860249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20418871791557346527254661 3828538460917002473860249)
                    ·
                      refine ⟨2871403845687751855395187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828538460917002473860249 2871403845687751855395187)
                      ·
                        rfl

theorem cell23_5592039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5592039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592039 prefixEnd_5592039 := by exact prefixLift 5592039
  have htrace : WordTrace (prefixWord ++ tailWord_5592039) baseStart_5592039 baseEnd_5592039 := by
    simpa [prefixWord, tailWord_5592039, baseEnd_5592039] using wordTrace_append hprefix tailTrace_5592039
  have hstable : (prefixWord ++ tailWord_5592039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592039).length < 2 ^ (prefixWord ++ tailWord_5592039).sum := by decide
  have hdescent : baseEnd_5592039 < baseStart_5592039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592095 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_5592095 : Nat := 118140960795 + 5592095 * 2 ^ 59
def prefixEnd_5592095 : Nat := 4983230072969 + 3 ^ 40 * 5592095 * 2
def baseEnd_5592095 : Nat := 2871432600604403636294929

theorem tailTrace_5592095 : CollatzResearch.WordTrace tailWord_5592095 prefixEnd_5592095 2871432600604403636294929 := by
  unfold tailWord_5592095
  simp only [CollatzResearch.WordTrace]
  refine ⟨203960460675802343635393739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135973640450534895756929159 203960460675802343635393739)
  ·
    refine ⟨305940691013703515453090609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203960460675802343635393739 305940691013703515453090609)
    ·
      refine ⟨229455518260277636589817957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305940691013703515453090609 229455518260277636589817957)
      ·
        refine ⟨43022909673802056860590867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229455518260277636589817957 43022909673802056860590867)
        ·
          refine ⟨64534364510703085290886301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43022909673802056860590867 64534364510703085290886301)
          ·
            refine ⟨24200386691513656984082363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64534364510703085290886301 24200386691513656984082363)
            ·
              refine ⟨36300580037270485476123545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24200386691513656984082363 36300580037270485476123545)
              ·
                refine ⟨27225435027952864107092659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36300580037270485476123545 27225435027952864107092659)
                ·
                  refine ⟨40838152541929296160638989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27225435027952864107092659 40838152541929296160638989)
                  ·
                    refine ⟨15314307203223486060239621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40838152541929296160638989 15314307203223486060239621)
                    ·
                      refine ⟨2871432600604403636294929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15314307203223486060239621 2871432600604403636294929)
                      ·
                        rfl

theorem cell23_5592095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_5592095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592095 prefixEnd_5592095 := by exact prefixLift 5592095
  have htrace : WordTrace (prefixWord ++ tailWord_5592095) baseStart_5592095 baseEnd_5592095 := by
    simpa [prefixWord, tailWord_5592095, baseEnd_5592095] using wordTrace_append hprefix tailTrace_5592095
  have hstable : (prefixWord ++ tailWord_5592095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592095).length < 2 ^ (prefixWord ++ tailWord_5592095).sum := by decide
  have hdescent : baseEnd_5592095 < baseStart_5592095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592129 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_5592129 : Nat := 118140960795 + 5592129 * 2 ^ 59
def prefixEnd_5592129 : Nat := 4983230072969 + 3 ^ 40 * 5592129 * 2
def baseEnd_5592129 : Nat := 2871450058946656503269773

theorem tailTrace_5592129 : CollatzResearch.WordTrace tailWord_5592129 prefixEnd_5592129 2871450058946656503269773 := by
  unfold tailWord_5592129
  simp only [CollatzResearch.WordTrace]
  refine ⟨203961700757679167442131441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135974467171786111628087627 203961700757679167442131441)
  ·
    refine ⟨152971275568259375581598581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203961700757679167442131441 152971275568259375581598581)
    ·
      refine ⟨14341057084524316460774867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152971275568259375581598581 14341057084524316460774867)
      ·
        refine ⟨21511585626786474691162301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14341057084524316460774867 21511585626786474691162301)
        ·
          refine ⟨8066844610044928009185863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21511585626786474691162301 8066844610044928009185863)
          ·
            refine ⟨12100266915067392013778795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8066844610044928009185863 12100266915067392013778795)
            ·
              refine ⟨18150400372601088020668193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12100266915067392013778795 18150400372601088020668193)
              ·
                refine ⟨13612800279450816015501145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18150400372601088020668193 13612800279450816015501145)
                ·
                  refine ⟨10209600209588112011625859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13612800279450816015501145 10209600209588112011625859)
                  ·
                    refine ⟨15314400314382168017438789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10209600209588112011625859 15314400314382168017438789)
                    ·
                      refine ⟨2871450058946656503269773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15314400314382168017438789 2871450058946656503269773)
                      ·
                        rfl

theorem cell23_5592129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_5592129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592129 prefixEnd_5592129 := by exact prefixLift 5592129
  have htrace : WordTrace (prefixWord ++ tailWord_5592129) baseStart_5592129 baseEnd_5592129 := by
    simpa [prefixWord, tailWord_5592129, baseEnd_5592129] using wordTrace_append hprefix tailTrace_5592129
  have hstable : (prefixWord ++ tailWord_5592129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592129).length < 2 ^ (prefixWord ++ tailWord_5592129).sum := by decide
  have hdescent : baseEnd_5592129 < baseStart_5592129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592135 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 8]
def baseStart_5592135 : Nat := 118140960795 + 5592135 * 2 ^ 59
def prefixEnd_5592135 : Nat := 4983230072969 + 3 ^ 40 * 5592135 * 2
def baseEnd_5592135 : Nat := 319050348870064831088305

theorem tailTrace_5592135 : CollatzResearch.WordTrace tailWord_5592135 prefixEnd_5592135 319050348870064831088305 := by
  unfold tailWord_5592135
  simp only [CollatzResearch.WordTrace]
  refine ⟨203961919595657430466849859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135974613063771620311233239 203961919595657430466849859)
  ·
    refine ⟨305942879393486145700274789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203961919595657430466849859 305942879393486145700274789)
    ·
      refine ⟨57364289886278652318801523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305942879393486145700274789 57364289886278652318801523)
      ·
        refine ⟨86046434829417978478202285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57364289886278652318801523 86046434829417978478202285)
        ·
          refine ⟨32267413061031741929325857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86046434829417978478202285 32267413061031741929325857)
          ·
            refine ⟨24200559795773806446994393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32267413061031741929325857 24200559795773806446994393)
            ·
              refine ⟨18150419846830354835245795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24200559795773806446994393 18150419846830354835245795)
              ·
                refine ⟨27225629770245532252868693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18150419846830354835245795 27225629770245532252868693)
                ·
                  refine ⟨319050348870064831088305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27225629770245532252868693 319050348870064831088305)
                  ·
                    rfl

theorem cell23_5592135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 8].length) (baseStart_5592135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592135 prefixEnd_5592135 := by exact prefixLift 5592135
  have htrace : WordTrace (prefixWord ++ tailWord_5592135) baseStart_5592135 baseEnd_5592135 := by
    simpa [prefixWord, tailWord_5592135, baseEnd_5592135] using wordTrace_append hprefix tailTrace_5592135
  have hstable : (prefixWord ++ tailWord_5592135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592135).length < 2 ^ (prefixWord ++ tailWord_5592135).sum := by decide
  have hdescent : baseEnd_5592135 < baseStart_5592135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592189 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_5592189 : Nat := 118140960795 + 5592189 * 2 ^ 59
def prefixEnd_5592189 : Nat := 4983230072969 + 3 ^ 40 * 5592189 * 2
def baseEnd_5592189 : Nat := 2871480867785926268519497

theorem tailTrace_5592189 : CollatzResearch.WordTrace tailWord_5592189 prefixEnd_5592189 2871480867785926268519497 := by
  unfold tailWord_5592189
  simp only [CollatzResearch.WordTrace]
  refine ⟨203963889137461797689315621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135975926091641198459543747 203963889137461797689315621)
  ·
    refine ⟨38243229213274087066746679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203963889137461797689315621 38243229213274087066746679)
    ·
      refine ⟨57364843819911130600120019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38243229213274087066746679 57364843819911130600120019)
      ·
        refine ⟨86047265729866695900180029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57364843819911130600120019 86047265729866695900180029)
        ·
          refine ⟨32267724648700010962567511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86047265729866695900180029 32267724648700010962567511)
          ·
            refine ⟨48401586973050016443851267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32267724648700010962567511 48401586973050016443851267)
            ·
              refine ⟨72602380459575024665776901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48401586973050016443851267 72602380459575024665776901)
              ·
                refine ⟨13612946336170317124833169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72602380459575024665776901 13612946336170317124833169)
                ·
                  refine ⟨10209709752127737843624877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13612946336170317124833169 10209709752127737843624877)
                  ·
                    refine ⟨3828641157047901691359329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10209709752127737843624877 3828641157047901691359329)
                    ·
                      refine ⟨2871480867785926268519497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828641157047901691359329 2871480867785926268519497)
                      ·
                        rfl

theorem cell23_5592189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_5592189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592189 prefixEnd_5592189 := by exact prefixLift 5592189
  have htrace : WordTrace (prefixWord ++ tailWord_5592189) baseStart_5592189 baseEnd_5592189 := by
    simpa [prefixWord, tailWord_5592189, baseEnd_5592189] using wordTrace_append hprefix tailTrace_5592189
  have hstable : (prefixWord ++ tailWord_5592189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592189).length < 2 ^ (prefixWord ++ tailWord_5592189).sum := by decide
  have hdescent : baseEnd_5592189 < baseStart_5592189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592195 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 3, 6]
def baseStart_5592195 : Nat := 118140960795 + 5592195 * 2 ^ 59
def prefixEnd_5592195 : Nat := 4983230072969 + 3 ^ 40 * 5592195 * 2
def baseEnd_5592195 : Nat := 957161316223284415014823

theorem tailTrace_5592195 : CollatzResearch.WordTrace tailWord_5592195 prefixEnd_5592195 957161316223284415014823 := by
  unfold tailWord_5592195
  simp only [CollatzResearch.WordTrace]
  refine ⟨203964107975440060714034039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135976071983626707142689359 203964107975440060714034039)
  ·
    refine ⟨305946161963160091071051059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203964107975440060714034039 305946161963160091071051059)
    ·
      refine ⟨458919242944740136606576589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305946161963160091071051059 458919242944740136606576589)
      ·
        refine ⟨172094716104277551227466221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458919242944740136606576589 172094716104277551227466221)
        ·
          refine ⟨64535518539104081710299833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172094716104277551227466221 64535518539104081710299833)
          ·
            refine ⟨48401638904328061282724875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64535518539104081710299833 48401638904328061282724875)
            ·
              refine ⟨72602458356492091924087313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48401638904328061282724875 72602458356492091924087313)
              ·
                refine ⟨54451843767369068943065485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72602458356492091924087313 54451843767369068943065485)
                ·
                  refine ⟨20419441412763400853649557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54451843767369068943065485 20419441412763400853649557)
                  ·
                    refine ⟨957161316223284415014823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20419441412763400853649557 957161316223284415014823)
                    ·
                      rfl

theorem cell23_5592195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 6].length) (baseStart_5592195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592195 prefixEnd_5592195 := by exact prefixLift 5592195
  have htrace : WordTrace (prefixWord ++ tailWord_5592195) baseStart_5592195 baseEnd_5592195 := by
    simpa [prefixWord, tailWord_5592195, baseEnd_5592195] using wordTrace_append hprefix tailTrace_5592195
  have hstable : (prefixWord ++ tailWord_5592195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592195).length < 2 ^ (prefixWord ++ tailWord_5592195).sum := by decide
  have hdescent : baseEnd_5592195 < baseStart_5592195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592202 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5592202 : Nat := 118140960795 + 5592202 * 2 ^ 59
def prefixEnd_5592202 : Nat := 4983230072969 + 3 ^ 40 * 5592202 * 2
def baseEnd_5592202 : Nat := 2871487543034434717656937

theorem tailTrace_5592202 : CollatzResearch.WordTrace tailWord_5592202 prefixEnd_5592202 2871487543034434717656937 := by
  unfold tailWord_5592202
  simp only [CollatzResearch.WordTrace]
  refine ⟨50991090821603675227384715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135976242190943133939692573 50991090821603675227384715)
  ·
    refine ⟨76486636232405512841077073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50991090821603675227384715 76486636232405512841077073)
    ·
      refine ⟨57364977174304134630807805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76486636232405512841077073 57364977174304134630807805)
      ·
        refine ⟨21511866440364050486552927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57364977174304134630807805 21511866440364050486552927)
        ·
          refine ⟨32267799660546075729829391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21511866440364050486552927 32267799660546075729829391)
          ·
            refine ⟨48401699490819113594744087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32267799660546075729829391 48401699490819113594744087)
            ·
              refine ⟨72602549236228670392116131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48401699490819113594744087 72602549236228670392116131)
              ·
                refine ⟨108903823854343005588174197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72602549236228670392116131 108903823854343005588174197)
                ·
                  refine ⟨10209733486344656773891331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108903823854343005588174197 10209733486344656773891331)
                  ·
                    refine ⟨15314600229516985160836997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10209733486344656773891331 15314600229516985160836997)
                    ·
                      refine ⟨2871487543034434717656937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15314600229516985160836997 2871487543034434717656937)
                      ·
                        rfl

theorem cell23_5592202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5592202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592202 prefixEnd_5592202 := by exact prefixLift 5592202
  have htrace : WordTrace (prefixWord ++ tailWord_5592202) baseStart_5592202 baseEnd_5592202 := by
    simpa [prefixWord, tailWord_5592202, baseEnd_5592202] using wordTrace_append hprefix tailTrace_5592202
  have hstable : (prefixWord ++ tailWord_5592202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592202).length < 2 ^ (prefixWord ++ tailWord_5592202).sum := by decide
  have hdescent : baseEnd_5592202 < baseStart_5592202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592223 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5592223 : Nat := 118140960795 + 5592223 * 2 ^ 59
def prefixEnd_5592223 : Nat := 4983230072969 + 3 ^ 40 * 5592223 * 2
def baseEnd_5592223 : Nat := 2871498326128179135494341

theorem tailTrace_5592223 : CollatzResearch.WordTrace tailWord_5592223 prefixEnd_5592223 2871498326128179135494341 := by
  unfold tailWord_5592223
  simp only [CollatzResearch.WordTrace]
  refine ⟨203965129219338621496053323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135976752812892414330702215 203965129219338621496053323)
  ·
    refine ⟨305947693829007932244079985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203965129219338621496053323 305947693829007932244079985)
    ·
      refine ⟨229460770371755949183059989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305947693829007932244079985 229460770371755949183059989)
      ·
        refine ⟨10755973611176060117955937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229460770371755949183059989 10755973611176060117955937)
        ·
          refine ⟨8066980208382045088466953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10755973611176060117955937 8066980208382045088466953)
          ·
            refine ⟨6050235156286533816350215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8066980208382045088466953 6050235156286533816350215)
            ·
              refine ⟨9075352734429800724525323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050235156286533816350215 9075352734429800724525323)
              ·
                refine ⟨13613029101644701086787985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9075352734429800724525323 13613029101644701086787985)
                ·
                  refine ⟨10209771826233525815090989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13613029101644701086787985 10209771826233525815090989)
                  ·
                    refine ⟨3828664434837572180659121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10209771826233525815090989 3828664434837572180659121)
                    ·
                      refine ⟨2871498326128179135494341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828664434837572180659121 2871498326128179135494341)
                      ·
                        rfl

theorem cell23_5592223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5592223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592223 prefixEnd_5592223 := by exact prefixLift 5592223
  have htrace : WordTrace (prefixWord ++ tailWord_5592223) baseStart_5592223 baseEnd_5592223 := by
    simpa [prefixWord, tailWord_5592223, baseEnd_5592223] using wordTrace_append hprefix tailTrace_5592223
  have hstable : (prefixWord ++ tailWord_5592223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592223).length < 2 ^ (prefixWord ++ tailWord_5592223).sum := by decide
  have hdescent : baseEnd_5592223 < baseStart_5592223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592253 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_5592253 : Nat := 118140960795 + 5592253 * 2 ^ 59
def prefixEnd_5592253 : Nat := 4983230072969 + 3 ^ 40 * 5592253 * 2
def baseEnd_5592253 : Nat := 2871513730547814018119203

theorem tailTrace_5592253 : CollatzResearch.WordTrace tailWord_5592253 prefixEnd_5592253 2871513730547814018119203 := by
  unfold tailWord_5592253
  simp only [CollatzResearch.WordTrace]
  refine ⟨203966223409229936619645413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135977482272819957746430275 203966223409229936619645413)
  ·
    refine ⟨38243666889230613116183515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203966223409229936619645413 38243666889230613116183515)
    ·
      refine ⟨57365500333845919674275273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38243666889230613116183515 57365500333845919674275273)
      ·
        refine ⟨43024125250384439755706455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57365500333845919674275273 43024125250384439755706455)
        ·
          refine ⟨64536187875576659633559683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43024125250384439755706455 64536187875576659633559683)
          ·
            refine ⟨96804281813364989450339525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64536187875576659633559683 96804281813364989450339525)
            ·
              refine ⟨18150802840005935521938661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96804281813364989450339525 18150802840005935521938661)
              ·
                refine ⟨3403275532501112910363499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18150802840005935521938661 3403275532501112910363499)
                ·
                  refine ⟨5104913298751669365545249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403275532501112910363499 5104913298751669365545249)
                  ·
                    refine ⟨3828684974063752024158937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104913298751669365545249 3828684974063752024158937)
                    ·
                      refine ⟨2871513730547814018119203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828684974063752024158937 2871513730547814018119203)
                      ·
                        rfl

theorem cell23_5592253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_5592253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592253 prefixEnd_5592253 := by exact prefixLift 5592253
  have htrace : WordTrace (prefixWord ++ tailWord_5592253) baseStart_5592253 baseEnd_5592253 := by
    simpa [prefixWord, tailWord_5592253, baseEnd_5592253] using wordTrace_append hprefix tailTrace_5592253
  have hstable : (prefixWord ++ tailWord_5592253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592253).length < 2 ^ (prefixWord ++ tailWord_5592253).sum := by decide
  have hdescent : baseEnd_5592253 < baseStart_5592253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592255 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 9]
def baseStart_5592255 : Nat := 118140960795 + 5592255 * 2 ^ 59
def prefixEnd_5592255 : Nat := 4983230072969 + 3 ^ 40 * 5592255 * 2
def baseEnd_5592255 : Nat := 957171585836374336764731

theorem tailTrace_5592255 : CollatzResearch.WordTrace tailWord_5592255 prefixEnd_5592255 957171585836374336764731 := by
  unfold tailWord_5592255
  simp only [CollatzResearch.WordTrace]
  refine ⟨203966296355222690961218219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135977530903481793974145479 203966296355222690961218219)
  ·
    refine ⟨305949444532834036441827329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203966296355222690961218219 305949444532834036441827329)
    ·
      refine ⟨229462083399625527331370497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305949444532834036441827329 229462083399625527331370497)
      ·
        refine ⟨172096562549719145498527873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229462083399625527331370497 172096562549719145498527873)
        ·
          refine ⟨129072421912289359123895905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172096562549719145498527873 129072421912289359123895905)
          ·
            refine ⟨96804316434217019342921929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129072421912289359123895905 96804316434217019342921929)
            ·
              refine ⟨72603237325662764507191447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96804316434217019342921929 72603237325662764507191447)
              ·
                refine ⟨108904855988494146760787171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72603237325662764507191447 108904855988494146760787171)
                ·
                  refine ⟨163357283982741220141180757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108904855988494146760787171 163357283982741220141180757)
                  ·
                    refine ⟨957171585836374336764731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 163357283982741220141180757 957171585836374336764731)
                    ·
                      rfl

theorem cell23_5592255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_5592255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592255 prefixEnd_5592255 := by exact prefixLift 5592255
  have htrace : WordTrace (prefixWord ++ tailWord_5592255) baseStart_5592255 baseEnd_5592255 := by
    simpa [prefixWord, tailWord_5592255, baseEnd_5592255] using wordTrace_append hprefix tailTrace_5592255
  have hstable : (prefixWord ++ tailWord_5592255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592255).length < 2 ^ (prefixWord ++ tailWord_5592255).sum := by decide
  have hdescent : baseEnd_5592255 < baseStart_5592255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592279 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 3, 3, 2]
def baseStart_5592279 : Nat := 118140960795 + 5592279 * 2 ^ 59
def prefixEnd_5592279 : Nat := 4983230072969 + 3 ^ 40 * 5592279 * 2
def baseEnd_5592279 : Nat := 2871527081044830916394083

theorem tailTrace_5592279 : CollatzResearch.WordTrace tailWord_5592279 prefixEnd_5592279 2871527081044830916394083 := by
  unfold tailWord_5592279
  simp only [CollatzResearch.WordTrace]
  refine ⟨203967171707135743060091891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135978114471423828706727927 203967171707135743060091891)
  ·
    refine ⟨305950757560703614590137837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203967171707135743060091891 305950757560703614590137837)
    ·
      refine ⟨114731534085263855471301689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305950757560703614590137837 114731534085263855471301689)
      ·
        refine ⟨86048650563947891603476267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114731534085263855471301689 86048650563947891603476267)
        ·
          refine ⟨129072975845921837405214401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86048650563947891603476267 129072975845921837405214401)
          ·
            refine ⟨96804731884441378053910801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129072975845921837405214401 96804731884441378053910801)
            ·
              refine ⟨72603548913331033540433101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96804731884441378053910801 72603548913331033540433101)
              ·
                refine ⟨27226330842499137577662413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72603548913331033540433101 27226330842499137577662413)
                ·
                  refine ⟨10209874065937176591623405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27226330842499137577662413 10209874065937176591623405)
                  ·
                    refine ⟨3828702774726441221858777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10209874065937176591623405 3828702774726441221858777)
                    ·
                      refine ⟨2871527081044830916394083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828702774726441221858777 2871527081044830916394083)
                      ·
                        rfl

theorem cell23_5592279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_5592279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592279 prefixEnd_5592279 := by exact prefixLift 5592279
  have htrace : WordTrace (prefixWord ++ tailWord_5592279) baseStart_5592279 baseEnd_5592279 := by
    simpa [prefixWord, tailWord_5592279, baseEnd_5592279] using wordTrace_append hprefix tailTrace_5592279
  have hstable : (prefixWord ++ tailWord_5592279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592279).length < 2 ^ (prefixWord ++ tailWord_5592279).sum := by decide
  have hdescent : baseEnd_5592279 < baseStart_5592279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592296 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_5592296 : Nat := 118140960795 + 5592296 * 2 ^ 59
def prefixEnd_5592296 : Nat := 4983230072969 + 3 ^ 40 * 5592296 * 2
def baseEnd_5592296 : Nat := 2871535810215957349881505

theorem tailTrace_5592296 : CollatzResearch.WordTrace tailWord_5592296 prefixEnd_5592296 2871535810215957349881505 := by
  unfold tailWord_5592296
  simp only [CollatzResearch.WordTrace]
  refine ⟨101983895874037077481730371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135978527832049436642307161 101983895874037077481730371)
  ·
    refine ⟨152975843811055616222595557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101983895874037077481730371 152975843811055616222595557)
    ·
      refine ⟨28682970714572928041736667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152975843811055616222595557 28682970714572928041736667)
      ·
        refine ⟨43024456071859392062605001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28682970714572928041736667 43024456071859392062605001)
        ·
          refine ⟨32268342053894544046953751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43024456071859392062605001 32268342053894544046953751)
          ·
            refine ⟨48402513080841816070430627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32268342053894544046953751 48402513080841816070430627)
            ·
              refine ⟨72603769621262724105645941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48402513080841816070430627 72603769621262724105645941)
              ·
                refine ⟨6806603401993380384904307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72603769621262724105645941 6806603401993380384904307)
                ·
                  refine ⟨10209905102990070577356461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806603401993380384904307 10209905102990070577356461)
                  ·
                    refine ⟨3828714413621276466508673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10209905102990070577356461 3828714413621276466508673)
                    ·
                      refine ⟨2871535810215957349881505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828714413621276466508673 2871535810215957349881505)
                      ·
                        rfl

theorem cell23_5592296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_5592296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592296 prefixEnd_5592296 := by exact prefixLift 5592296
  have htrace : WordTrace (prefixWord ++ tailWord_5592296) baseStart_5592296 baseEnd_5592296 := by
    simpa [prefixWord, tailWord_5592296, baseEnd_5592296] using wordTrace_append hprefix tailTrace_5592296
  have hstable : (prefixWord ++ tailWord_5592296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592296).length < 2 ^ (prefixWord ++ tailWord_5592296).sum := by decide
  have hdescent : baseEnd_5592296 < baseStart_5592296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592302 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_5592302 : Nat := 118140960795 + 5592302 * 2 ^ 59
def prefixEnd_5592302 : Nat := 4983230072969 + 3 ^ 40 * 5592302 * 2
def baseEnd_5592302 : Nat := 957179630366628108802159

theorem tailTrace_5592302 : CollatzResearch.WordTrace tailWord_5592302 prefixEnd_5592302 957179630366628108802159 := by
  unfold tailWord_5592302
  simp only [CollatzResearch.WordTrace]
  refine ⟨25496001323256552248522395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135978673724034945325452773 25496001323256552248522395)
  ·
    refine ⟨38244001984884828372783593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25496001323256552248522395 38244001984884828372783593)
    ·
      refine ⟨28683001488663621279587695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38244001984884828372783593 28683001488663621279587695)
      ·
        refine ⟨43024502232995431919381543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28683001488663621279587695 43024502232995431919381543)
        ·
          refine ⟨64536753349493147879072315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43024502232995431919381543 64536753349493147879072315)
          ·
            refine ⟨96805130024239721818608473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64536753349493147879072315 96805130024239721818608473)
            ·
              refine ⟨72603847518179791363956355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96805130024239721818608473 72603847518179791363956355)
              ·
                refine ⟨108905771277269687045934533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72603847518179791363956355 108905771277269687045934533)
                ·
                  refine ⟨20419832114488066321112725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108905771277269687045934533 20419832114488066321112725)
                  ·
                    refine ⟨957179630366628108802159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20419832114488066321112725 957179630366628108802159)
                    ·
                      rfl

theorem cell23_5592302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_5592302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592302 prefixEnd_5592302 := by exact prefixLift 5592302
  have htrace : WordTrace (prefixWord ++ tailWord_5592302) baseStart_5592302 baseEnd_5592302 := by
    simpa [prefixWord, tailWord_5592302, baseEnd_5592302] using wordTrace_append hprefix tailTrace_5592302
  have hstable : (prefixWord ++ tailWord_5592302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592302).length < 2 ^ (prefixWord ++ tailWord_5592302).sum := by decide
  have hdescent : baseEnd_5592302 < baseStart_5592302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592360 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_5592360 : Nat := 118140960795 + 5592360 * 2 ^ 59
def prefixEnd_5592360 : Nat := 4983230072969 + 3 ^ 40 * 5592360 * 2
def baseEnd_5592360 : Nat := 2871568672977845099481211

theorem tailTrace_5592360 : CollatzResearch.WordTrace tailWord_5592360 prefixEnd_5592360 2871568672977845099481211 := by
  unfold tailWord_5592360
  simp only [CollatzResearch.WordTrace]
  refine ⟨101985063009921146946895267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135980084013228195929193689 101985063009921146946895267)
  ·
    refine ⟨152977594514881720420342901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101985063009921146946895267 152977594514881720420342901)
    ·
      refine ⟨14341649485770161289407147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152977594514881720420342901 14341649485770161289407147)
      ·
        refine ⟨21512474228655241934110721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14341649485770161289407147 21512474228655241934110721)
        ·
          refine ⟨16134355671491431450583041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21512474228655241934110721 16134355671491431450583041)
          ·
            refine ⟨12100766753618573587937281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16134355671491431450583041 12100766753618573587937281)
            ·
              refine ⟨9075575065213930190952961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12100766753618573587937281 9075575065213930190952961)
              ·
                refine ⟨6806681298910447643214721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9075575065213930190952961 6806681298910447643214721)
                ·
                  refine ⟨5105010974182835732411041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806681298910447643214721 5105010974182835732411041)
                  ·
                    refine ⟨3828758230637126799308281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5105010974182835732411041 3828758230637126799308281)
                    ·
                      refine ⟨2871568672977845099481211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828758230637126799308281 2871568672977845099481211)
                      ·
                        rfl

theorem cell23_5592360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_5592360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592360 prefixEnd_5592360 := by exact prefixLift 5592360
  have htrace : WordTrace (prefixWord ++ tailWord_5592360) baseStart_5592360 baseEnd_5592360 := by
    simpa [prefixWord, tailWord_5592360, baseEnd_5592360] using wordTrace_append hprefix tailTrace_5592360
  have hstable : (prefixWord ++ tailWord_5592360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592360).length < 2 ^ (prefixWord ++ tailWord_5592360).sum := by decide
  have hdescent : baseEnd_5592360 < baseStart_5592360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592396 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_5592396 : Nat := 118140960795 + 5592396 * 2 ^ 59
def prefixEnd_5592396 : Nat := 4983230072969 + 3 ^ 40 * 5592396 * 2
def baseEnd_5592396 : Nat := 957195719427135652877015

theorem tailTrace_5592396 : CollatzResearch.WordTrace tailWord_5592396 prefixEnd_5592396 957195719427135652877015 := by
  unfold tailWord_5592396
  simp only [CollatzResearch.WordTrace]
  refine ⟨101985719523855936021050521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135980959365141248028067361 101985719523855936021050521)
  ·
    refine ⟨76489289642891952015787891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101985719523855936021050521 76489289642891952015787891)
    ·
      refine ⟨114733934464337928023681837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76489289642891952015787891 114733934464337928023681837)
      ·
        refine ⟨43025225424126723008880689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114733934464337928023681837 43025225424126723008880689)
        ·
          refine ⟨32268919068095042256660517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43025225424126723008880689 32268919068095042256660517)
          ·
            refine ⟨6050422325267820423123847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32268919068095042256660517 6050422325267820423123847)
            ·
              refine ⟨9075633487901730634685771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050422325267820423123847 9075633487901730634685771)
              ·
                refine ⟨13613450231852595952028657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9075633487901730634685771 13613450231852595952028657)
                ·
                  refine ⟨10210087673889446964021493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13613450231852595952028657 10210087673889446964021493)
                  ·
                    refine ⟨957195719427135652877015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10210087673889446964021493 957195719427135652877015)
                    ·
                      rfl

theorem cell23_5592396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_5592396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592396 prefixEnd_5592396 := by exact prefixLift 5592396
  have htrace : WordTrace (prefixWord ++ tailWord_5592396) baseStart_5592396 baseEnd_5592396 := by
    simpa [prefixWord, tailWord_5592396, baseEnd_5592396] using wordTrace_append hprefix tailTrace_5592396
  have hstable : (prefixWord ++ tailWord_5592396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592396).length < 2 ^ (prefixWord ++ tailWord_5592396).sum := by decide
  have hdescent : baseEnd_5592396 < baseStart_5592396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592416 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 2, 4, 2]
def baseStart_5592416 : Nat := 118140960795 + 5592416 * 2 ^ 59
def prefixEnd_5592416 : Nat := 4983230072969 + 3 ^ 40 * 5592416 * 2
def baseEnd_5592416 : Nat := 2871597427894496880380953

theorem tailTrace_5592416 : CollatzResearch.WordTrace tailWord_5592416 prefixEnd_5592416 2871597427894496880380953 := by
  unfold tailWord_5592416
  simp only [CollatzResearch.WordTrace]
  refine ⟨101986084253819707728914551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135981445671759610305219401 101986084253819707728914551)
  ·
    refine ⟨152979126380729561593371827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101986084253819707728914551 152979126380729561593371827)
    ·
      refine ⟨229468689571094342390057741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152979126380729561593371827 229468689571094342390057741)
      ·
        refine ⟨86050758589160378396271653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229468689571094342390057741 86050758589160378396271653)
        ·
          refine ⟨16134517235467570949300935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86050758589160378396271653 16134517235467570949300935)
          ·
            refine ⟨24201775853201356423951403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16134517235467570949300935 24201775853201356423951403)
            ·
              refine ⟨36302663779802034635927105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24201775853201356423951403 36302663779802034635927105)
              ·
                refine ⟨27226997834851525976945329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36302663779802034635927105 27226997834851525976945329)
                ·
                  refine ⟨20420248376138644482708997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27226997834851525976945329 20420248376138644482708997)
                  ·
                    refine ⟨3828796570525995840507937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20420248376138644482708997 3828796570525995840507937)
                    ·
                      refine ⟨2871597427894496880380953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828796570525995840507937 2871597427894496880380953)
                      ·
                        rfl

theorem cell23_5592416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_5592416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592416 prefixEnd_5592416 := by exact prefixLift 5592416
  have htrace : WordTrace (prefixWord ++ tailWord_5592416) baseStart_5592416 baseEnd_5592416 := by
    simpa [prefixWord, tailWord_5592416, baseEnd_5592416] using wordTrace_append hprefix tailTrace_5592416
  have hstable : (prefixWord ++ tailWord_5592416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592416).length < 2 ^ (prefixWord ++ tailWord_5592416).sum := by decide
  have hdescent : baseEnd_5592416 < baseStart_5592416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592516 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_5592516 : Nat := 118140960795 + 5592516 * 2 ^ 59
def prefixEnd_5592516 : Nat := 4983230072969 + 3 ^ 40 * 5592516 * 2
def baseEnd_5592516 : Nat := 957216258653315496376831

theorem tailTrace_5592516 : CollatzResearch.WordTrace tailWord_5592516 prefixEnd_5592516 957216258653315496376831 := by
  unfold tailWord_5592516
  simp only [CollatzResearch.WordTrace]
  refine ⟨101987907903638566268234701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135983877204851421690979601 101987907903638566268234701)
  ·
    refine ⟨38245465463864462350588013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101987907903638566268234701 38245465463864462350588013)
    ·
      refine ⟨14342049548949173381470505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38245465463864462350588013 14342049548949173381470505)
      ·
        refine ⟨10756537161711880036102879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14342049548949173381470505 10756537161711880036102879)
        ·
          refine ⟨16134805742567820054154319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10756537161711880036102879 16134805742567820054154319)
          ·
            refine ⟨24202208613851730081231479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16134805742567820054154319 24202208613851730081231479)
            ·
              refine ⟨36303312920777595121847219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24202208613851730081231479 36303312920777595121847219)
              ·
                refine ⟨54454969381166392682770829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36303312920777595121847219 54454969381166392682770829)
                ·
                  refine ⟨20420613517937397256039061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54454969381166392682770829 20420613517937397256039061)
                  ·
                    refine ⟨957216258653315496376831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20420613517937397256039061 957216258653315496376831)
                    ·
                      rfl

theorem cell23_5592516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_5592516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592516 prefixEnd_5592516 := by exact prefixLift 5592516
  have htrace : WordTrace (prefixWord ++ tailWord_5592516) baseStart_5592516 baseEnd_5592516 := by
    simpa [prefixWord, tailWord_5592516, baseEnd_5592516] using wordTrace_append hprefix tailTrace_5592516
  have hstable : (prefixWord ++ tailWord_5592516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592516).length < 2 ^ (prefixWord ++ tailWord_5592516).sum := by decide
  have hdescent : baseEnd_5592516 < baseStart_5592516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592526 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_5592526 : Nat := 118140960795 + 5592526 * 2 ^ 59
def prefixEnd_5592526 : Nat := 4983230072969 + 3 ^ 40 * 5592526 * 2
def baseEnd_5592526 : Nat := 2871653910766491450005447

theorem tailTrace_5592526 : CollatzResearch.WordTrace tailWord_5592526 prefixEnd_5592526 2871653910766491450005447 := by
  unfold tailWord_5592526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497022567155113030541679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135984120358160602829555621 25497022567155113030541679)
  ·
    refine ⟨38245533850732669545812519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25497022567155113030541679 38245533850732669545812519)
    ·
      refine ⟨57368300776099004318718779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38245533850732669545812519 57368300776099004318718779)
      ·
        refine ⟨86052451164148506478078169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57368300776099004318718779 86052451164148506478078169)
        ·
          refine ⟨64539338373111379858558627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86052451164148506478078169 64539338373111379858558627)
          ·
            refine ⟨96809007559667069787837941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64539338373111379858558627 96809007559667069787837941)
            ·
              refine ⟨9075844458718787792609807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96809007559667069787837941 9075844458718787792609807)
              ·
                refine ⟨13613766688078181688914711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9075844458718787792609807 13613766688078181688914711)
                ·
                  refine ⟨20420650032117272533372067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13613766688078181688914711 20420650032117272533372067)
                  ·
                    refine ⟨30630975048175908800058101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20420650032117272533372067 30630975048175908800058101)
                    ·
                      refine ⟨2871653910766491450005447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30630975048175908800058101 2871653910766491450005447)
                      ·
                        rfl

theorem cell23_5592526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_5592526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592526 prefixEnd_5592526 := by exact prefixLift 5592526
  have htrace : WordTrace (prefixWord ++ tailWord_5592526) baseStart_5592526 baseEnd_5592526 := by
    simpa [prefixWord, tailWord_5592526, baseEnd_5592526] using wordTrace_append hprefix tailTrace_5592526
  have hstable : (prefixWord ++ tailWord_5592526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592526).length < 2 ^ (prefixWord ++ tailWord_5592526).sum := by decide
  have hdescent : baseEnd_5592526 < baseStart_5592526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592533 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_5592533 : Nat := 118140960795 + 5592533 * 2 ^ 59
def prefixEnd_5592533 : Nat := 4983230072969 + 3 ^ 40 * 5592533 * 2
def baseEnd_5592533 : Nat := 957219168377024307539305

theorem tailTrace_5592533 : CollatzResearch.WordTrace tailWord_5592533 prefixEnd_5592533 957219168377024307539305 := by
  unfold tailWord_5592533
  simp only [CollatzResearch.WordTrace]
  refine ⟨203976435848215544439838253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135984290565477029626558835 203976435848215544439838253)
  ·
    refine ⟨76491163443080829164939345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203976435848215544439838253 76491163443080829164939345)
    ·
      refine ⟨57368372582310621873704509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76491163443080829164939345 57368372582310621873704509)
      ·
        refine ⟨21513139718366483202639191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57368372582310621873704509 21513139718366483202639191)
        ·
          refine ⟨32269709577549724803958787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21513139718366483202639191 32269709577549724803958787)
          ·
            refine ⟨48404564366324587205938181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32269709577549724803958787 48404564366324587205938181)
            ·
              refine ⟨9075855818685860101113409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48404564366324587205938181 9075855818685860101113409)
              ·
                refine ⟨6806891864014395075835057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9075855818685860101113409 6806891864014395075835057)
                ·
                  refine ⟨5105168898010796306876293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806891864014395075835057 5105168898010796306876293)
                  ·
                    refine ⟨957219168377024307539305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5105168898010796306876293 957219168377024307539305)
                    ·
                      rfl

theorem cell23_5592533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_5592533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592533 prefixEnd_5592533 := by exact prefixLift 5592533
  have htrace : WordTrace (prefixWord ++ tailWord_5592533) baseStart_5592533 baseEnd_5592533 := by
    simpa [prefixWord, tailWord_5592533, baseEnd_5592533] using wordTrace_append hprefix tailTrace_5592533
  have hstable : (prefixWord ++ tailWord_5592533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592533).length < 2 ^ (prefixWord ++ tailWord_5592533).sum := by decide
  have hdescent : baseEnd_5592533 < baseStart_5592533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592534 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_5592534 : Nat := 118140960795 + 5592534 * 2 ^ 59
def prefixEnd_5592534 : Nat := 4983230072969 + 3 ^ 40 * 5592534 * 2
def baseEnd_5592534 : Nat := 2871658018611727418705411

theorem tailTrace_5592534 : CollatzResearch.WordTrace tailWord_5592534 prefixEnd_5592534 2871658018611727418705411 := by
  unfold tailWord_5592534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12748529520075745100664041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135984314880807947740416437 12748529520075745100664041)
  ·
    refine ⟨9561397140056808825498031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12748529520075745100664041 9561397140056808825498031)
    ·
      refine ⟨14342095710085213238247047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9561397140056808825498031 14342095710085213238247047)
      ·
        refine ⟨21513143565127819857370571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14342095710085213238247047 21513143565127819857370571)
        ·
          refine ⟨32269715347691729786055857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21513143565127819857370571 32269715347691729786055857)
          ·
            refine ⟨24202286510768797339541893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32269715347691729786055857 24202286510768797339541893)
            ·
              refine ⟨4537928720769149501164105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24202286510768797339541893 4537928720769149501164105)
              ·
                refine ⟨3403446540576862125873079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537928720769149501164105 3403446540576862125873079)
                ·
                  refine ⟨5105169810865293188809619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403446540576862125873079 5105169810865293188809619)
                  ·
                    refine ⟨7657754716297939783214429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5105169810865293188809619 7657754716297939783214429)
                    ·
                      refine ⟨2871658018611727418705411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7657754716297939783214429 2871658018611727418705411)
                      ·
                        rfl

theorem cell23_5592534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_5592534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592534 prefixEnd_5592534 := by exact prefixLift 5592534
  have htrace : WordTrace (prefixWord ++ tailWord_5592534) baseStart_5592534 baseEnd_5592534 := by
    simpa [prefixWord, tailWord_5592534, baseEnd_5592534] using wordTrace_append hprefix tailTrace_5592534
  have hstable : (prefixWord ++ tailWord_5592534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592534).length < 2 ^ (prefixWord ++ tailWord_5592534).sum := by decide
  have hdescent : baseEnd_5592534 < baseStart_5592534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592557 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5592557 : Nat := 118140960795 + 5592557 * 2 ^ 59
def prefixEnd_5592557 : Nat := 4983230072969 + 3 ^ 40 * 5592557 * 2
def baseEnd_5592557 : Nat := 2871669828666780828717805

theorem tailTrace_5592557 : CollatzResearch.WordTrace tailWord_5592557 prefixEnd_5592557 2871669828666780828717805 := by
  unfold tailWord_5592557
  simp only [CollatzResearch.WordTrace]
  refine ⟨203977311200128596538711925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135984874133419064359141283 203977311200128596538711925)
  ·
    refine ⟨19122872925012055925504243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203977311200128596538711925 19122872925012055925504243)
    ·
      refine ⟨28684309387518083888256365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19122872925012055925504243 28684309387518083888256365)
      ·
        refine ⟨10756616020319281458096137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28684309387518083888256365 10756616020319281458096137)
        ·
          refine ⟨8067462015239461093572103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10756616020319281458096137 8067462015239461093572103)
          ·
            refine ⟨12101193022859191640358155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8067462015239461093572103 12101193022859191640358155)
            ·
              refine ⟨18151789534288787460537233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12101193022859191640358155 18151789534288787460537233)
              ·
                refine ⟨13613842150716590595402925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18151789534288787460537233 13613842150716590595402925)
                ·
                  refine ⟨5105190806518721473276097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13613842150716590595402925 5105190806518721473276097)
                  ·
                    refine ⟨3828893104889041104957073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5105190806518721473276097 3828893104889041104957073)
                    ·
                      refine ⟨2871669828666780828717805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3828893104889041104957073 2871669828666780828717805)
                      ·
                        rfl

theorem cell23_5592557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5592557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592557 prefixEnd_5592557 := by exact prefixLift 5592557
  have htrace : WordTrace (prefixWord ++ tailWord_5592557) baseStart_5592557 baseEnd_5592557 := by
    simpa [prefixWord, tailWord_5592557, baseEnd_5592557] using wordTrace_append hprefix tailTrace_5592557
  have hstable : (prefixWord ++ tailWord_5592557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592557).length < 2 ^ (prefixWord ++ tailWord_5592557).sum := by decide
  have hdescent : baseEnd_5592557 < baseStart_5592557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592569 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_5592569 : Nat := 118140960795 + 5592569 * 2 ^ 59
def prefixEnd_5592569 : Nat := 4983230072969 + 3 ^ 40 * 5592569 * 2
def baseEnd_5592569 : Nat := 2871675990434634781767749

theorem tailTrace_5592569 : CollatzResearch.WordTrace tailWord_5592569 prefixEnd_5592569 2871675990434634781767749 := by
  unfold tailWord_5592569
  simp only [CollatzResearch.WordTrace]
  refine ⟨203977748876085122588148761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135985165917390081725432507 203977748876085122588148761)
  ·
    refine ⟨152983311657063841941111571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203977748876085122588148761 152983311657063841941111571)
    ·
      refine ⟨229474967485595762911667357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152983311657063841941111571 229474967485595762911667357)
      ·
        refine ⟨86053112807098411091875259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229474967485595762911667357 86053112807098411091875259)
        ·
          refine ⟨129079669210647616637812889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86053112807098411091875259 129079669210647616637812889)
          ·
            refine ⟨96809751907985712478359667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129079669210647616637812889 96809751907985712478359667)
            ·
              refine ⟨145214627861978568717539501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96809751907985712478359667 145214627861978568717539501)
              ·
                refine ⟨54455485448241963269077313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145214627861978568717539501 54455485448241963269077313)
                ·
                  refine ⟨40841614086181472451807985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54455485448241963269077313 40841614086181472451807985)
                  ·
                    refine ⟨30631210564636104338855989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40841614086181472451807985 30631210564636104338855989)
                    ·
                      refine ⟨2871675990434634781767749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30631210564636104338855989 2871675990434634781767749)
                      ·
                        rfl

theorem cell23_5592569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_5592569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592569 prefixEnd_5592569 := by exact prefixLift 5592569
  have htrace : WordTrace (prefixWord ++ tailWord_5592569) baseStart_5592569 baseEnd_5592569 := by
    simpa [prefixWord, tailWord_5592569, baseEnd_5592569] using wordTrace_append hprefix tailTrace_5592569
  have hstable : (prefixWord ++ tailWord_5592569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592569).length < 2 ^ (prefixWord ++ tailWord_5592569).sum := by decide
  have hdescent : baseEnd_5592569 < baseStart_5592569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592574 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5592574 : Nat := 118140960795 + 5592574 * 2 ^ 59
def prefixEnd_5592574 : Nat := 4983230072969 + 3 ^ 40 * 5592574 * 2
def baseEnd_5592574 : Nat := 2871678557837907262205227

theorem tailTrace_5592574 : CollatzResearch.WordTrace tailWord_5592574 prefixEnd_5592574 2871678557837907262205227 := by
  unfold tailWord_5592574
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497241405133376055260097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135985287494044672294720517 25497241405133376055260097)
  ·
    refine ⟨19122931053850032041445073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25497241405133376055260097 19122931053850032041445073)
    ·
      refine ⟨14342198290387524031083805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19122931053850032041445073 14342198290387524031083805)
      ·
        refine ⟨5378324358895321511656427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14342198290387524031083805 5378324358895321511656427)
        ·
          refine ⟨8067486538342982267484641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378324358895321511656427 8067486538342982267484641)
          ·
            refine ⟨6050614903757236700613481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8067486538342982267484641 6050614903757236700613481)
            ·
              refine ⟨4537961177817927525460111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050614903757236700613481 4537961177817927525460111)
              ·
                refine ⟨6806941766726891288190167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537961177817927525460111 6806941766726891288190167)
                ·
                  refine ⟨10210412650090336932285251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806941766726891288190167 10210412650090336932285251)
                  ·
                    refine ⟨15315618975135505398427877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10210412650090336932285251 15315618975135505398427877)
                    ·
                      refine ⟨2871678557837907262205227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15315618975135505398427877 2871678557837907262205227)
                      ·
                        rfl

theorem cell23_5592574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5592574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592574 prefixEnd_5592574 := by exact prefixLift 5592574
  have htrace : WordTrace (prefixWord ++ tailWord_5592574) baseStart_5592574 baseEnd_5592574 := by
    simpa [prefixWord, tailWord_5592574, baseEnd_5592574] using wordTrace_append hprefix tailTrace_5592574
  have hstable : (prefixWord ++ tailWord_5592574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592574).length < 2 ^ (prefixWord ++ tailWord_5592574).sum := by decide
  have hdescent : baseEnd_5592574 < baseStart_5592574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592577 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_5592577 : Nat := 118140960795 + 5592577 * 2 ^ 59
def prefixEnd_5592577 : Nat := 4983230072969 + 3 ^ 40 * 5592577 * 2
def baseEnd_5592577 : Nat := 2871680098279870750467713

theorem tailTrace_5592577 : CollatzResearch.WordTrace tailWord_5592577 prefixEnd_5592577 2871680098279870750467713 := by
  unfold tailWord_5592577
  simp only [CollatzResearch.WordTrace]
  refine ⟨203978040660056139954439985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135985360440037426636293323 203978040660056139954439985)
  ·
    refine ⟨152983530495042104965829989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203978040660056139954439985 152983530495042104965829989)
    ·
      refine ⟨28684411967820394681093123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152983530495042104965829989 28684411967820394681093123)
      ·
        refine ⟨43026617951730592021639685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28684411967820394681093123 43026617951730592021639685)
        ·
          refine ⟨8067490865949486004057441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43026617951730592021639685 8067490865949486004057441)
          ·
            refine ⟨6050618149462114503043081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8067490865949486004057441 6050618149462114503043081)
            ·
              refine ⟨4537963612096585877282311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050618149462114503043081 4537963612096585877282311)
              ·
                refine ⟨6806945418144878815923467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537963612096585877282311 6806945418144878815923467)
                ·
                  refine ⟨10210418127217318223885201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806945418144878815923467 10210418127217318223885201)
                  ·
                    refine ⟨7657813595412988667913901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10210418127217318223885201 7657813595412988667913901)
                    ·
                      refine ⟨2871680098279870750467713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7657813595412988667913901 2871680098279870750467713)
                      ·
                        rfl

theorem cell23_5592577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_5592577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592577 prefixEnd_5592577 := by exact prefixLift 5592577
  have htrace : WordTrace (prefixWord ++ tailWord_5592577) baseStart_5592577 baseEnd_5592577 := by
    simpa [prefixWord, tailWord_5592577, baseEnd_5592577] using wordTrace_append hprefix tailTrace_5592577
  have hstable : (prefixWord ++ tailWord_5592577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592577).length < 2 ^ (prefixWord ++ tailWord_5592577).sum := by decide
  have hdescent : baseEnd_5592577 < baseStart_5592577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592579 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4]
def baseStart_5592579 : Nat := 118140960795 + 5592579 * 2 ^ 59
def prefixEnd_5592579 : Nat := 4983230072969 + 3 ^ 40 * 5592579 * 2
def baseEnd_5592579 : Nat := 2871681125241179742642703

theorem tailTrace_5592579 : CollatzResearch.WordTrace tailWord_5592579 prefixEnd_5592579 2871681125241179742642703 := by
  unfold tailWord_5592579
  simp only [CollatzResearch.WordTrace]
  refine ⟨203978113606048894296012791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135985409070699262864008527 203978113606048894296012791)
  ·
    refine ⟨305967170409073341444019187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203978113606048894296012791 305967170409073341444019187)
    ·
      refine ⟨458950755613610012166028781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305967170409073341444019187 458950755613610012166028781)
      ·
        refine ⟨172106533355103754562260793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458950755613610012166028781 172106533355103754562260793)
        ·
          refine ⟨129079900016327815921695595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172106533355103754562260793 129079900016327815921695595)
          ·
            refine ⟨193619850024491723882543393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129079900016327815921695595 193619850024491723882543393)
            ·
              refine ⟨145214887518368792911907545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193619850024491723882543393 145214887518368792911907545)
              ·
                refine ⟨108911165638776594683930659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145214887518368792911907545 108911165638776594683930659)
                ·
                  refine ⟨163366748458164892025895989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108911165638776594683930659 163366748458164892025895989)
                  ·
                    refine ⟨15315632667952958627427749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163366748458164892025895989 15315632667952958627427749)
                    ·
                      refine ⟨2871681125241179742642703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15315632667952958627427749 2871681125241179742642703)
                      ·
                        rfl

theorem cell23_5592579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_5592579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592579 prefixEnd_5592579 := by exact prefixLift 5592579
  have htrace : WordTrace (prefixWord ++ tailWord_5592579) baseStart_5592579 baseEnd_5592579 := by
    simpa [prefixWord, tailWord_5592579, baseEnd_5592579] using wordTrace_append hprefix tailTrace_5592579
  have hstable : (prefixWord ++ tailWord_5592579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592579).length < 2 ^ (prefixWord ++ tailWord_5592579).sum := by decide
  have hdescent : baseEnd_5592579 < baseStart_5592579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592590 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5592590 : Nat := 118140960795 + 5592590 * 2 ^ 59
def prefixEnd_5592590 : Nat := 4983230072969 + 3 ^ 40 * 5592590 * 2
def baseEnd_5592590 : Nat := 2871686773528379199605153

theorem tailTrace_5592590 : CollatzResearch.WordTrace tailWord_5592590 prefixEnd_5592590 2871686773528379199605153 := by
  unfold tailWord_5592590
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497314351126130396832903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135985676539339362116442149 25497314351126130396832903)
  ·
    refine ⟨38245971526689195595249355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25497314351126130396832903 38245971526689195595249355)
    ·
      refine ⟨57368957290033793392874033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38245971526689195595249355 57368957290033793392874033)
      ·
        refine ⟨43026717967525345044655525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57368957290033793392874033 43026717967525345044655525)
        ·
          refine ⟨8067509618911002195872911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43026717967525345044655525 8067509618911002195872911)
          ·
            refine ⟨12101264428366503293809367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8067509618911002195872911 12101264428366503293809367)
            ·
              refine ⟨18151896642549754940714051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12101264428366503293809367 18151896642549754940714051)
              ·
                refine ⟨27227844963824632411071077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18151896642549754940714051 27227844963824632411071077)
                ·
                  refine ⟨5105220930717118577075827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27227844963824632411071077 5105220930717118577075827)
                  ·
                    refine ⟨7657831396075677865613741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5105220930717118577075827 7657831396075677865613741)
                    ·
                      refine ⟨2871686773528379199605153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7657831396075677865613741 2871686773528379199605153)
                      ·
                        rfl

theorem cell23_5592590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5592590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592590 prefixEnd_5592590 := by exact prefixLift 5592590
  have htrace : WordTrace (prefixWord ++ tailWord_5592590) baseStart_5592590 baseEnd_5592590 := by
    simpa [prefixWord, tailWord_5592590, baseEnd_5592590] using wordTrace_append hprefix tailTrace_5592590
  have hstable : (prefixWord ++ tailWord_5592590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592590).length < 2 ^ (prefixWord ++ tailWord_5592590).sum := by decide
  have hdescent : baseEnd_5592590 < baseStart_5592590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592693 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5592693 : Nat := 118140960795 + 5592693 * 2 ^ 59
def prefixEnd_5592693 : Nat := 4983230072969 + 3 ^ 40 * 5592693 * 2
def baseEnd_5592693 : Nat := 2871739662035792296617179

theorem tailTrace_5592693 : CollatzResearch.WordTrace tailWord_5592693 prefixEnd_5592693 2871739662035792296617179 := by
  unfold tailWord_5592693
  simp only [CollatzResearch.WordTrace]
  refine ⟨203982271527635891765662733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135988181018423927843775155 203982271527635891765662733)
  ·
    refine ⟨76493351822863459412123525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203982271527635891765662733 76493351822863459412123525)
    ·
      refine ⟨14342503466786898639773161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76493351822863459412123525 14342503466786898639773161)
      ·
        refine ⟨10756877600090173979829871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14342503466786898639773161 10756877600090173979829871)
        ·
          refine ⟨16135316400135260969744807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10756877600090173979829871 16135316400135260969744807)
          ·
            refine ⟨24202974600202891454617211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16135316400135260969744807 24202974600202891454617211)
            ·
              refine ⟨36304461900304337181925817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24202974600202891454617211 36304461900304337181925817)
              ·
                refine ⟨27228346425228252886444363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36304461900304337181925817 27228346425228252886444363)
                ·
                  refine ⟨40842519637842379329666545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27228346425228252886444363 40842519637842379329666545)
                  ·
                    refine ⟨30631889728381784497249909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40842519637842379329666545 30631889728381784497249909)
                    ·
                      refine ⟨2871739662035792296617179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30631889728381784497249909 2871739662035792296617179)
                      ·
                        rfl

theorem cell23_5592693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5592693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592693 prefixEnd_5592693 := by exact prefixLift 5592693
  have htrace : WordTrace (prefixWord ++ tailWord_5592693) baseStart_5592693 baseEnd_5592693 := by
    simpa [prefixWord, tailWord_5592693, baseEnd_5592693] using wordTrace_append hprefix tailTrace_5592693
  have hstable : (prefixWord ++ tailWord_5592693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592693).length < 2 ^ (prefixWord ++ tailWord_5592693).sum := by decide
  have hdescent : baseEnd_5592693 < baseStart_5592693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592740 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_5592740 : Nat := 118140960795 + 5592740 * 2 ^ 59
def prefixEnd_5592740 : Nat := 4983230072969 + 3 ^ 40 * 5592740 * 2
def baseEnd_5592740 : Nat := 2871763795626553612729463

theorem tailTrace_5592740 : CollatzResearch.WordTrace tailWord_5592740 prefixEnd_5592740 2871763795626553612729463 := by
  unfold tailWord_5592740
  simp only [CollatzResearch.WordTrace]
  refine ⟨101991992879232809396311837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135989323838977079195082449 101991992879232809396311837)
  ·
    refine ⟨38246997329712303523616939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101991992879232809396311837 38246997329712303523616939)
    ·
      refine ⟨57370495994568455285425409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38246997329712303523616939 57370495994568455285425409)
      ·
        refine ⟨43027871995926341464069057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57370495994568455285425409 43027871995926341464069057)
        ·
          refine ⟨32270903996944756098051793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43027871995926341464069057 32270903996944756098051793)
          ·
            refine ⟨24203177997708567073538845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32270903996944756098051793 24203177997708567073538845)
            ·
              refine ⟨9076191749140712652577067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24203177997708567073538845 9076191749140712652577067)
              ·
                refine ⟨13614287623711068978865601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076191749140712652577067 13614287623711068978865601)
                ·
                  refine ⟨10210715717783301734149201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13614287623711068978865601 10210715717783301734149201)
                  ·
                    refine ⟨7658036788337476300611901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10210715717783301734149201 7658036788337476300611901)
                    ·
                      refine ⟨2871763795626553612729463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7658036788337476300611901 2871763795626553612729463)
                      ·
                        rfl

theorem cell23_5592740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_5592740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592740 prefixEnd_5592740 := by exact prefixLift 5592740
  have htrace : WordTrace (prefixWord ++ tailWord_5592740) baseStart_5592740 baseEnd_5592740 := by
    simpa [prefixWord, tailWord_5592740, baseEnd_5592740] using wordTrace_append hprefix tailTrace_5592740
  have hstable : (prefixWord ++ tailWord_5592740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592740).length < 2 ^ (prefixWord ++ tailWord_5592740).sum := by decide
  have hdescent : baseEnd_5592740 < baseStart_5592740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592810 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_5592810 : Nat := 118140960795 + 5592810 * 2 ^ 59
def prefixEnd_5592810 : Nat := 4983230072969 + 3 ^ 40 * 5592810 * 2
def baseEnd_5592810 : Nat := 2871799739272368338854141

theorem tailTrace_5592810 : CollatzResearch.WordTrace tailWord_5592810 prefixEnd_5592810 2871799739272368338854141 := by
  unfold tailWord_5592810
  simp only [CollatzResearch.WordTrace]
  refine ⟨50996634717053005186917971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135991025912141347165114589 50996634717053005186917971)
  ·
    refine ⟨76494952075579507780376957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50996634717053005186917971 76494952075579507780376957)
    ·
      refine ⟨28685607028342315417641359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76494952075579507780376957 28685607028342315417641359)
      ·
        refine ⟨43028410542513473126462039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28685607028342315417641359 43028410542513473126462039)
        ·
          refine ⟨64542615813770209689693059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43028410542513473126462039 64542615813770209689693059)
          ·
            refine ⟨96813923720655314534539589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64542615813770209689693059 96813923720655314534539589)
            ·
              refine ⟨18152610697622871475226173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96813923720655314534539589 18152610697622871475226173)
              ·
                refine ⟨6807229011608576803209815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18152610697622871475226173 6807229011608576803209815)
                ·
                  refine ⟨10210843517412865204814723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6807229011608576803209815 10210843517412865204814723)
                  ·
                    refine ⟨15316265276119297807222085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10210843517412865204814723 15316265276119297807222085)
                    ·
                      refine ⟨2871799739272368338854141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15316265276119297807222085 2871799739272368338854141)
                      ·
                        rfl

theorem cell23_5592810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_5592810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592810 prefixEnd_5592810 := by exact prefixLift 5592810
  have htrace : WordTrace (prefixWord ++ tailWord_5592810) baseStart_5592810 baseEnd_5592810 := by
    simpa [prefixWord, tailWord_5592810, baseEnd_5592810] using wordTrace_append hprefix tailTrace_5592810
  have hstable : (prefixWord ++ tailWord_5592810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592810).length < 2 ^ (prefixWord ++ tailWord_5592810).sum := by decide
  have hdescent : baseEnd_5592810 < baseStart_5592810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592850 : List Nat := [3, 2, 4, 1, 1, 1, 2, 9]
def baseStart_5592850 : Nat := 118140960795 + 5592850 * 2 ^ 59
def prefixEnd_5592850 : Nat := 4983230072969 + 3 ^ 40 * 5592850 * 2
def baseEnd_5592850 : Nat := 106363714018464747494591

theorem tailTrace_5592850 : CollatzResearch.WordTrace tailWord_5592850 prefixEnd_5592850 106363714018464747494591 := by
  unfold tailWord_5592850
  simp only [CollatzResearch.WordTrace]
  refine ⟨50996999447016776894782001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135991998525378071719418669 50996999447016776894782001)
  ·
    refine ⟨38247749585262582671086501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50996999447016776894782001 38247749585262582671086501)
    ·
      refine ⟨7171453047236734250828719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38247749585262582671086501 7171453047236734250828719)
      ·
        refine ⟨10757179570855101376243079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7171453047236734250828719 10757179570855101376243079)
        ·
          refine ⟨16135769356282652064364619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10757179570855101376243079 16135769356282652064364619)
          ·
            refine ⟨24203654034423978096546929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16135769356282652064364619 24203654034423978096546929)
            ·
              refine ⟨18152740525817983572410197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24203654034423978096546929 18152740525817983572410197)
              ·
                refine ⟨106363714018464747494591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18152740525817983572410197 106363714018464747494591)
                ·
                  rfl

theorem cell23_5592850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_5592850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592850 prefixEnd_5592850 := by exact prefixLift 5592850
  have htrace : WordTrace (prefixWord ++ tailWord_5592850) baseStart_5592850 baseEnd_5592850 := by
    simpa [prefixWord, tailWord_5592850, baseEnd_5592850] using wordTrace_append hprefix tailTrace_5592850
  have hstable : (prefixWord ++ tailWord_5592850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592850).length < 2 ^ (prefixWord ++ tailWord_5592850).sum := by decide
  have hdescent : baseEnd_5592850 < baseStart_5592850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592860 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_5592860 : Nat := 118140960795 + 5592860 * 2 ^ 59
def prefixEnd_5592860 : Nat := 4983230072969 + 3 ^ 40 * 5592860 * 2
def baseEnd_5592860 : Nat := 2871825413305093143228911

theorem tailTrace_5592860 : CollatzResearch.WordTrace tailWord_5592860 prefixEnd_5592860 2871825413305093143228911 := by
  unfold tailWord_5592860
  simp only [CollatzResearch.WordTrace]
  refine ⟨101994181259015439643496017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135992241678687252857994689 101994181259015439643496017)
  ·
    refine ⟨76495635944261579732622013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101994181259015439643496017 76495635944261579732622013)
    ·
      refine ⟨28685863479098092399733255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76495635944261579732622013 28685863479098092399733255)
      ·
        refine ⟨43028795218647138599599883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28685863479098092399733255 43028795218647138599599883)
        ·
          refine ⟨64543192827970707899399825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43028795218647138599599883 64543192827970707899399825)
          ·
            refine ⟨48407394620978030924549869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64543192827970707899399825 48407394620978030924549869)
            ·
              refine ⟨18152772982866761596706201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48407394620978030924549869 18152772982866761596706201)
              ·
                refine ⟨13614579737150071197529651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18152772982866761596706201 13614579737150071197529651)
                ·
                  refine ⟨20421869605725106796294477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13614579737150071197529651 20421869605725106796294477)
                  ·
                    refine ⟨7658201102146915048610429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20421869605725106796294477 7658201102146915048610429)
                    ·
                      refine ⟨2871825413305093143228911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7658201102146915048610429 2871825413305093143228911)
                      ·
                        rfl

theorem cell23_5592860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_5592860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592860 prefixEnd_5592860 := by exact prefixLift 5592860
  have htrace : WordTrace (prefixWord ++ tailWord_5592860) baseStart_5592860 baseEnd_5592860 := by
    simpa [prefixWord, tailWord_5592860, baseEnd_5592860] using wordTrace_append hprefix tailTrace_5592860
  have hstable : (prefixWord ++ tailWord_5592860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592860).length < 2 ^ (prefixWord ++ tailWord_5592860).sum := by decide
  have hdescent : baseEnd_5592860 < baseStart_5592860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592878 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5592878 : Nat := 118140960795 + 5592878 * 2 ^ 59
def prefixEnd_5592878 : Nat := 4983230072969 + 3 ^ 40 * 5592878 * 2
def baseEnd_5592878 : Nat := 2871834655956874072803829

theorem tailTrace_5592878 : CollatzResearch.WordTrace tailWord_5592878 prefixEnd_5592878 2871834655956874072803829 := by
  unfold tailWord_5592878
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498627378995708545143411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135992679354643778907431525 25498627378995708545143411)
  ·
    refine ⟨38247941068493562817715117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25498627378995708545143411 38247941068493562817715117)
    ·
      refine ⟨14342977900685086056643169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38247941068493562817715117 14342977900685086056643169)
      ·
        refine ⟨10757233425513814542482377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14342977900685086056643169 10757233425513814542482377)
        ·
          refine ⟨8067925069135360906861783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10757233425513814542482377 8067925069135360906861783)
          ·
            refine ⟨12101887603703041360292675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8067925069135360906861783 12101887603703041360292675)
            ·
              refine ⟨18152831405554562040439013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12101887603703041360292675 18152831405554562040439013)
              ·
                refine ⟨3403655888541480382582315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18152831405554562040439013 3403655888541480382582315)
                ·
                  refine ⟨5105483832812220573873473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403655888541480382582315 5105483832812220573873473)
                  ·
                    refine ⟨3829112874609165430405105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5105483832812220573873473 3829112874609165430405105)
                    ·
                      refine ⟨2871834655956874072803829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829112874609165430405105 2871834655956874072803829)
                      ·
                        rfl

theorem cell23_5592878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5592878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592878 prefixEnd_5592878 := by exact prefixLift 5592878
  have htrace : WordTrace (prefixWord ++ tailWord_5592878) baseStart_5592878 baseEnd_5592878 := by
    simpa [prefixWord, tailWord_5592878, baseEnd_5592878] using wordTrace_append hprefix tailTrace_5592878
  have hstable : (prefixWord ++ tailWord_5592878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592878).length < 2 ^ (prefixWord ++ tailWord_5592878).sum := by decide
  have hdescent : baseEnd_5592878 < baseStart_5592878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592894 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_5592894 : Nat := 118140960795 + 5592894 * 2 ^ 59
def prefixEnd_5592894 : Nat := 4983230072969 + 3 ^ 40 * 5592894 * 2
def baseEnd_5592894 : Nat := 2871842871647346010203755

theorem tailTrace_5592894 : CollatzResearch.WordTrace tailWord_5592894 prefixEnd_5592894 2871842871647346010203755 := by
  unfold tailWord_5592894
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498700324988462886716217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135993068399938468729153157 25498700324988462886716217)
  ·
    refine ⟨19124025243741347165037163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25498700324988462886716217 19124025243741347165037163)
    ·
      refine ⟨28686037865612020747555745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19124025243741347165037163 28686037865612020747555745)
      ·
        refine ⟨21514528399209015560666809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28686037865612020747555745 21514528399209015560666809)
        ·
          refine ⟨16135896299406761670500107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21514528399209015560666809 16135896299406761670500107)
          ·
            refine ⟨24203844449110142505750161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16135896299406761670500107 24203844449110142505750161)
            ·
              refine ⟨18152883336832606879312621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24203844449110142505750161 18152883336832606879312621)
              ·
                refine ⟨6807331251312227579742233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18152883336832606879312621 6807331251312227579742233)
                ·
                  refine ⟨5105498438484170684806675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6807331251312227579742233 5105498438484170684806675)
                  ·
                    refine ⟨7658247657726256027210013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5105498438484170684806675 7658247657726256027210013)
                    ·
                      refine ⟨2871842871647346010203755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7658247657726256027210013 2871842871647346010203755)
                      ·
                        rfl

theorem cell23_5592894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_5592894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592894 prefixEnd_5592894 := by exact prefixLift 5592894
  have htrace : WordTrace (prefixWord ++ tailWord_5592894) baseStart_5592894 baseEnd_5592894 := by
    simpa [prefixWord, tailWord_5592894, baseEnd_5592894] using wordTrace_append hprefix tailTrace_5592894
  have hstable : (prefixWord ++ tailWord_5592894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592894).length < 2 ^ (prefixWord ++ tailWord_5592894).sum := by decide
  have hdescent : baseEnd_5592894 < baseStart_5592894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592903 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_5592903 : Nat := 118140960795 + 5592903 * 2 ^ 59
def prefixEnd_5592903 : Nat := 4983230072969 + 3 ^ 40 * 5592903 * 2
def baseEnd_5592903 : Nat := 2871847492973236474991213

theorem tailTrace_5592903 : CollatzResearch.WordTrace tailWord_5592903 prefixEnd_5592903 2871847492973236474991213 := by
  unfold tailWord_5592903
  simp only [CollatzResearch.WordTrace]
  refine ⟨203989930856875097630807363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135993287237916731753871575 203989930856875097630807363)
  ·
    refine ⟨305984896285312646446211045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203989930856875097630807363 305984896285312646446211045)
    ·
      refine ⟨57372168053496121208664571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305984896285312646446211045 57372168053496121208664571)
      ·
        refine ⟨86058252080244181812996857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57372168053496121208664571 86058252080244181812996857)
        ·
          refine ⟨64543689060183136359747643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86058252080244181812996857 64543689060183136359747643)
          ·
            refine ⟨96815533590274704539621465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64543689060183136359747643 96815533590274704539621465)
            ·
              refine ⟨72611650192706028404716099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96815533590274704539621465 72611650192706028404716099)
              ·
                refine ⟨108917475289059042607074149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72611650192706028404716099 108917475289059042607074149)
                ·
                  refine ⟨20422026616698570488826403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108917475289059042607074149 20422026616698570488826403)
                  ·
                    refine ⟨30633039925047855733239605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20422026616698570488826403 30633039925047855733239605)
                    ·
                      refine ⟨2871847492973236474991213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30633039925047855733239605 2871847492973236474991213)
                      ·
                        rfl

theorem cell23_5592903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_5592903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592903 prefixEnd_5592903 := by exact prefixLift 5592903
  have htrace : WordTrace (prefixWord ++ tailWord_5592903) baseStart_5592903 baseEnd_5592903 := by
    simpa [prefixWord, tailWord_5592903, baseEnd_5592903] using wordTrace_append hprefix tailTrace_5592903
  have hstable : (prefixWord ++ tailWord_5592903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592903).length < 2 ^ (prefixWord ++ tailWord_5592903).sum := by decide
  have hdescent : baseEnd_5592903 < baseStart_5592903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592917 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_5592917 : Nat := 118140960795 + 5592917 * 2 ^ 59
def prefixEnd_5592917 : Nat := 4983230072969 + 3 ^ 40 * 5592917 * 2
def baseEnd_5592917 : Nat := 2871854681702399420216149

theorem tailTrace_5592917 : CollatzResearch.WordTrace tailWord_5592917 prefixEnd_5592917 2871854681702399420216149 := by
  unfold tailWord_5592917
  simp only [CollatzResearch.WordTrace]
  refine ⟨203990441478824378021817005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135993627652549585347878003 203990441478824378021817005)
  ·
    refine ⟨76496415554559141758181377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203990441478824378021817005 76496415554559141758181377)
    ·
      refine ⟨57372311665919356318636033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76496415554559141758181377 57372311665919356318636033)
      ·
        refine ⟨43029233749439517238977025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57372311665919356318636033 43029233749439517238977025)
        ·
          refine ⟨32271925312079637929232769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43029233749439517238977025 32271925312079637929232769)
          ·
            refine ⟨24203943984059728446924577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32271925312079637929232769 24203943984059728446924577)
            ·
              refine ⟨18152957988044796335193433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24203943984059728446924577 18152957988044796335193433)
              ·
                refine ⟨13614718491033597251395075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18152957988044796335193433 13614718491033597251395075)
                ·
                  refine ⟨20422077736550395877092613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13614718491033597251395075 20422077736550395877092613)
                  ·
                    refine ⟨3829139575603199226954865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20422077736550395877092613 3829139575603199226954865)
                    ·
                      refine ⟨2871854681702399420216149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829139575603199226954865 2871854681702399420216149)
                      ·
                        rfl

theorem cell23_5592917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_5592917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592917 prefixEnd_5592917 := by exact prefixLift 5592917
  have htrace : WordTrace (prefixWord ++ tailWord_5592917) baseStart_5592917 baseEnd_5592917 := by
    simpa [prefixWord, tailWord_5592917, baseEnd_5592917] using wordTrace_append hprefix tailTrace_5592917
  have hstable : (prefixWord ++ tailWord_5592917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592917).length < 2 ^ (prefixWord ++ tailWord_5592917).sum := by decide
  have hdescent : baseEnd_5592917 < baseStart_5592917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592940 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 7]
def baseStart_5592940 : Nat := 118140960795 + 5592940 * 2 ^ 59
def prefixEnd_5592940 : Nat := 4983230072969 + 3 ^ 40 * 5592940 * 2
def baseEnd_5592940 : Nat := 319096276861939203358727

theorem tailTrace_5592940 : CollatzResearch.WordTrace tailWord_5592940 prefixEnd_5592940 319096276861939203358727 := by
  unfold tailWord_5592940
  simp only [CollatzResearch.WordTrace]
  refine ⟨101995640178870526474952137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135994186905160701966602849 101995640178870526474952137)
  ·
    refine ⟨76496730134152894856214103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101995640178870526474952137 76496730134152894856214103)
    ·
      refine ⟨114745095201229342284321155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76496730134152894856214103 114745095201229342284321155)
      ·
        refine ⟨172117642801844013426481733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114745095201229342284321155 172117642801844013426481733)
        ·
          refine ⟨32272058025345752517465325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172117642801844013426481733 32272058025345752517465325)
          ·
            refine ⟨12102021759504657194049497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32272058025345752517465325 12102021759504657194049497)
            ·
              refine ⟨9076516319628492895537123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12102021759504657194049497 9076516319628492895537123)
              ·
                refine ⟨13614774479442739343305685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076516319628492895537123 13614774479442739343305685)
                ·
                  refine ⟨319096276861939203358727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13614774479442739343305685 319096276861939203358727)
                  ·
                    rfl

theorem cell23_5592940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_5592940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592940 prefixEnd_5592940 := by exact prefixLift 5592940
  have htrace : WordTrace (prefixWord ++ tailWord_5592940) baseStart_5592940 baseEnd_5592940 := by
    simpa [prefixWord, tailWord_5592940, baseEnd_5592940] using wordTrace_append hprefix tailTrace_5592940
  have hstable : (prefixWord ++ tailWord_5592940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592940).length < 2 ^ (prefixWord ++ tailWord_5592940).sum := by decide
  have hdescent : baseEnd_5592940 < baseStart_5592940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5592953 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_5592953 : Nat := 118140960795 + 5592953 * 2 ^ 59
def prefixEnd_5592953 : Nat := 4983230072969 + 3 ^ 40 * 5592953 * 2
def baseEnd_5592953 : Nat := 957291055668653759788661

theorem tailTrace_5592953 : CollatzResearch.WordTrace tailWord_5592953 prefixEnd_5592953 957291055668653759788661 := by
  unfold tailWord_5592953
  simp only [CollatzResearch.WordTrace]
  refine ⟨203991754506693956170127513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135994503004462637446751675 203991754506693956170127513)
  ·
    refine ⟨152993815880020467127595635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203991754506693956170127513 152993815880020467127595635)
    ·
      refine ⟨229490723820030700691393453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152993815880020467127595635 229490723820030700691393453)
      ·
        refine ⟨86059021432511512759272545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229490723820030700691393453 86059021432511512759272545)
        ·
          refine ⟨64544266074383634569454409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86059021432511512759272545 64544266074383634569454409)
          ·
            refine ⟨48408199555787725927090807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64544266074383634569454409 48408199555787725927090807)
            ·
              refine ⟨72612299333681588890636211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48408199555787725927090807 72612299333681588890636211)
              ·
                refine ⟨108918449000522383335954317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72612299333681588890636211 108918449000522383335954317)
                ·
                  refine ⟨40844418375195893750982869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108918449000522383335954317 40844418375195893750982869)
                  ·
                    refine ⟨957291055668653759788661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40844418375195893750982869 957291055668653759788661)
                    ·
                      rfl

theorem cell23_5592953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_5592953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5592953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5592953 prefixEnd_5592953 := by exact prefixLift 5592953
  have htrace : WordTrace (prefixWord ++ tailWord_5592953) baseStart_5592953 baseEnd_5592953 := by
    simpa [prefixWord, tailWord_5592953, baseEnd_5592953] using wordTrace_append hprefix tailTrace_5592953
  have hstable : (prefixWord ++ tailWord_5592953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5592953).length < 2 ^ (prefixWord ++ tailWord_5592953).sum := by decide
  have hdescent : baseEnd_5592953 < baseStart_5592953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5592953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593010 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_5593010 : Nat := 118140960795 + 5593010 * 2 ^ 59
def prefixEnd_5593010 : Nat := 4983230072969 + 3 ^ 40 * 5593010 * 2
def baseEnd_5593010 : Nat := 2871902435403267556353221

theorem tailTrace_5593010 : CollatzResearch.WordTrace tailWord_5593010 prefixEnd_5593010 2871902435403267556353221 := by
  unfold tailWord_5593010
  simp only [CollatzResearch.WordTrace]
  refine ⟨50998458366871863726238121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135995888978324969936634989 50998458366871863726238121)
  ·
    refine ⟨38248843775153897794678591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50998458366871863726238121 38248843775153897794678591)
    ·
      refine ⟨57373265662730846692017887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38248843775153897794678591 57373265662730846692017887)
      ·
        refine ⟨86059898494096270038026831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57373265662730846692017887 86059898494096270038026831)
        ·
          refine ⟨129089847741144405057040247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86059898494096270038026831 129089847741144405057040247)
          ·
            refine ⟨193634771611716607585560371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129089847741144405057040247 193634771611716607585560371)
            ·
              refine ⟨290452157417574911378340557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193634771611716607585560371 290452157417574911378340557)
              ·
                refine ⟨108919559031590591766877709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290452157417574911378340557 108919559031590591766877709)
                ·
                  refine ⟨40844834636846471912579141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108919559031590591766877709 40844834636846471912579141)
                  ·
                    refine ⟨7658406494408713483608589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40844834636846471912579141 7658406494408713483608589)
                    ·
                      refine ⟨2871902435403267556353221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7658406494408713483608589 2871902435403267556353221)
                      ·
                        rfl

theorem cell23_5593010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_5593010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593010 prefixEnd_5593010 := by exact prefixLift 5593010
  have htrace : WordTrace (prefixWord ++ tailWord_5593010) baseStart_5593010 baseEnd_5593010 := by
    simpa [prefixWord, tailWord_5593010, baseEnd_5593010] using wordTrace_append hprefix tailTrace_5593010
  have hstable : (prefixWord ++ tailWord_5593010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593010).length < 2 ^ (prefixWord ++ tailWord_5593010).sum := by decide
  have hdescent : baseEnd_5593010 < baseStart_5593010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593060 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_5593060 : Nat := 118140960795 + 5593060 * 2 ^ 59
def prefixEnd_5593060 : Nat := 4983230072969 + 3 ^ 40 * 5593060 * 2
def baseEnd_5593060 : Nat := 957309369811997453575997

theorem tailTrace_5593060 : CollatzResearch.WordTrace tailWord_5593060 prefixEnd_5593060 957309369811997453575997 := by
  unfold tailWord_5593060
  simp only [CollatzResearch.WordTrace]
  refine ⟨101997828558653156722136317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135997104744870875629515089 101997828558653156722136317)
  ·
    refine ⟨38249185709494933770801119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101997828558653156722136317 38249185709494933770801119)
    ·
      refine ⟨57373778564242400656201679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38249185709494933770801119 57373778564242400656201679)
      ·
        refine ⟨86060667846363600984302519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57373778564242400656201679 86060667846363600984302519)
        ·
          refine ⟨129091001769545401476453779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86060667846363600984302519 129091001769545401476453779)
          ·
            refine ⟨193636502654318102214680669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129091001769545401476453779 193636502654318102214680669)
            ·
              refine ⟨72613688495369288330505251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193636502654318102214680669 72613688495369288330505251)
              ·
                refine ⟨108920532743053932495757877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72613688495369288330505251 108920532743053932495757877)
                ·
                  refine ⟨10211299944661306171477301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108920532743053932495757877 10211299944661306171477301)
                  ·
                    refine ⟨957309369811997453575997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10211299944661306171477301 957309369811997453575997)
                    ·
                      rfl

theorem cell23_5593060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_5593060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593060 prefixEnd_5593060 := by exact prefixLift 5593060
  have htrace : WordTrace (prefixWord ++ tailWord_5593060) baseStart_5593060 baseEnd_5593060 := by
    simpa [prefixWord, tailWord_5593060, baseEnd_5593060] using wordTrace_append hprefix tailTrace_5593060
  have hstable : (prefixWord ++ tailWord_5593060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593060).length < 2 ^ (prefixWord ++ tailWord_5593060).sum := by decide
  have hdescent : baseEnd_5593060 < baseStart_5593060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593067 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 4, 3, 2]
def baseStart_5593067 : Nat := 118140960795 + 5593067 * 2 ^ 59
def prefixEnd_5593067 : Nat := 4983230072969 + 3 ^ 40 * 5593067 * 2
def baseEnd_5593067 : Nat := 2871931703800573833340459

theorem tailTrace_5593067 : CollatzResearch.WordTrace tailWord_5593067 prefixEnd_5593067 2871931703800573833340459 := by
  unfold tailWord_5593067
  simp only [CollatzResearch.WordTrace]
  refine ⟨203995912428280953639777455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135997274952187302426518303 203995912428280953639777455)
  ·
    refine ⟨305993868642421430459666183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203995912428280953639777455 305993868642421430459666183)
    ·
      refine ⟨458990802963632145689499275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305993868642421430459666183 458990802963632145689499275)
      ·
        refine ⟨688486204445448218534248913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458990802963632145689499275 688486204445448218534248913)
        ·
          refine ⟨516364653334086163900686685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688486204445448218534248913 516364653334086163900686685)
          ·
            refine ⟨193636745000282311462757507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516364653334086163900686685 193636745000282311462757507)
            ·
              refine ⟨290455117500423467194136261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193636745000282311462757507 290455117500423467194136261)
              ·
                refine ⟨54460334531329400098900549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290455117500423467194136261 54460334531329400098900549)
                ·
                  refine ⟨10211312724624262518543853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54460334531329400098900549 10211312724624262518543853)
                  ·
                    refine ⟨3829242271734098444453945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10211312724624262518543853 3829242271734098444453945)
                    ·
                      refine ⟨2871931703800573833340459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829242271734098444453945 2871931703800573833340459)
                      ·
                        rfl

theorem cell23_5593067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3, 2].length) (baseStart_5593067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593067 prefixEnd_5593067 := by exact prefixLift 5593067
  have htrace : WordTrace (prefixWord ++ tailWord_5593067) baseStart_5593067 baseEnd_5593067 := by
    simpa [prefixWord, tailWord_5593067, baseEnd_5593067] using wordTrace_append hprefix tailTrace_5593067
  have hstable : (prefixWord ++ tailWord_5593067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593067).length < 2 ^ (prefixWord ++ tailWord_5593067).sum := by decide
  have hdescent : baseEnd_5593067 < baseStart_5593067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593078 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5593078 : Nat := 118140960795 + 5593078 * 2 ^ 59
def prefixEnd_5593078 : Nat := 4983230072969 + 3 ^ 40 * 5593078 * 2
def baseEnd_5593078 : Nat := 2871937352087773290302909

theorem tailTrace_5593078 : CollatzResearch.WordTrace tailWord_5593078 prefixEnd_5593078 2871937352087773290302909 := by
  unfold tailWord_5593078
  simp only [CollatzResearch.WordTrace]
  refine ⟨12749769601952568907401743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135997542420827401678951925 12749769601952568907401743)
  ·
    refine ⟨19124654402928853361102615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12749769601952568907401743 19124654402928853361102615)
    ·
      refine ⟨28686981604393280041653923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19124654402928853361102615 28686981604393280041653923)
      ·
        refine ⟨43030472406589920062480885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28686981604393280041653923 43030472406589920062480885)
        ·
          refine ⟨4034106788117805005857583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43030472406589920062480885 4034106788117805005857583)
          ·
            refine ⟨6051160182176707508786375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034106788117805005857583 6051160182176707508786375)
            ·
              refine ⟨9076740273265061263179563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051160182176707508786375 9076740273265061263179563)
              ·
                refine ⟨13615110409897591894769345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076740273265061263179563 13615110409897591894769345)
                ·
                  refine ⟨10211332807423193921077009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13615110409897591894769345 10211332807423193921077009)
                  ·
                    refine ⟨7658499605567395440807757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10211332807423193921077009 7658499605567395440807757)
                    ·
                      refine ⟨2871937352087773290302909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7658499605567395440807757 2871937352087773290302909)
                      ·
                        rfl

theorem cell23_5593078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5593078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593078 prefixEnd_5593078 := by exact prefixLift 5593078
  have htrace : WordTrace (prefixWord ++ tailWord_5593078) baseStart_5593078 baseEnd_5593078 := by
    simpa [prefixWord, tailWord_5593078, baseEnd_5593078] using wordTrace_append hprefix tailTrace_5593078
  have hstable : (prefixWord ++ tailWord_5593078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593078).length < 2 ^ (prefixWord ++ tailWord_5593078).sum := by decide
  have hdescent : baseEnd_5593078 < baseStart_5593078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593117 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5593117 : Nat := 118140960795 + 5593117 * 2 ^ 59
def prefixEnd_5593117 : Nat := 4983230072969 + 3 ^ 40 * 5593117 * 2
def baseEnd_5593117 : Nat := 2871957377833298637715229

theorem tailTrace_5593117 : CollatzResearch.WordTrace tailWord_5593117 prefixEnd_5593117 2871957377833298637715229 := by
  unfold tailWord_5593117
  simp only [CollatzResearch.WordTrace]
  refine ⟨203997736078099812179097605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135998490718733208119398403 203997736078099812179097605)
  ·
    refine ⟨38249575514643714783580801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203997736078099812179097605 38249575514643714783580801)
    ·
      refine ⟨28687181635982786087685601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38249575514643714783580801 28687181635982786087685601)
      ·
        refine ⟨21515386226987089565764201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28687181635982786087685601 21515386226987089565764201)
        ·
          refine ⟨16136539670240317174323151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21515386226987089565764201 16136539670240317174323151)
          ·
            refine ⟨24204809505360475761484727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16136539670240317174323151 24204809505360475761484727)
            ·
              refine ⟨36307214258040713642227091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24204809505360475761484727 36307214258040713642227091)
              ·
                refine ⟨54460821387061070463340637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36307214258040713642227091 54460821387061070463340637)
                ·
                  refine ⟨20422808020147901423752739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54460821387061070463340637 20422808020147901423752739)
                  ·
                    refine ⟨30634212030221852135629109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20422808020147901423752739 30634212030221852135629109)
                    ·
                      refine ⟨2871957377833298637715229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30634212030221852135629109 2871957377833298637715229)
                      ·
                        rfl

theorem cell23_5593117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5593117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593117 prefixEnd_5593117 := by exact prefixLift 5593117
  have htrace : WordTrace (prefixWord ++ tailWord_5593117) baseStart_5593117 baseEnd_5593117 := by
    simpa [prefixWord, tailWord_5593117, baseEnd_5593117] using wordTrace_append hprefix tailTrace_5593117
  have hstable : (prefixWord ++ tailWord_5593117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593117).length < 2 ^ (prefixWord ++ tailWord_5593117).sum := by decide
  have hdescent : baseEnd_5593117 < baseStart_5593117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593137 : List Nat := [1, 2, 2, 3, 1, 3, 4, 7]
def baseStart_5593137 : Nat := 118140960795 + 5593137 * 2 ^ 59
def prefixEnd_5593137 : Nat := 4983230072969 + 3 ^ 40 * 5593137 * 2
def baseEnd_5593137 : Nat := 106369172127644020720931

theorem tailTrace_5593137 : CollatzResearch.WordTrace tailWord_5593137 prefixEnd_5593137 106369172127644020720931 := by
  unfold tailWord_5593137
  simp only [CollatzResearch.WordTrace]
  refine ⟨203998465538027355594825665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135998977025351570396550443 203998465538027355594825665)
  ·
    refine ⟨152998849153520516696119249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203998465538027355594825665 152998849153520516696119249)
    ·
      refine ⟨114749136865140387522089437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152998849153520516696119249 114749136865140387522089437)
      ·
        refine ⟨43030926324427645320783539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114749136865140387522089437 43030926324427645320783539)
        ·
          refine ⟨64546389486641467981175309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43030926324427645320783539 64546389486641467981175309)
          ·
            refine ⟨24204896057490550492940741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64546389486641467981175309 24204896057490550492940741)
            ·
              refine ⟨4538418010779478217426389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24204896057490550492940741 4538418010779478217426389)
              ·
                refine ⟨106369172127644020720931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4538418010779478217426389 106369172127644020720931)
                ·
                  rfl

theorem cell23_5593137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 7].length) (baseStart_5593137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593137 prefixEnd_5593137 := by exact prefixLift 5593137
  have htrace : WordTrace (prefixWord ++ tailWord_5593137) baseStart_5593137 baseEnd_5593137 := by
    simpa [prefixWord, tailWord_5593137, baseEnd_5593137] using wordTrace_append hprefix tailTrace_5593137
  have hstable : (prefixWord ++ tailWord_5593137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593137).length < 2 ^ (prefixWord ++ tailWord_5593137).sum := by decide
  have hdescent : baseEnd_5593137 < baseStart_5593137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593164 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_5593164 : Nat := 118140960795 + 5593164 * 2 ^ 59
def prefixEnd_5593164 : Nat := 4983230072969 + 3 ^ 40 * 5593164 * 2
def baseEnd_5593164 : Nat := 2871981511424059953827513

theorem tailTrace_5593164 : CollatzResearch.WordTrace tailWord_5593164 prefixEnd_5593164 2871981511424059953827513 := by
  unfold tailWord_5593164
  simp only [CollatzResearch.WordTrace]
  refine ⟨101999725154464769603029273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135999633539286359470705697 101999725154464769603029273)
  ·
    refine ⟨76499793865848577202271955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101999725154464769603029273 76499793865848577202271955)
    ·
      refine ⟨114749690798772865803407933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76499793865848577202271955 114749690798772865803407933)
      ·
        refine ⟨43031134049539824676277975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114749690798772865803407933 43031134049539824676277975)
        ·
          refine ⟨64546701074309737014416963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43031134049539824676277975 64546701074309737014416963)
          ·
            refine ⟨96820051611464605521625445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64546701074309737014416963 96820051611464605521625445)
            ·
              refine ⟨18153759677149613535304771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96820051611464605521625445 18153759677149613535304771)
              ·
                refine ⟨27230639515724420302957157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18153759677149613535304771 27230639515724420302957157)
                ·
                  refine ⟨5105744909198328806804467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27230639515724420302957157 5105744909198328806804467)
                  ·
                    refine ⟨7658617363797493210206701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5105744909198328806804467 7658617363797493210206701)
                    ·
                      refine ⟨2871981511424059953827513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7658617363797493210206701 2871981511424059953827513)
                      ·
                        rfl

theorem cell23_5593164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_5593164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593164 prefixEnd_5593164 := by exact prefixLift 5593164
  have htrace : WordTrace (prefixWord ++ tailWord_5593164) baseStart_5593164 baseEnd_5593164 := by
    simpa [prefixWord, tailWord_5593164, baseEnd_5593164] using wordTrace_append hprefix tailTrace_5593164
  have hstable : (prefixWord ++ tailWord_5593164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593164).length < 2 ^ (prefixWord ++ tailWord_5593164).sum := by decide
  have hdescent : baseEnd_5593164 < baseStart_5593164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593182 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_5593182 : Nat := 118140960795 + 5593182 * 2 ^ 59
def prefixEnd_5593182 : Nat := 4983230072969 + 3 ^ 40 * 5593182 * 2
def baseEnd_5593182 : Nat := 2871990754075840883402431

theorem tailTrace_5593182 : CollatzResearch.WordTrace tailWord_5593182 prefixEnd_5593182 2871990754075840883402431 := by
  unfold tailWord_5593182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25500013352858041035026725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136000071215242885520142533 25500013352858041035026725)
  ·
    refine ⟨4781252503660882694067511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25500013352858041035026725 4781252503660882694067511)
    ·
      refine ⟨7171878755491324041101267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4781252503660882694067511 7171878755491324041101267)
      ·
        refine ⟨10757818133236986061651901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7171878755491324041101267 10757818133236986061651901)
        ·
          refine ⟨4034181799963869773119463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10757818133236986061651901 4034181799963869773119463)
          ·
            refine ⟨6051272699945804659679195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034181799963869773119463 6051272699945804659679195)
            ·
              refine ⟨9076909049918706989518793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051272699945804659679195 9076909049918706989518793)
              ·
                refine ⟨6807681787439030242139095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9076909049918706989518793 6807681787439030242139095)
                ·
                  refine ⟨10211522681158545363208643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6807681787439030242139095 10211522681158545363208643)
                  ·
                    refine ⟨15317284021737818044812965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10211522681158545363208643 15317284021737818044812965)
                    ·
                      refine ⟨2871990754075840883402431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15317284021737818044812965 2871990754075840883402431)
                      ·
                        rfl

theorem cell23_5593182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_5593182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593182 prefixEnd_5593182 := by exact prefixLift 5593182
  have htrace : WordTrace (prefixWord ++ tailWord_5593182) baseStart_5593182 baseEnd_5593182 := by
    simpa [prefixWord, tailWord_5593182, baseEnd_5593182] using wordTrace_append hprefix tailTrace_5593182
  have hstable : (prefixWord ++ tailWord_5593182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593182).length < 2 ^ (prefixWord ++ tailWord_5593182).sum := by decide
  have hdescent : baseEnd_5593182 < baseStart_5593182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593207 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_5593207 : Nat := 118140960795 + 5593207 * 2 ^ 59
def prefixEnd_5593207 : Nat := 4983230072969 + 3 ^ 40 * 5593207 * 2
def baseEnd_5593207 : Nat := 2872003591092203285589815

theorem tailTrace_5593207 : CollatzResearch.WordTrace tailWord_5593207 prefixEnd_5593207 2872003591092203285589815 := by
  unfold tailWord_5593207
  simp only [CollatzResearch.WordTrace]
  refine ⟨204001018647773757549873875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136000679098515838366582583 204001018647773757549873875)
  ·
    refine ⟨306001527971660636324810813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204001018647773757549873875 306001527971660636324810813)
    ·
      refine ⟨114750572989372738621804055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306001527971660636324810813 114750572989372738621804055)
      ·
        refine ⟨172125859484059107932706083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114750572989372738621804055 172125859484059107932706083)
        ·
          refine ⟨258188789226088661899059125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172125859484059107932706083 258188789226088661899059125)
          ·
            refine ⟨24205198989945812053036793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258188789226088661899059125 24205198989945812053036793)
            ·
              refine ⟨18153899242459359039777595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24205198989945812053036793 18153899242459359039777595)
              ·
                refine ⟨27230848863689038559666393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18153899242459359039777595 27230848863689038559666393)
                ·
                  refine ⟨20423136647766778919749795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27230848863689038559666393 20423136647766778919749795)
                  ·
                    refine ⟨30634704971650168379624693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20423136647766778919749795 30634704971650168379624693)
                    ·
                      refine ⟨2872003591092203285589815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30634704971650168379624693 2872003591092203285589815)
                      ·
                        rfl

theorem cell23_5593207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_5593207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593207 prefixEnd_5593207 := by exact prefixLift 5593207
  have htrace : WordTrace (prefixWord ++ tailWord_5593207) baseStart_5593207 baseEnd_5593207 := by
    simpa [prefixWord, tailWord_5593207, baseEnd_5593207] using wordTrace_append hprefix tailTrace_5593207
  have hstable : (prefixWord ++ tailWord_5593207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593207).length < 2 ^ (prefixWord ++ tailWord_5593207).sum := by decide
  have hdescent : baseEnd_5593207 < baseStart_5593207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593224 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5593224 : Nat := 118140960795 + 5593224 * 2 ^ 59
def prefixEnd_5593224 : Nat := 4983230072969 + 3 ^ 40 * 5593224 * 2
def baseEnd_5593224 : Nat := 2872012320263329719077237

theorem tailTrace_5593224 : CollatzResearch.WordTrace tailWord_5593224 prefixEnd_5593224 2872012320263329719077237 := by
  unfold tailWord_5593224
  simp only [CollatzResearch.WordTrace]
  refine ⟨102000819344356084726621363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136001092459141446302161817 102000819344356084726621363)
  ·
    refine ⟨153001229016534127089932045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102000819344356084726621363 153001229016534127089932045)
    ·
      refine ⟨57375460881200297658724517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153001229016534127089932045 57375460881200297658724517)
      ·
        refine ⟨10757898915225055811010847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57375460881200297658724517 10757898915225055811010847)
        ·
          refine ⟨16136848372837583716516271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10757898915225055811010847 16136848372837583716516271)
          ·
            refine ⟨24205272559256375574774407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16136848372837583716516271 24205272559256375574774407)
            ·
              refine ⟨36307908838884563362161611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24205272559256375574774407 36307908838884563362161611)
              ·
                refine ⟨54461863258326845043242417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36307908838884563362161611 54461863258326845043242417)
                ·
                  refine ⟨40846397443745133782431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54461863258326845043242417 40846397443745133782431813)
                  ·
                    refine ⟨7658699520702212584205965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40846397443745133782431813 7658699520702212584205965)
                    ·
                      refine ⟨2872012320263329719077237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7658699520702212584205965 2872012320263329719077237)
                      ·
                        rfl

theorem cell23_5593224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5593224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593224 prefixEnd_5593224 := by exact prefixLift 5593224
  have htrace : WordTrace (prefixWord ++ tailWord_5593224) baseStart_5593224 baseEnd_5593224 := by
    simpa [prefixWord, tailWord_5593224, baseEnd_5593224] using wordTrace_append hprefix tailTrace_5593224
  have hstable : (prefixWord ++ tailWord_5593224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593224).length < 2 ^ (prefixWord ++ tailWord_5593224).sum := by decide
  have hdescent : baseEnd_5593224 < baseStart_5593224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593234 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5593234 : Nat := 118140960795 + 5593234 * 2 ^ 59
def prefixEnd_5593234 : Nat := 4983230072969 + 3 ^ 40 * 5593234 * 2
def baseEnd_5593234 : Nat := 2872017455069874679952191

theorem tailTrace_5593234 : CollatzResearch.WordTrace tailWord_5593234 prefixEnd_5593234 2872017455069874679952191 := by
  unfold tailWord_5593234
  simp only [CollatzResearch.WordTrace]
  refine ⟨51000500854668985290276689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136001335612450627440737837 51000500854668985290276689)
  ·
    refine ⟨38250375641001738967707517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51000500854668985290276689 38250375641001738967707517)
    ·
      refine ⟨14343890865375652112890319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38250375641001738967707517 14343890865375652112890319)
      ·
        refine ⟨21515836298063478169335479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14343890865375652112890319 21515836298063478169335479)
        ·
          refine ⟨32273754447095217254003219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21515836298063478169335479 32273754447095217254003219)
          ·
            refine ⟨48410631670642825881004829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32273754447095217254003219 48410631670642825881004829)
            ·
              refine ⟨18153986876491059705376811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48410631670642825881004829 18153986876491059705376811)
              ·
                refine ⟨27230980314736589558065217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18153986876491059705376811 27230980314736589558065217)
                ·
                  refine ⟨20423235236052442168548913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27230980314736589558065217 20423235236052442168548913)
                  ·
                    refine ⟨15317426427039331626411685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20423235236052442168548913 15317426427039331626411685)
                    ·
                      refine ⟨2872017455069874679952191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15317426427039331626411685 2872017455069874679952191)
                      ·
                        rfl

theorem cell23_5593234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5593234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593234 prefixEnd_5593234 := by exact prefixLift 5593234
  have htrace : WordTrace (prefixWord ++ tailWord_5593234) baseStart_5593234 baseEnd_5593234 := by
    simpa [prefixWord, tailWord_5593234, baseEnd_5593234] using wordTrace_append hprefix tailTrace_5593234
  have hstable : (prefixWord ++ tailWord_5593234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593234).length < 2 ^ (prefixWord ++ tailWord_5593234).sum := by decide
  have hdescent : baseEnd_5593234 < baseStart_5593234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593261 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 5]
def baseStart_5593261 : Nat := 118140960795 + 5593261 * 2 ^ 59
def prefixEnd_5593261 : Nat := 4983230072969 + 3 ^ 40 * 5593261 * 2
def baseEnd_5593261 : Nat := 319114591005282897146063

theorem tailTrace_5593261 : CollatzResearch.WordTrace tailWord_5593261 prefixEnd_5593261 319114591005282897146063 := by
  unfold tailWord_5593261
  simp only [CollatzResearch.WordTrace]
  refine ⟨204002988189578124772339637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136001992126385416514893091 204002988189578124772339637)
  ·
    refine ⟨19125280142772949197406841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204002988189578124772339637 19125280142772949197406841)
    ·
      refine ⟨14343960107079711898055131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19125280142772949197406841 14343960107079711898055131)
      ·
        refine ⟨21515940160619567847082697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14343960107079711898055131 21515940160619567847082697)
        ·
          refine ⟨16136955120464675885312023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21515940160619567847082697 16136955120464675885312023)
          ·
            refine ⟨24205432680697013827968035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16136955120464675885312023 24205432680697013827968035)
            ·
              refine ⟨36308149021045520741952053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24205432680697013827968035 36308149021045520741952053)
              ·
                refine ⟨3403888970723017569558005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36308149021045520741952053 3403888970723017569558005)
                ·
                  refine ⟨319114591005282897146063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3403888970723017569558005 319114591005282897146063)
                  ·
                    rfl

theorem cell23_5593261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_5593261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593261 prefixEnd_5593261 := by exact prefixLift 5593261
  have htrace : WordTrace (prefixWord ++ tailWord_5593261) baseStart_5593261 baseEnd_5593261 := by
    simpa [prefixWord, tailWord_5593261, baseEnd_5593261] using wordTrace_append hprefix tailTrace_5593261
  have hstable : (prefixWord ++ tailWord_5593261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593261).length < 2 ^ (prefixWord ++ tailWord_5593261).sum := by decide
  have hdescent : baseEnd_5593261 < baseStart_5593261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593294 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_5593294 : Nat := 118140960795 + 5593294 * 2 ^ 59
def prefixEnd_5593294 : Nat := 4983230072969 + 3 ^ 40 * 5593294 * 2
def baseEnd_5593294 : Nat := 2872048263909144445201915

theorem tailTrace_5593294 : CollatzResearch.WordTrace tailWord_5593294 prefixEnd_5593294 2872048263909144445201915 := by
  unfold tailWord_5593294
  simp only [CollatzResearch.WordTrace]
  refine ⟨25500523974807321426036367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136002794532305714272193957 25500523974807321426036367)
  ·
    refine ⟨38250785962210982139054551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25500523974807321426036367 38250785962210982139054551)
    ·
      refine ⟨57376178943316473208581827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38250785962210982139054551 57376178943316473208581827)
      ·
        refine ⟨86064268414974709812872741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57376178943316473208581827 86064268414974709812872741)
        ·
          refine ⟨16137050327807758089913639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86064268414974709812872741 16137050327807758089913639)
          ·
            refine ⟨24205575491711637134870459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16137050327807758089913639 24205575491711637134870459)
            ·
              refine ⟨36308363237567455702305689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24205575491711637134870459 36308363237567455702305689)
              ·
                refine ⟨27231272428175591776729267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36308363237567455702305689 27231272428175591776729267)
                ·
                  refine ⟨40846908642263387665093901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27231272428175591776729267 40846908642263387665093901)
                  ·
                    refine ⟨15317590740848770374410213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40846908642263387665093901 15317590740848770374410213)
                    ·
                      refine ⟨2872048263909144445201915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15317590740848770374410213 2872048263909144445201915)
                      ·
                        rfl

theorem cell23_5593294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_5593294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593294 prefixEnd_5593294 := by exact prefixLift 5593294
  have htrace : WordTrace (prefixWord ++ tailWord_5593294) baseStart_5593294 baseEnd_5593294 := by
    simpa [prefixWord, tailWord_5593294, baseEnd_5593294] using wordTrace_append hprefix tailTrace_5593294
  have hstable : (prefixWord ++ tailWord_5593294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593294).length < 2 ^ (prefixWord ++ tailWord_5593294).sum := by decide
  have hdescent : baseEnd_5593294 < baseStart_5593294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593334 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_5593334 : Nat := 118140960795 + 5593334 * 2 ^ 59
def prefixEnd_5593334 : Nat := 4983230072969 + 3 ^ 40 * 5593334 * 2
def baseEnd_5593334 : Nat := 319118755903924920966859

theorem tailTrace_5593334 : CollatzResearch.WordTrace tailWord_5593334 prefixEnd_5593334 319118755903924920966859 := by
  unfold tailWord_5593334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750353169894603639984191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136003767145542438826498037 12750353169894603639984191)
  ·
    refine ⟨19125529754841905459976287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12750353169894603639984191 19125529754841905459976287)
    ·
      refine ⟨28688294632262858189964431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19125529754841905459976287 28688294632262858189964431)
      ·
        refine ⟨43032441948394287284946647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28688294632262858189964431 43032441948394287284946647)
        ·
          refine ⟨64548662922591430927419971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43032441948394287284946647 64548662922591430927419971)
          ·
            refine ⟨96822994383887146391129957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64548662922591430927419971 96822994383887146391129957)
            ·
              refine ⟨18154311446978839948336867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96822994383887146391129957 18154311446978839948336867)
              ·
                refine ⟨27231467170468259922505301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18154311446978839948336867 27231467170468259922505301)
                ·
                  refine ⟨319118755903924920966859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27231467170468259922505301 319118755903924920966859)
                  ·
                    rfl

theorem cell23_5593334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_5593334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593334 prefixEnd_5593334 := by exact prefixLift 5593334
  have htrace : WordTrace (prefixWord ++ tailWord_5593334) baseStart_5593334 baseEnd_5593334 := by
    simpa [prefixWord, tailWord_5593334, baseEnd_5593334] using wordTrace_append hprefix tailTrace_5593334
  have hstable : (prefixWord ++ tailWord_5593334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593334).length < 2 ^ (prefixWord ++ tailWord_5593334).sum := by decide
  have hdescent : baseEnd_5593334 < baseStart_5593334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593337 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_5593337 : Nat := 118140960795 + 5593337 * 2 ^ 59
def prefixEnd_5593337 : Nat := 4983230072969 + 3 ^ 40 * 5593337 * 2
def baseEnd_5593337 : Nat := 2872070343577287776964217

theorem tailTrace_5593337 : CollatzResearch.WordTrace tailWord_5593337 prefixEnd_5593337 2872070343577287776964217 := by
  unfold tailWord_5593337
  simp only [CollatzResearch.WordTrace]
  refine ⟨204005760137302789752106265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136003840091535193168070843 204005760137302789752106265)
  ·
    refine ⟨153004320102977092314079699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204005760137302789752106265 153004320102977092314079699)
    ·
      refine ⟨229506480154465638471119549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153004320102977092314079699 229506480154465638471119549)
      ·
        refine ⟨86064930057924614426669831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229506480154465638471119549 86064930057924614426669831)
        ·
          refine ⟨129097395086886921640004747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86064930057924614426669831 129097395086886921640004747)
          ·
            refine ⟨193646092630330382460007121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129097395086886921640004747 193646092630330382460007121)
            ·
              refine ⟨145234569472747786845005341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193646092630330382460007121 145234569472747786845005341)
              ·
                refine ⟨54462963552280420066877003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145234569472747786845005341 54462963552280420066877003)
                ·
                  refine ⟨81694445328420630100315505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54462963552280420066877003 81694445328420630100315505)
                  ·
                    refine ⟨61270833996315472575236629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81694445328420630100315505 61270833996315472575236629)
                    ·
                      refine ⟨2872070343577287776964217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61270833996315472575236629 2872070343577287776964217)
                      ·
                        rfl

theorem cell23_5593337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_5593337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593337 prefixEnd_5593337 := by exact prefixLift 5593337
  have htrace : WordTrace (prefixWord ++ tailWord_5593337) baseStart_5593337 baseEnd_5593337 := by
    simpa [prefixWord, tailWord_5593337, baseEnd_5593337] using wordTrace_append hprefix tailTrace_5593337
  have hstable : (prefixWord ++ tailWord_5593337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593337).length < 2 ^ (prefixWord ++ tailWord_5593337).sum := by decide
  have hdescent : baseEnd_5593337 < baseStart_5593337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593371 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 2, 3, 2]
def baseStart_5593371 : Nat := 118140960795 + 5593371 * 2 ^ 59
def prefixEnd_5593371 : Nat := 4983230072969 + 3 ^ 40 * 5593371 * 2
def baseEnd_5593371 : Nat := 2872087801919540643939061

theorem tailTrace_5593371 : CollatzResearch.WordTrace tailWord_5593371 prefixEnd_5593371 2872087801919540643939061 := by
  unfold tailWord_5593371
  simp only [CollatzResearch.WordTrace]
  refine ⟨204007000219179613558843967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136004666812786409039229311 204007000219179613558843967)
  ·
    refine ⟨306010500328769420338265951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204007000219179613558843967 306010500328769420338265951)
    ·
      refine ⟨459015750493154130507398927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306010500328769420338265951 459015750493154130507398927)
      ·
        refine ⟨688523625739731195761098391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459015750493154130507398927 688523625739731195761098391)
        ·
          refine ⟨1032785438609596793641647587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688523625739731195761098391 1032785438609596793641647587)
          ·
            refine ⟨1549178157914395190462471381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032785438609596793641647587 1549178157914395190462471381)
            ·
              refine ⟨36308863076118637276464173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1549178157914395190462471381 36308863076118637276464173)
              ·
                refine ⟨13615823653544488978674065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36308863076118637276464173 13615823653544488978674065)
                ·
                  refine ⟨10211867740158366734005549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13615823653544488978674065 10211867740158366734005549)
                  ·
                    refine ⟨3829450402559387525252081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10211867740158366734005549 3829450402559387525252081)
                    ·
                      refine ⟨2872087801919540643939061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829450402559387525252081 2872087801919540643939061)
                      ·
                        rfl

theorem cell23_5593371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3, 2].length) (baseStart_5593371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593371 prefixEnd_5593371 := by exact prefixLift 5593371
  have htrace : WordTrace (prefixWord ++ tailWord_5593371) baseStart_5593371 baseEnd_5593371 := by
    simpa [prefixWord, tailWord_5593371, baseEnd_5593371] using wordTrace_append hprefix tailTrace_5593371
  have hstable : (prefixWord ++ tailWord_5593371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593371).length < 2 ^ (prefixWord ++ tailWord_5593371).sum := by decide
  have hdescent : baseEnd_5593371 < baseStart_5593371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593389 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5593389 : Nat := 118140960795 + 5593389 * 2 ^ 59
def prefixEnd_5593389 : Nat := 4983230072969 + 3 ^ 40 * 5593389 * 2
def baseEnd_5593389 : Nat := 957365681523773857837993

theorem tailTrace_5593389 : CollatzResearch.WordTrace tailWord_5593389 prefixEnd_5593389 957365681523773857837993 := by
  unfold tailWord_5593389
  simp only [CollatzResearch.WordTrace]
  refine ⟨204007656733114402632999221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136005104488742935088666147 204007656733114402632999221)
  ·
    refine ⟨19125717818729475246843677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204007656733114402632999221 19125717818729475246843677)
    ·
      refine ⟨7172144182023553217566379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19125717818729475246843677 7172144182023553217566379)
      ·
        refine ⟨10758216273035329826349569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7172144182023553217566379 10758216273035329826349569)
        ·
          refine ⟨8068662204776497369762177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10758216273035329826349569 8068662204776497369762177)
          ·
            refine ⟨6051496653582373027321633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8068662204776497369762177 6051496653582373027321633)
            ·
              refine ⟨4538622490186779770491225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6051496653582373027321633 4538622490186779770491225)
              ·
                refine ⟨3403966867640084827868419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538622490186779770491225 3403966867640084827868419)
                ·
                  refine ⟨5105950301460127241802629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403966867640084827868419 5105950301460127241802629)
                  ·
                    refine ⟨957365681523773857837993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5105950301460127241802629 957365681523773857837993)
                    ·
                      rfl

theorem cell23_5593389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5593389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593389 prefixEnd_5593389 := by exact prefixLift 5593389
  have htrace : WordTrace (prefixWord ++ tailWord_5593389) baseStart_5593389 baseEnd_5593389 := by
    simpa [prefixWord, tailWord_5593389, baseEnd_5593389] using wordTrace_append hprefix tailTrace_5593389
  have hstable : (prefixWord ++ tailWord_5593389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593389).length < 2 ^ (prefixWord ++ tailWord_5593389).sum := by decide
  have hdescent : baseEnd_5593389 < baseStart_5593389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593401 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5593401 : Nat := 118140960795 + 5593401 * 2 ^ 59
def prefixEnd_5593401 : Nat := 4983230072969 + 3 ^ 40 * 5593401 * 2
def baseEnd_5593401 : Nat := 2872103206339175526563923

theorem tailTrace_5593401 : CollatzResearch.WordTrace tailWord_5593401 prefixEnd_5593401 2872103206339175526563923 := by
  unfold tailWord_5593401
  simp only [CollatzResearch.WordTrace]
  refine ⟨204008094409070928682436057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136005396272713952454957371 204008094409070928682436057)
  ·
    refine ⟨153006070806803196511827043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204008094409070928682436057 153006070806803196511827043)
    ·
      refine ⟨229509106210204794767740565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153006070806803196511827043 229509106210204794767740565)
      ·
        refine ⟨10758239353603349754737839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229509106210204794767740565 10758239353603349754737839)
        ·
          refine ⟨16137359030405024632106759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758239353603349754737839 16137359030405024632106759)
          ·
            refine ⟨24206038545607536948160139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16137359030405024632106759 24206038545607536948160139)
            ·
              refine ⟨36309057818411305422240209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24206038545607536948160139 36309057818411305422240209)
              ·
                refine ⟨27231793363808479066680157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36309057818411305422240209 27231793363808479066680157)
                ·
                  refine ⟨10211922511428179650005059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27231793363808479066680157 10211922511428179650005059)
                  ·
                    refine ⟨15317883767142269475007589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10211922511428179650005059 15317883767142269475007589)
                    ·
                      refine ⟨2872103206339175526563923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15317883767142269475007589 2872103206339175526563923)
                      ·
                        rfl

theorem cell23_5593401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5593401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593401 prefixEnd_5593401 := by exact prefixLift 5593401
  have htrace : WordTrace (prefixWord ++ tailWord_5593401) baseStart_5593401 baseEnd_5593401 := by
    simpa [prefixWord, tailWord_5593401, baseEnd_5593401] using wordTrace_append hprefix tailTrace_5593401
  have hstable : (prefixWord ++ tailWord_5593401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593401).length < 2 ^ (prefixWord ++ tailWord_5593401).sum := by decide
  have hdescent : baseEnd_5593401 < baseStart_5593401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593404 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_5593404 : Nat := 118140960795 + 5593404 * 2 ^ 59
def prefixEnd_5593404 : Nat := 4983230072969 + 3 ^ 40 * 5593404 * 2
def baseEnd_5593404 : Nat := 2872104746781139014826409

theorem tailTrace_5593404 : CollatzResearch.WordTrace tailWord_5593404 prefixEnd_5593404 2872104746781139014826409 := by
  unfold tailWord_5593404
  simp only [CollatzResearch.WordTrace]
  refine ⟨102004101914030030097397633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136005469218706706796530177 102004101914030030097397633)
  ·
    refine ⟨76503076435522522573048225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102004101914030030097397633 76503076435522522573048225)
    ·
      refine ⟨57377307326641891929786169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76503076435522522573048225 57377307326641891929786169)
      ·
        refine ⟨43032980494981418947339627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57377307326641891929786169 43032980494981418947339627)
        ·
          refine ⟨64549470742472128421009441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43032980494981418947339627 64549470742472128421009441)
          ·
            refine ⟨48412103056854096315757081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64549470742472128421009441 48412103056854096315757081)
            ·
              refine ⟨36309077292640572236817811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48412103056854096315757081 36309077292640572236817811)
              ·
                refine ⟨54463615938960858355226717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36309077292640572236817811 54463615938960858355226717)
                ·
                  refine ⟨20423855977110321883210019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54463615938960858355226717 20423855977110321883210019)
                  ·
                    refine ⟨30635783965665482824815029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20423855977110321883210019 30635783965665482824815029)
                    ·
                      refine ⟨2872104746781139014826409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30635783965665482824815029 2872104746781139014826409)
                      ·
                        rfl

theorem cell23_5593404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_5593404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593404 prefixEnd_5593404 := by exact prefixLift 5593404
  have htrace : WordTrace (prefixWord ++ tailWord_5593404) baseStart_5593404 baseEnd_5593404 := by
    simpa [prefixWord, tailWord_5593404, baseEnd_5593404] using wordTrace_append hprefix tailTrace_5593404
  have hstable : (prefixWord ++ tailWord_5593404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593404).length < 2 ^ (prefixWord ++ tailWord_5593404).sum := by decide
  have hdescent : baseEnd_5593404 < baseStart_5593404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593411 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 2, 4]
def baseStart_5593411 : Nat := 118140960795 + 5593411 * 2 ^ 59
def prefixEnd_5593411 : Nat := 4983230072969 + 3 ^ 40 * 5593411 * 2
def baseEnd_5593411 : Nat := 957369447048573495812959

theorem tailTrace_5593411 : CollatzResearch.WordTrace tailWord_5593411 prefixEnd_5593411 957369447048573495812959 := by
  unfold tailWord_5593411
  simp only [CollatzResearch.WordTrace]
  refine ⟨204008459139034700390300087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136005639426023133593533391 204008459139034700390300087)
  ·
    refine ⟨306012688708552050585450131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204008459139034700390300087 306012688708552050585450131)
    ·
      refine ⟨459019033062828075878175197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306012688708552050585450131 459019033062828075878175197)
      ·
        refine ⟨172132137398560528454315699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459019033062828075878175197 172132137398560528454315699)
        ·
          refine ⟨258198206097840792681473549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172132137398560528454315699 258198206097840792681473549)
          ·
            refine ⟨96824327286690297255552581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258198206097840792681473549 96824327286690297255552581)
            ·
              refine ⟨18154561366254430735416109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96824327286690297255552581 18154561366254430735416109)
              ·
                refine ⟨6807960512345411525781041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18154561366254430735416109 6807960512345411525781041)
                ·
                  refine ⟨5105970384259058644335781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6807960512345411525781041 5105970384259058644335781)
                  ·
                    refine ⟨957369447048573495812959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5105970384259058644335781 957369447048573495812959)
                    ·
                      rfl

theorem cell23_5593411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 4].length) (baseStart_5593411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593411 prefixEnd_5593411 := by exact prefixLift 5593411
  have htrace : WordTrace (prefixWord ++ tailWord_5593411) baseStart_5593411 baseEnd_5593411 := by
    simpa [prefixWord, tailWord_5593411, baseEnd_5593411] using wordTrace_append hprefix tailTrace_5593411
  have hstable : (prefixWord ++ tailWord_5593411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593411).length < 2 ^ (prefixWord ++ tailWord_5593411).sum := by decide
  have hdescent : baseEnd_5593411 < baseStart_5593411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593451 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 3]
def baseStart_5593451 : Nat := 118140960795 + 5593451 * 2 ^ 59
def prefixEnd_5593451 : Nat := 4983230072969 + 3 ^ 40 * 5593451 * 2
def baseEnd_5593451 : Nat := 2872128880371900330938693

theorem tailTrace_5593451 : CollatzResearch.WordTrace tailWord_5593451 prefixEnd_5593451 2872128880371900330938693 := by
  unfold tailWord_5593451
  simp only [CollatzResearch.WordTrace]
  refine ⟨204009918058889787221756207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136006612039259858147837471 204009918058889787221756207)
  ·
    refine ⟨306014877088334680832634311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204009918058889787221756207 306014877088334680832634311)
    ·
      refine ⟨459022315632502021248951467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306014877088334680832634311 459022315632502021248951467)
      ·
        refine ⟨688533473448753031873427201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459022315632502021248951467 688533473448753031873427201)
        ·
          refine ⟨516400105086564773905070401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688533473448753031873427201 516400105086564773905070401)
          ·
            refine ⟨387300078814923580428802801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516400105086564773905070401 387300078814923580428802801)
            ·
              refine ⟨290475059111192685321602101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387300078814923580428802801 290475059111192685321602101)
              ·
                refine ⟨27232036791674314248900197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290475059111192685321602101 27232036791674314248900197)
                ·
                  refine ⟨5106006898438933921668787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27232036791674314248900197 5106006898438933921668787)
                  ·
                    refine ⟨7659010347658400882503181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5106006898438933921668787 7659010347658400882503181)
                    ·
                      refine ⟨2872128880371900330938693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7659010347658400882503181 2872128880371900330938693)
                      ·
                        rfl

theorem cell23_5593451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 3].length) (baseStart_5593451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593451 prefixEnd_5593451 := by exact prefixLift 5593451
  have htrace : WordTrace (prefixWord ++ tailWord_5593451) baseStart_5593451 baseEnd_5593451 := by
    simpa [prefixWord, tailWord_5593451, baseEnd_5593451] using wordTrace_append hprefix tailTrace_5593451
  have hstable : (prefixWord ++ tailWord_5593451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593451).length < 2 ^ (prefixWord ++ tailWord_5593451).sum := by decide
  have hdescent : baseEnd_5593451 < baseStart_5593451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593462 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_5593462 : Nat := 118140960795 + 5593462 * 2 ^ 59
def prefixEnd_5593462 : Nat := 4983230072969 + 3 ^ 40 * 5593462 * 2
def baseEnd_5593462 : Nat := 957378176219699929300381

theorem tailTrace_5593462 : CollatzResearch.WordTrace tailWord_5593462 prefixEnd_5593462 957378176219699929300381 := by
  unfold tailWord_5593462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750644953865621006275415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136006879507899957400271093 12750644953865621006275415)
  ·
    refine ⟨19125967430798431509413123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12750644953865621006275415 19125967430798431509413123)
    ·
      refine ⟨28688951146197647264119685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19125967430798431509413123 28688951146197647264119685)
      ·
        refine ⟨5379178339912058862022441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28688951146197647264119685 5379178339912058862022441)
        ·
          refine ⟨4034383754934044146516831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5379178339912058862022441 4034383754934044146516831)
          ·
            refine ⟨6051575632401066219775247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034383754934044146516831 6051575632401066219775247)
            ·
              refine ⟨9077363448601599329662871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051575632401066219775247 9077363448601599329662871)
              ·
                refine ⟨13616045172902398994494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9077363448601599329662871 13616045172902398994494307)
                ·
                  refine ⟨20424067759353598491741461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13616045172902398994494307 20424067759353598491741461)
                  ·
                    refine ⟨957378176219699929300381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20424067759353598491741461 957378176219699929300381)
                    ·
                      rfl

theorem cell23_5593462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_5593462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593462 prefixEnd_5593462 := by exact prefixLift 5593462
  have htrace : WordTrace (prefixWord ++ tailWord_5593462) baseStart_5593462 baseEnd_5593462 := by
    simpa [prefixWord, tailWord_5593462, baseEnd_5593462] using wordTrace_append hprefix tailTrace_5593462
  have hstable : (prefixWord ++ tailWord_5593462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593462).length < 2 ^ (prefixWord ++ tailWord_5593462).sum := by decide
  have hdescent : baseEnd_5593462 < baseStart_5593462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593561 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_5593561 : Nat := 118140960795 + 5593561 * 2 ^ 59
def prefixEnd_5593561 : Nat := 4983230072969 + 3 ^ 40 * 5593561 * 2
def baseEnd_5593561 : Nat := 957395121081298300187729

theorem tailTrace_5593561 : CollatzResearch.WordTrace tailWord_5593561 prefixEnd_5593561 957395121081298300187729 := by
  unfold tailWord_5593561
  simp only [CollatzResearch.WordTrace]
  refine ⟨204013930088491276008260537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136009286725660850672173691 204013930088491276008260537)
  ·
    refine ⟨153010447566368457006195403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204013930088491276008260537 153010447566368457006195403)
    ·
      refine ⟨229515671349552685509293105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153010447566368457006195403 229515671349552685509293105)
      ·
        refine ⟨172136753512164514131969829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229515671349552685509293105 172136753512164514131969829)
        ·
          refine ⟨32275641283530846399744343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172136753512164514131969829 32275641283530846399744343)
          ·
            refine ⟨48413461925296269599616515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32275641283530846399744343 48413461925296269599616515)
            ·
              refine ⟨72620192887944404399424773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48413461925296269599616515 72620192887944404399424773)
              ·
                refine ⟨13616286166489575824892145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72620192887944404399424773 13616286166489575824892145)
                ·
                  refine ⟨10212214624867181868669109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13616286166489575824892145 10212214624867181868669109)
                  ·
                    refine ⟨957395121081298300187729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10212214624867181868669109 957395121081298300187729)
                    ·
                      rfl

theorem cell23_5593561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_5593561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593561 prefixEnd_5593561 := by exact prefixLift 5593561
  have htrace : WordTrace (prefixWord ++ tailWord_5593561) baseStart_5593561 baseEnd_5593561 := by
    simpa [prefixWord, tailWord_5593561, baseEnd_5593561] using wordTrace_append hprefix tailTrace_5593561
  have hstable : (prefixWord ++ tailWord_5593561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593561).length < 2 ^ (prefixWord ++ tailWord_5593561).sum := by decide
  have hdescent : baseEnd_5593561 < baseStart_5593561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593611 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6]
def baseStart_5593611 : Nat := 118140960795 + 5593611 * 2 ^ 59
def prefixEnd_5593611 : Nat := 4983230072969 + 3 ^ 40 * 5593611 * 2
def baseEnd_5593611 : Nat := 2872211037276619704937957

theorem tailTrace_5593611 : CollatzResearch.WordTrace tailWord_5593611 prefixEnd_5593611 2872211037276619704937957 := by
  unfold tailWord_5593611
  simp only [CollatzResearch.WordTrace]
  refine ⟨204015753738310134547580687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136010502492206756365053791 204015753738310134547580687)
  ·
    refine ⟨306023630607465201821371031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204015753738310134547580687 306023630607465201821371031)
    ·
      refine ⟨459035445911197802732056547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306023630607465201821371031 459035445911197802732056547)
      ·
        refine ⟨688553168866796704098084821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459035445911197802732056547 688553168866796704098084821)
        ·
          refine ⟨16137964895315547752298863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 688553168866796704098084821 16137964895315547752298863)
          ·
            refine ⟨24206947342973321628448295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16137964895315547752298863 24206947342973321628448295)
            ·
              refine ⟨36310421014459982442672443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24206947342973321628448295 36310421014459982442672443)
              ·
                refine ⟨54465631521689973664008665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36310421014459982442672443 54465631521689973664008665)
                ·
                  refine ⟨40849223641267480248006499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54465631521689973664008665 40849223641267480248006499)
                  ·
                    refine ⟨61273835461901220372009749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40849223641267480248006499 61273835461901220372009749)
                    ·
                      refine ⟨2872211037276619704937957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61273835461901220372009749 2872211037276619704937957)
                      ·
                        rfl

theorem cell23_5593611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_5593611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593611 prefixEnd_5593611 := by exact prefixLift 5593611
  have htrace : WordTrace (prefixWord ++ tailWord_5593611) baseStart_5593611 baseEnd_5593611 := by
    simpa [prefixWord, tailWord_5593611, baseEnd_5593611] using wordTrace_append hprefix tailTrace_5593611
  have hstable : (prefixWord ++ tailWord_5593611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593611).length < 2 ^ (prefixWord ++ tailWord_5593611).sum := by decide
  have hdescent : baseEnd_5593611 < baseStart_5593611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593621 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 8]
def baseStart_5593621 : Nat := 118140960795 + 5593621 * 2 ^ 59
def prefixEnd_5593621 : Nat := 4983230072969 + 3 ^ 40 * 5593621 * 2
def baseEnd_5593621 : Nat := 319135130231462740645879

theorem tailTrace_5593621 : CollatzResearch.WordTrace tailWord_5593621 prefixEnd_5593621 319135130231462740645879 := by
  unfold tailWord_5593621
  simp only [CollatzResearch.WordTrace]
  refine ⟨204016118468273906255444717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136010745645515937503629811 204016118468273906255444717)
  ·
    refine ⟨76506044425602714845791769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204016118468273906255444717 76506044425602714845791769)
    ·
      refine ⟨57379533319202036134343827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76506044425602714845791769 57379533319202036134343827)
      ·
        refine ⟨86069299978803054201515741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57379533319202036134343827 86069299978803054201515741)
        ·
          refine ⟨32275987492051145325568403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86069299978803054201515741 32275987492051145325568403)
          ·
            refine ⟨48413981238076717988352605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32275987492051145325568403 48413981238076717988352605)
            ·
              refine ⟨18155242964278769245632227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48413981238076717988352605 18155242964278769245632227)
              ·
                refine ⟨27232864446418153868448341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18155242964278769245632227 27232864446418153868448341)
                ·
                  refine ⟨319135130231462740645879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27232864446418153868448341 319135130231462740645879)
                  ·
                    rfl

theorem cell23_5593621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_5593621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593621 prefixEnd_5593621 := by exact prefixLift 5593621
  have htrace : WordTrace (prefixWord ++ tailWord_5593621) baseStart_5593621 baseEnd_5593621 := by
    simpa [prefixWord, tailWord_5593621, baseEnd_5593621] using wordTrace_append hprefix tailTrace_5593621
  have hstable : (prefixWord ++ tailWord_5593621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593621).length < 2 ^ (prefixWord ++ tailWord_5593621).sum := by decide
  have hdescent : baseEnd_5593621 < baseStart_5593621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593705 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 5, 2, 2]
def baseStart_5593705 : Nat := 118140960795 + 5593705 * 2 ^ 59
def prefixEnd_5593705 : Nat := 4983230072969 + 3 ^ 40 * 5593705 * 2
def baseEnd_5593705 : Nat := 2872259304458142337162525

theorem tailTrace_5593705 : CollatzResearch.WordTrace tailWord_5593705 prefixEnd_5593705 2872259304458142337162525 := by
  unfold tailWord_5593705
  simp only [CollatzResearch.WordTrace]
  refine ⟨204019182199969588601502569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136012788133313059067668379 204019182199969588601502569)
  ·
    refine ⟨153014386649977191451126927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204019182199969588601502569 153014386649977191451126927)
    ·
      refine ⟨229521579974965787176690391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153014386649977191451126927 229521579974965787176690391)
      ·
        refine ⟨344282369962448680765035587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229521579974965787176690391 344282369962448680765035587)
        ·
          refine ⟨516423554943673021147553381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344282369962448680765035587 516423554943673021147553381)
          ·
            refine ⟨96829416551938691465166259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 516423554943673021147553381 96829416551938691465166259)
            ·
              refine ⟨145244124827908037197749389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96829416551938691465166259 145244124827908037197749389)
              ·
                refine ⟨54466546810465513949156021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145244124827908037197749389 54466546810465513949156021)
                ·
                  refine ⟨5106238763481141932733377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54466546810465513949156021 5106238763481141932733377)
                  ·
                    refine ⟨3829679072610856449550033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106238763481141932733377 3829679072610856449550033)
                    ·
                      refine ⟨2872259304458142337162525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3829679072610856449550033 2872259304458142337162525)
                      ·
                        rfl

theorem cell23_5593705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 2, 2].length) (baseStart_5593705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593705 prefixEnd_5593705 := by exact prefixLift 5593705
  have htrace : WordTrace (prefixWord ++ tailWord_5593705) baseStart_5593705 baseEnd_5593705 := by
    simpa [prefixWord, tailWord_5593705, baseEnd_5593705] using wordTrace_append hprefix tailTrace_5593705
  have hstable : (prefixWord ++ tailWord_5593705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593705).length < 2 ^ (prefixWord ++ tailWord_5593705).sum := by decide
  have hdescent : baseEnd_5593705 < baseStart_5593705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593711 : List Nat := [1, 1, 2, 1, 3, 2, 4, 9]
def baseStart_5593711 : Nat := 118140960795 + 5593711 * 2 ^ 59
def prefixEnd_5593711 : Nat := 4983230072969 + 3 ^ 40 * 5593711 * 2
def baseEnd_5593711 : Nat := 106380088346002567173611

theorem tailTrace_5593711 : CollatzResearch.WordTrace tailWord_5593711 prefixEnd_5593711 106380088346002567173611 := by
  unfold tailWord_5593711
  simp only [CollatzResearch.WordTrace]
  refine ⟨204019401037947851626220987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136012934025298567750813991 204019401037947851626220987)
  ·
    refine ⟨306029101556921777439331481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204019401037947851626220987 306029101556921777439331481)
    ·
      refine ⟨229521826167691333079498611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306029101556921777439331481 229521826167691333079498611)
      ·
        refine ⟨344282739251536999619247917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229521826167691333079498611 344282739251536999619247917)
        ·
          refine ⟨129106027219326374857217969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344282739251536999619247917 129106027219326374857217969)
          ·
            refine ⟨96829520414494781142913477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129106027219326374857217969 96829520414494781142913477)
            ·
              refine ⟨18155535077717771464296277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96829520414494781142913477 18155535077717771464296277)
              ·
                refine ⟨106380088346002567173611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18155535077717771464296277 106380088346002567173611)
                ·
                  rfl

theorem cell23_5593711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 9].length) (baseStart_5593711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593711 prefixEnd_5593711 := by exact prefixLift 5593711
  have htrace : WordTrace (prefixWord ++ tailWord_5593711) baseStart_5593711 baseEnd_5593711 := by
    simpa [prefixWord, tailWord_5593711, baseEnd_5593711] using wordTrace_append hprefix tailTrace_5593711
  have hstable : (prefixWord ++ tailWord_5593711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593711).length < 2 ^ (prefixWord ++ tailWord_5593711).sum := by decide
  have hdescent : baseEnd_5593711 < baseStart_5593711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5593732 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_5593732 : Nat := 118140960795 + 5593732 * 2 ^ 59
def prefixEnd_5593732 : Nat := 4983230072969 + 3 ^ 40 * 5593732 * 2
def baseEnd_5593732 : Nat := 957424389478604577174967

theorem tailTrace_5593732 : CollatzResearch.WordTrace tailWord_5593732 prefixEnd_5593732 957424389478604577174967 := by
  unfold tailWord_5593732
  simp only [CollatzResearch.WordTrace]
  refine ⟨102010083485435886106367725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136013444647247848141823633 102010083485435886106367725)
  ·
    refine ⟨38253781307038457289887897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102010083485435886106367725 38253781307038457289887897)
    ·
      refine ⟨28690335980278842967415923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38253781307038457289887897 28690335980278842967415923)
      ·
        refine ⟨43035503970418264451123885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28690335980278842967415923 43035503970418264451123885)
        ·
          refine ⟨16138313988906849169171457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43035503970418264451123885 16138313988906849169171457)
          ·
            refine ⟨12103735491680136876878593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16138313988906849169171457 12103735491680136876878593)
            ·
              refine ⟨9077801618760102657658945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12103735491680136876878593 9077801618760102657658945)
              ·
                refine ⟨6808351214070076993244209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9077801618760102657658945 6808351214070076993244209)
                ·
                  refine ⟨5106263410552557744933157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6808351214070076993244209 5106263410552557744933157)
                  ·
                    refine ⟨957424389478604577174967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5106263410552557744933157 957424389478604577174967)
                    ·
                      rfl

theorem cell23_5593732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_5593732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5593732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5593732 prefixEnd_5593732 := by exact prefixLift 5593732
  have htrace : WordTrace (prefixWord ++ tailWord_5593732) baseStart_5593732 baseEnd_5593732 := by
    simpa [prefixWord, tailWord_5593732, baseEnd_5593732] using wordTrace_append hprefix tailTrace_5593732
  have hstable : (prefixWord ++ tailWord_5593732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5593732).length < 2 ^ (prefixWord ++ tailWord_5593732).sum := by decide
  have hdescent : baseEnd_5593732 < baseStart_5593732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5593732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
