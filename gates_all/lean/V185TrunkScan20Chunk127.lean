import V185TrunkScan20Chunk126

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_772882 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_772882 : Nat := 118140960795 + 772882 * 2 ^ 59
def prefixEnd_772882 : Nat := 4983230072969 + 3 ^ 40 * 772882 * 2
def baseEnd_772882 : Nat := 352764404629644737173855

theorem tailTrace_772882 : CollatzResearch.WordTrace tailWord_772882 prefixEnd_772882 352764404629644737173855 := by
  unfold tailWord_772882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047330596496996645458225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18792881590658657721221933 7047330596496996645458225)
  ·
    refine ⟨5285497947372747484093669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7047330596496996645458225 5285497947372747484093669)
    ·
      refine ⟨991030865132390153267563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5285497947372747484093669 991030865132390153267563)
      ·
        refine ⟨1486546297698585229901345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991030865132390153267563 1486546297698585229901345)
        ·
          refine ⟨1114909723273938922426009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1486546297698585229901345 1114909723273938922426009)
          ·
            refine ⟨836182292455454191819507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114909723273938922426009 836182292455454191819507)
            ·
              refine ⟨1254273438683181287729261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836182292455454191819507 1254273438683181287729261)
              ·
                refine ⟨470352539506192982898473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254273438683181287729261 470352539506192982898473)
                ·
                  refine ⟨352764404629644737173855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470352539506192982898473 352764404629644737173855)
                  ·
                    rfl

theorem cell20_772882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_772882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772882 prefixEnd_772882 := by exact prefixLift 772882
  have htrace : WordTrace (prefixWord ++ tailWord_772882) baseStart_772882 baseEnd_772882 := by
    simpa [prefixWord, tailWord_772882, baseEnd_772882] using wordTrace_append hprefix tailTrace_772882
  have hstable : (prefixWord ++ tailWord_772882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772882).length < 2 ^ (prefixWord ++ tailWord_772882).sum := by decide
  have hdescent : baseEnd_772882 < baseStart_772882 := by decide
  rcases family_descends (prefixWord ++ tailWord_772882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772893 : List Nat := [1, 4, 2, 4, 1, 2, 6]
def baseStart_772893 : Nat := 118140960795 + 772893 * 2 ^ 59
def prefixEnd_772893 : Nat := 4983230072969 + 3 ^ 40 * 772893 * 2
def baseEnd_772893 : Nat := 39196602814375287534127

theorem tailTrace_772893 : CollatzResearch.WordTrace tailWord_772893 prefixEnd_772893 39196602814375287534127 := by
  unfold tailWord_772893
  simp only [CollatzResearch.WordTrace]
  refine ⟨28189723588948135460483333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18793149059298756973655555 28189723588948135460483333)
  ·
    refine ⟨5285573172927775398840625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28189723588948135460483333 5285573172927775398840625)
    ·
      refine ⟨3964179879695831549130469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5285573172927775398840625 3964179879695831549130469)
      ·
        refine ⟨743283727442968415461963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3964179879695831549130469 743283727442968415461963)
        ·
          refine ⟨1114925591164452623192945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743283727442968415461963 1114925591164452623192945)
          ·
            refine ⟨836194193373339467394709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114925591164452623192945 836194193373339467394709)
            ·
              refine ⟨39196602814375287534127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 836194193373339467394709 39196602814375287534127)
              ·
                rfl

theorem cell20_772893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_772893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772893 prefixEnd_772893 := by exact prefixLift 772893
  have htrace : WordTrace (prefixWord ++ tailWord_772893) baseStart_772893 baseEnd_772893 := by
    simpa [prefixWord, tailWord_772893, baseEnd_772893] using wordTrace_append hprefix tailTrace_772893
  have hstable : (prefixWord ++ tailWord_772893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772893).length < 2 ^ (prefixWord ++ tailWord_772893).sum := by decide
  have hdescent : baseEnd_772893 < baseStart_772893 := by decide
  rcases family_descends (prefixWord ++ tailWord_772893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772917 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 3]
def baseStart_772917 : Nat := 118140960795 + 772917 * 2 ^ 59
def prefixEnd_772917 : Nat := 4983230072969 + 3 ^ 40 * 772917 * 2
def baseEnd_772917 : Nat := 352780379583340171007045

theorem tailTrace_772917 : CollatzResearch.WordTrace tailWord_772917 prefixEnd_772917 352780379583340171007045 := by
  unfold tailWord_772917
  simp only [CollatzResearch.WordTrace]
  refine ⟨28190598940861187559357005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18793732627240791706238003 28190598940861187559357005)
  ·
    refine ⟨10571474602822945334758877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28190598940861187559357005 10571474602822945334758877)
    ·
      refine ⟨3964302976058604500534579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10571474602822945334758877 3964302976058604500534579)
      ·
        refine ⟨5946454464087906750801869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964302976058604500534579 5946454464087906750801869)
        ·
          refine ⟨2229920424032965031550701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5946454464087906750801869 2229920424032965031550701)
          ·
            refine ⟨836220159012361886831513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2229920424032965031550701 836220159012361886831513)
            ·
              refine ⟨627165119259271415123635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836220159012361886831513 627165119259271415123635)
              ·
                refine ⟨940747678888907122685453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627165119259271415123635 940747678888907122685453)
                ·
                  refine ⟨352780379583340171007045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940747678888907122685453 352780379583340171007045)
                  ·
                    rfl

theorem cell20_772917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_772917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772917 prefixEnd_772917 := by exact prefixLift 772917
  have htrace : WordTrace (prefixWord ++ tailWord_772917) baseStart_772917 baseEnd_772917 := by
    simpa [prefixWord, tailWord_772917, baseEnd_772917] using wordTrace_append hprefix tailTrace_772917
  have hstable : (prefixWord ++ tailWord_772917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772917).length < 2 ^ (prefixWord ++ tailWord_772917).sum := by decide
  have hdescent : baseEnd_772917 < baseStart_772917 := by decide
  rcases family_descends (prefixWord ++ tailWord_772917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772942 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_772942 : Nat := 118140960795 + 772942 * 2 ^ 59
def prefixEnd_772942 : Nat := 4983230072969 + 3 ^ 40 * 772942 * 2
def baseEnd_772942 : Nat := 352791790264551195173609

theorem tailTrace_772942 : CollatzResearch.WordTrace tailWord_772942 prefixEnd_772942 352791790264551195173609 := by
  unfold tailWord_772942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523938845721327103627135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18794340510513744552678053 3523938845721327103627135)
  ·
    refine ⟨5285908268581990655440703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3523938845721327103627135 5285908268581990655440703)
    ·
      refine ⟨7928862402872985983161055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5285908268581990655440703 7928862402872985983161055)
      ·
        refine ⟨11893293604309478974741583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7928862402872985983161055 11893293604309478974741583)
        ·
          refine ⟨17839940406464218462112375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893293604309478974741583 17839940406464218462112375)
          ·
            refine ⟨26759910609696327693168563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17839940406464218462112375 26759910609696327693168563)
            ·
              refine ⟨40139865914544491539752845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26759910609696327693168563 40139865914544491539752845)
              ·
                refine ⟨15052449717954184327407317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40139865914544491539752845 15052449717954184327407317)
                ·
                  refine ⟨352791790264551195173609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15052449717954184327407317 352791790264551195173609)
                  ·
                    rfl

theorem cell20_772942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_772942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772942 prefixEnd_772942 := by exact prefixLift 772942
  have htrace : WordTrace (prefixWord ++ tailWord_772942) baseStart_772942 baseEnd_772942 := by
    simpa [prefixWord, tailWord_772942, baseEnd_772942] using wordTrace_append hprefix tailTrace_772942
  have hstable : (prefixWord ++ tailWord_772942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772942).length < 2 ^ (prefixWord ++ tailWord_772942).sum := by decide
  have hdescent : baseEnd_772942 < baseStart_772942 := by decide
  rcases family_descends (prefixWord ++ tailWord_772942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772959 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_772959 : Nat := 118140960795 + 772959 * 2 ^ 59
def prefixEnd_772959 : Nat := 4983230072969 + 3 ^ 40 * 772959 * 2
def baseEnd_772959 : Nat := 352799549527774691606873

theorem tailTrace_772959 : CollatzResearch.WordTrace tailWord_772959 prefixEnd_772959 352799549527774691606873 := by
  unfold tailWord_772959
  simp only [CollatzResearch.WordTrace]
  refine ⟨28192130806709028732385931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18794753871139352488257287 28192130806709028732385931)
  ·
    refine ⟨42288196210063543098578897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28192130806709028732385931 42288196210063543098578897)
    ·
      refine ⟨31716147157547657323934173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42288196210063543098578897 31716147157547657323934173)
      ·
        refine ⟨11893555184080371496475315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31716147157547657323934173 11893555184080371496475315)
        ·
          refine ⟨17840332776120557244712973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893555184080371496475315 17840332776120557244712973)
          ·
            refine ⟨6690124791045208966767365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17840332776120557244712973 6690124791045208966767365)
            ·
              refine ⟨1254398398320976681268881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6690124791045208966767365 1254398398320976681268881)
              ·
                refine ⟨940798798740732510951661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254398398320976681268881 940798798740732510951661)
                ·
                  refine ⟨352799549527774691606873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940798798740732510951661 352799549527774691606873)
                  ·
                    rfl

theorem cell20_772959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_772959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772959 prefixEnd_772959 := by exact prefixLift 772959
  have htrace : WordTrace (prefixWord ++ tailWord_772959) baseStart_772959 baseEnd_772959 := by
    simpa [prefixWord, tailWord_772959, baseEnd_772959] using wordTrace_append hprefix tailTrace_772959
  have hstable : (prefixWord ++ tailWord_772959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772959).length < 2 ^ (prefixWord ++ tailWord_772959).sum := by decide
  have hdescent : baseEnd_772959 < baseStart_772959 := by decide
  rcases family_descends (prefixWord ++ tailWord_772959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772987 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_772987 : Nat := 118140960795 + 772987 * 2 ^ 59
def prefixEnd_772987 : Nat := 4983230072969 + 3 ^ 40 * 772987 * 2
def baseEnd_772987 : Nat := 352812329490731038673425

theorem tailTrace_772987 : CollatzResearch.WordTrace tailWord_772987 prefixEnd_772987 352812329490731038673425 := by
  unfold tailWord_772987
  simp only [CollatzResearch.WordTrace]
  refine ⟨28193152050607589514405215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18795434700405059676270143 28193152050607589514405215)
  ·
    refine ⟨42289728075911384271607823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28193152050607589514405215 42289728075911384271607823)
    ·
      refine ⟨63434592113867076407411735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42289728075911384271607823 63434592113867076407411735)
      ·
        refine ⟨95151888170800614611117603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63434592113867076407411735 95151888170800614611117603)
        ·
          refine ⟨142727832256200921916676405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95151888170800614611117603 142727832256200921916676405)
          ·
            refine ⟨13380734274018836429688413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142727832256200921916676405 13380734274018836429688413)
            ·
              refine ⟨5017775352757063661133155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13380734274018836429688413 5017775352757063661133155)
              ·
                refine ⟨7526663029135595491699733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017775352757063661133155 7526663029135595491699733)
                ·
                  refine ⟨352812329490731038673425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7526663029135595491699733 352812329490731038673425)
                  ·
                    rfl

theorem cell20_772987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_772987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772987 prefixEnd_772987 := by exact prefixLift 772987
  have htrace : WordTrace (prefixWord ++ tailWord_772987) baseStart_772987 baseEnd_772987 := by
    simpa [prefixWord, tailWord_772987, baseEnd_772987] using wordTrace_append hprefix tailTrace_772987
  have hstable : (prefixWord ++ tailWord_772987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772987).length < 2 ^ (prefixWord ++ tailWord_772987).sum := by decide
  have hdescent : baseEnd_772987 < baseStart_772987 := by decide
  rcases family_descends (prefixWord ++ tailWord_772987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773000 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 2]
def baseStart_773000 : Nat := 118140960795 + 773000 * 2 ^ 59
def prefixEnd_773000 : Nat := 4983230072969 + 3 ^ 40 * 773000 * 2
def baseEnd_773000 : Nat := 352818263044960771240039

theorem tailTrace_773000 : CollatzResearch.WordTrace tailWord_773000 prefixEnd_773000 352818263044960771240039 := by
  unfold tailWord_773000
  simp only [CollatzResearch.WordTrace]
  refine ⟨14096813099780246367314227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18795750799706995156418969 14096813099780246367314227)
  ·
    refine ⟨21145219649670369550971341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14096813099780246367314227 21145219649670369550971341)
    ·
      refine ⟨7929457368626388581614253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21145219649670369550971341 7929457368626388581614253)
      ·
        refine ⟨2973546513234895718105345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7929457368626388581614253 2973546513234895718105345)
        ·
          refine ⟨2230159884926171788579009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2973546513234895718105345 2230159884926171788579009)
          ·
            refine ⟨1672619913694628841434257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230159884926171788579009 1672619913694628841434257)
            ·
              refine ⟨1254464935270971631075693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672619913694628841434257 1254464935270971631075693)
              ·
                refine ⟨470424350726614361653385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254464935270971631075693 470424350726614361653385)
                ·
                  refine ⟨352818263044960771240039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470424350726614361653385 352818263044960771240039)
                  ·
                    rfl

theorem cell20_773000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_773000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773000 prefixEnd_773000 := by exact prefixLift 773000
  have htrace : WordTrace (prefixWord ++ tailWord_773000) baseStart_773000 baseEnd_773000 := by
    simpa [prefixWord, tailWord_773000, baseEnd_773000] using wordTrace_append hprefix tailTrace_773000
  have hstable : (prefixWord ++ tailWord_773000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773000).length < 2 ^ (prefixWord ++ tailWord_773000).sum := by decide
  have hdescent : baseEnd_773000 < baseStart_773000 := by decide
  rcases family_descends (prefixWord ++ tailWord_773000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773010 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_773010 : Nat := 118140960795 + 773010 * 2 ^ 59
def prefixEnd_773010 : Nat := 4983230072969 + 3 ^ 40 * 773010 * 2
def baseEnd_773010 : Nat := 352822827317445180906665

theorem tailTrace_773010 : CollatzResearch.WordTrace tailWord_773010 prefixEnd_773010 352822827317445180906665 := by
  unfold tailWord_773010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7048497732381066110623121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18795993953016176294994989 7048497732381066110623121)
  ·
    refine ⟨5286373299285799582967341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7048497732381066110623121 5286373299285799582967341)
    ·
      refine ⟨1982389987232174843612753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5286373299285799582967341 1982389987232174843612753)
      ·
        refine ⟨1486792490424131132709565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1982389987232174843612753 1486792490424131132709565)
        ·
          refine ⟨557547183909049174766087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1486792490424131132709565 557547183909049174766087)
          ·
            refine ⟨836320775863573762149131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557547183909049174766087 836320775863573762149131)
            ·
              refine ⟨1254481163795360643223697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836320775863573762149131 1254481163795360643223697)
              ·
                refine ⟨940860872846520482417773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254481163795360643223697 940860872846520482417773)
                ·
                  refine ⟨352822827317445180906665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940860872846520482417773 352822827317445180906665)
                  ·
                    rfl

theorem cell20_773010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_773010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773010 prefixEnd_773010 := by exact prefixLift 773010
  have htrace : WordTrace (prefixWord ++ tailWord_773010) baseStart_773010 baseEnd_773010 := by
    simpa [prefixWord, tailWord_773010, baseEnd_773010] using wordTrace_append hprefix tailTrace_773010
  have hstable : (prefixWord ++ tailWord_773010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773010).length < 2 ^ (prefixWord ++ tailWord_773010).sum := by decide
  have hdescent : baseEnd_773010 < baseStart_773010 := by decide
  rcases family_descends (prefixWord ++ tailWord_773010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773021 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 2]
def baseStart_773021 : Nat := 118140960795 + 773021 * 2 ^ 59
def prefixEnd_773021 : Nat := 4983230072969 + 3 ^ 40 * 773021 * 2
def baseEnd_773021 : Nat := 352827848017178031539953

theorem tailTrace_773021 : CollatzResearch.WordTrace tailWord_773021 prefixEnd_773021 352827848017178031539953 := by
  unfold tailWord_773021
  simp only [CollatzResearch.WordTrace]
  refine ⟨28194392132484413321142917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18796261421656275547428611 28194392132484413321142917)
  ·
    refine ⟨5286448524840827497714297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28194392132484413321142917 5286448524840827497714297)
    ·
      refine ⟨3964836393630620623285723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5286448524840827497714297 3964836393630620623285723)
      ·
        refine ⟨5947254590445930934928585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964836393630620623285723 5947254590445930934928585)
        ·
          refine ⟨4460440942834448201196439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947254590445930934928585 4460440942834448201196439)
          ·
            refine ⟨6690661414251672301794659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460440942834448201196439 6690661414251672301794659)
            ·
              refine ⟨10035992121377508452691989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690661414251672301794659 10035992121377508452691989)
              ·
                refine ⟨470437130689570708719937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10035992121377508452691989 470437130689570708719937)
                ·
                  refine ⟨352827848017178031539953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470437130689570708719937 352827848017178031539953)
                  ·
                    rfl

theorem cell20_773021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_773021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773021 prefixEnd_773021 := by exact prefixLift 773021
  have htrace : WordTrace (prefixWord ++ tailWord_773021) baseStart_773021 baseEnd_773021 := by
    simpa [prefixWord, tailWord_773021, baseEnd_773021] using wordTrace_append hprefix tailTrace_773021
  have hstable : (prefixWord ++ tailWord_773021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773021).length < 2 ^ (prefixWord ++ tailWord_773021).sum := by decide
  have hdescent : baseEnd_773021 < baseStart_773021 := by decide
  rcases family_descends (prefixWord ++ tailWord_773021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773031 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 3]
def baseStart_773031 : Nat := 118140960795 + 773031 * 2 ^ 59
def prefixEnd_773031 : Nat := 4983230072969 + 3 ^ 40 * 773031 * 2
def baseEnd_773031 : Nat := 352832412289662441206579

theorem tailTrace_773031 : CollatzResearch.WordTrace tailWord_773031 prefixEnd_773031 352832412289662441206579 := by
  unfold tailWord_773031
  simp only [CollatzResearch.WordTrace]
  refine ⟨28194756862448185029006947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18796504574965456686004631 28194756862448185029006947)
  ·
    refine ⟨42292135293672277543510421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28194756862448185029006947 42292135293672277543510421)
    ·
      refine ⟨1982443841890888009852051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42292135293672277543510421 1982443841890888009852051)
      ·
        refine ⟨2973665762836332014778077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982443841890888009852051 2973665762836332014778077)
        ·
          refine ⟨1115124661063624505541779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2973665762836332014778077 1115124661063624505541779)
          ·
            refine ⟨1672686991595436758312669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115124661063624505541779 1672686991595436758312669)
            ·
              refine ⟨627257621848288784367251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1672686991595436758312669 627257621848288784367251)
              ·
                refine ⟨940886432772433176550877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627257621848288784367251 940886432772433176550877)
                ·
                  refine ⟨352832412289662441206579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940886432772433176550877 352832412289662441206579)
                  ·
                    rfl

theorem cell20_773031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_773031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773031 prefixEnd_773031 := by exact prefixLift 773031
  have htrace : WordTrace (prefixWord ++ tailWord_773031) baseStart_773031 baseEnd_773031 := by
    simpa [prefixWord, tailWord_773031, baseEnd_773031] using wordTrace_append hprefix tailTrace_773031
  have hstable : (prefixWord ++ tailWord_773031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773031).length < 2 ^ (prefixWord ++ tailWord_773031).sum := by decide
  have hdescent : baseEnd_773031 < baseStart_773031 := by decide
  rcases family_descends (prefixWord ++ tailWord_773031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773049 : List Nat := [1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_773049 : Nat := 118140960795 + 773049 * 2 ^ 59
def prefixEnd_773049 : Nat := 4983230072969 + 3 ^ 40 * 773049 * 2
def baseEnd_773049 : Nat := 117613542660044792868835

theorem tailTrace_773049 : CollatzResearch.WordTrace tailWord_773049 prefixEnd_773049 117613542660044792868835 := by
  unfold tailWord_773049
  simp only [CollatzResearch.WordTrace]
  refine ⟨28195413376382974103162201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18796942250921982735441467 28195413376382974103162201)
  ·
    refine ⟨21146560032287230577371651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28195413376382974103162201 21146560032287230577371651)
    ·
      refine ⟨31719840048430845866057477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21146560032287230577371651 31719840048430845866057477)
      ·
        refine ⟨5947470009080783599885777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31719840048430845866057477 5947470009080783599885777)
        ·
          refine ⟨4460602506810587699914333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947470009080783599885777 4460602506810587699914333)
          ·
            refine ⟨1672725940053970387467875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4460602506810587699914333 1672725940053970387467875)
            ·
              refine ⟨2509088910080955581201813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672725940053970387467875 2509088910080955581201813)
              ·
                refine ⟨117613542660044792868835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2509088910080955581201813 117613542660044792868835)
                ·
                  rfl

theorem cell20_773049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_773049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773049 prefixEnd_773049 := by exact prefixLift 773049
  have htrace : WordTrace (prefixWord ++ tailWord_773049) baseStart_773049 baseEnd_773049 := by
    simpa [prefixWord, tailWord_773049, baseEnd_773049] using wordTrace_append hprefix tailTrace_773049
  have hstable : (prefixWord ++ tailWord_773049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773049).length < 2 ^ (prefixWord ++ tailWord_773049).sum := by decide
  have hdescent : baseEnd_773049 < baseStart_773049 := by decide
  rcases family_descends (prefixWord ++ tailWord_773049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773056 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_773056 : Nat := 118140960795 + 773056 * 2 ^ 59
def prefixEnd_773056 : Nat := 4983230072969 + 3 ^ 40 * 773056 * 2
def baseEnd_773056 : Nat := 352843822970873465373143

theorem tailTrace_773056 : CollatzResearch.WordTrace tailWord_773056 prefixEnd_773056 352843822970873465373143 := by
  unfold tailWord_773056
  simp only [CollatzResearch.WordTrace]
  refine ⟨14097834343678807149333511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18797112458238409532444681 14097834343678807149333511)
  ·
    refine ⟨21146751515518210724000267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14097834343678807149333511 21146751515518210724000267)
    ·
      refine ⟨31720127273277316086000401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21146751515518210724000267 31720127273277316086000401)
      ·
        refine ⟨23790095454957987064500301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31720127273277316086000401 23790095454957987064500301)
        ·
          refine ⟨8921285795609245149187613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23790095454957987064500301 8921285795609245149187613)
          ·
            refine ⟨3345482173353466930945355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8921285795609245149187613 3345482173353466930945355)
            ·
              refine ⟨5018223260030200396418033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345482173353466930945355 5018223260030200396418033)
              ·
                refine ⟨3763667445022650297313525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5018223260030200396418033 3763667445022650297313525)
                ·
                  refine ⟨352843822970873465373143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3763667445022650297313525 352843822970873465373143)
                  ·
                    rfl

theorem cell20_773056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_773056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773056 prefixEnd_773056 := by exact prefixLift 773056
  have htrace : WordTrace (prefixWord ++ tailWord_773056) baseStart_773056 baseEnd_773056 := by
    simpa [prefixWord, tailWord_773056, baseEnd_773056] using wordTrace_append hprefix tailTrace_773056
  have hstable : (prefixWord ++ tailWord_773056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773056).length < 2 ^ (prefixWord ++ tailWord_773056).sum := by decide
  have hdescent : baseEnd_773056 < baseStart_773056 := by decide
  rcases family_descends (prefixWord ++ tailWord_773056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773063 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_773063 : Nat := 118140960795 + 773063 * 2 ^ 59
def prefixEnd_773063 : Nat := 4983230072969 + 3 ^ 40 * 773063 * 2
def baseEnd_773063 : Nat := 352847017961612552139781

theorem tailTrace_773063 : CollatzResearch.WordTrace tailWord_773063 prefixEnd_773063 352847017961612552139781 := by
  unfold tailWord_773063
  simp only [CollatzResearch.WordTrace]
  refine ⟨28195923998332254494171843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18797282665554836329447895 28195923998332254494171843)
  ·
    refine ⟨42293885997498381741257765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28195923998332254494171843 42293885997498381741257765)
    ·
      refine ⟨7930103624530946576485831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42293885997498381741257765 7930103624530946576485831)
      ·
        refine ⟨11895155436796419864728747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7930103624530946576485831 11895155436796419864728747)
        ·
          refine ⟨17842733155194629797093121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11895155436796419864728747 17842733155194629797093121)
          ·
            refine ⟨13382049866395972347819841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17842733155194629797093121 13382049866395972347819841)
            ·
              refine ⟨10036537399796979260864881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13382049866395972347819841 10036537399796979260864881)
              ·
                refine ⟨7527403049847734445648661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036537399796979260864881 7527403049847734445648661)
                ·
                  refine ⟨352847017961612552139781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7527403049847734445648661 352847017961612552139781)
                  ·
                    rfl

theorem cell20_773063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_773063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773063 prefixEnd_773063 := by exact prefixLift 773063
  have htrace : WordTrace (prefixWord ++ tailWord_773063) baseStart_773063 baseEnd_773063 := by
    simpa [prefixWord, tailWord_773063, baseEnd_773063] using wordTrace_append hprefix tailTrace_773063
  have hstable : (prefixWord ++ tailWord_773063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773063).length < 2 ^ (prefixWord ++ tailWord_773063).sum := by decide
  have hdescent : baseEnd_773063 < baseStart_773063 := by decide
  rcases family_descends (prefixWord ++ tailWord_773063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773080 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_773080 : Nat := 118140960795 + 773080 * 2 ^ 59
def prefixEnd_773080 : Nat := 4983230072969 + 3 ^ 40 * 773080 * 2
def baseEnd_773080 : Nat := 352854777224836048573045

theorem tailTrace_773080 : CollatzResearch.WordTrace tailWord_773080 prefixEnd_773080 352854777224836048573045 := by
  unfold tailWord_773080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14098272019635333198770347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18797696026180444265027129 14098272019635333198770347)
  ·
    refine ⟨21147408029452999798155521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14098272019635333198770347 21147408029452999798155521)
    ·
      refine ⟨15860556022089749848616641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21147408029452999798155521 15860556022089749848616641)
      ·
        refine ⟨11895417016567312386462481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15860556022089749848616641 11895417016567312386462481)
        ·
          refine ⟨8921562762425484289846861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11895417016567312386462481 8921562762425484289846861)
          ·
            refine ⟨3345586035909556608692573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8921562762425484289846861 3345586035909556608692573)
            ·
              refine ⟨1254594763466083728259715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3345586035909556608692573 1254594763466083728259715)
              ·
                refine ⟨1881892145199125592389573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254594763466083728259715 1881892145199125592389573)
                ·
                  refine ⟨352854777224836048573045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881892145199125592389573 352854777224836048573045)
                  ·
                    rfl

theorem cell20_773080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_773080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773080 prefixEnd_773080 := by exact prefixLift 773080
  have htrace : WordTrace (prefixWord ++ tailWord_773080) baseStart_773080 baseEnd_773080 := by
    simpa [prefixWord, tailWord_773080, baseEnd_773080] using wordTrace_append hprefix tailTrace_773080
  have hstable : (prefixWord ++ tailWord_773080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773080).length < 2 ^ (prefixWord ++ tailWord_773080).sum := by decide
  have hdescent : baseEnd_773080 < baseStart_773080 := by decide
  rcases family_descends (prefixWord ++ tailWord_773080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773139 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_773139 : Nat := 118140960795 + 773139 * 2 ^ 59
def prefixEnd_773139 : Nat := 4983230072969 + 3 ^ 40 * 773139 * 2
def baseEnd_773139 : Nat := 352881706432494065606137

theorem tailTrace_773139 : CollatzResearch.WordTrace tailWord_773139 prefixEnd_773139 352881706432494065606137 := by
  unfold tailWord_773139
  simp only [CollatzResearch.WordTrace]
  refine ⟨28198695946056919473938471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18799130630704612982625647 28198695946056919473938471)
  ·
    refine ⟨42298043919085379210907707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28198695946056919473938471 42298043919085379210907707)
    ·
      refine ⟨63447065878628068816361561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42298043919085379210907707 63447065878628068816361561)
      ·
        refine ⟨47585299408971051612271171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63447065878628068816361561 47585299408971051612271171)
        ·
          refine ⟨71377949113456577418406757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47585299408971051612271171 71377949113456577418406757)
          ·
            refine ⟨13383365458773108265951267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71377949113456577418406757 13383365458773108265951267)
            ·
              refine ⟨20075048188159662398926901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13383365458773108265951267 20075048188159662398926901)
              ·
                refine ⟨1882035767639968349899397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20075048188159662398926901 1882035767639968349899397)
                ·
                  refine ⟨352881706432494065606137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882035767639968349899397 352881706432494065606137)
                  ·
                    rfl

theorem cell20_773139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_773139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773139 prefixEnd_773139 := by exact prefixLift 773139
  have htrace : WordTrace (prefixWord ++ tailWord_773139) baseStart_773139 baseEnd_773139 := by
    simpa [prefixWord, tailWord_773139, baseEnd_773139] using wordTrace_append hprefix tailTrace_773139
  have hstable : (prefixWord ++ tailWord_773139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773139).length < 2 ^ (prefixWord ++ tailWord_773139).sum := by decide
  have hdescent : baseEnd_773139 < baseStart_773139 := by decide
  rcases family_descends (prefixWord ++ tailWord_773139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773156 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_773156 : Nat := 118140960795 + 773156 * 2 ^ 59
def prefixEnd_773156 : Nat := 4983230072969 + 3 ^ 40 * 773156 * 2
def baseEnd_773156 : Nat := 352889465695717562039401

theorem tailTrace_773156 : CollatzResearch.WordTrace tailWord_773156 prefixEnd_773156 352889465695717562039401 := by
  unfold tailWord_773156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099657993497665688653661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18799543991330220918204881 14099657993497665688653661)
  ·
    refine ⟨5287371747561624633245123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14099657993497665688653661 5287371747561624633245123)
    ·
      refine ⟨7931057621342436949867685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287371747561624633245123 7931057621342436949867685)
      ·
        refine ⟨1487073304001706928100191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7931057621342436949867685 1487073304001706928100191)
        ·
          refine ⟨2230609956002560392150287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487073304001706928100191 2230609956002560392150287)
          ·
            refine ⟨3345914934003840588225431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230609956002560392150287 3345914934003840588225431)
            ·
              refine ⟨5018872401005760882338147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345914934003840588225431 5018872401005760882338147)
              ·
                refine ⟨7528308601508641323507221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018872401005760882338147 7528308601508641323507221)
                ·
                  refine ⟨352889465695717562039401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7528308601508641323507221 352889465695717562039401)
                  ·
                    rfl

theorem cell20_773156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_773156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773156 prefixEnd_773156 := by exact prefixLift 773156
  have htrace : WordTrace (prefixWord ++ tailWord_773156) baseStart_773156 baseEnd_773156 := by
    simpa [prefixWord, tailWord_773156, baseEnd_773156] using wordTrace_append hprefix tailTrace_773156
  have hstable : (prefixWord ++ tailWord_773156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773156).length < 2 ^ (prefixWord ++ tailWord_773156).sum := by decide
  have hdescent : baseEnd_773156 < baseStart_773156 := by decide
  rcases family_descends (prefixWord ++ tailWord_773156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773159 : List Nat := [1, 1, 7, 1, 1, 2, 3, 4]
def baseStart_773159 : Nat := 118140960795 + 773159 * 2 ^ 59
def prefixEnd_773159 : Nat := 4983230072969 + 3 ^ 40 * 773159 * 2
def baseEnd_773159 : Nat := 117630278325820961646463

theorem tailTrace_773159 : CollatzResearch.WordTrace tailWord_773159 prefixEnd_773159 117630278325820961646463 := by
  unfold tailWord_773159
  simp only [CollatzResearch.WordTrace]
  refine ⟨28199425405984462889666531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18799616937322975259777687 28199425405984462889666531)
  ·
    refine ⟨42299138108976694334499797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28199425405984462889666531 42299138108976694334499797)
    ·
      refine ⟨991386049429141273464839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42299138108976694334499797 991386049429141273464839)
      ·
        refine ⟨1487079074143711910197259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991386049429141273464839 1487079074143711910197259)
        ·
          refine ⟨2230618611215567865295889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487079074143711910197259 2230618611215567865295889)
          ·
            refine ⟨1672963958411675898971917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230618611215567865295889 1672963958411675898971917)
            ·
              refine ⟨627361484404378462114469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1672963958411675898971917 627361484404378462114469)
              ·
                refine ⟨117630278325820961646463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627361484404378462114469 117630278325820961646463)
                ·
                  rfl

theorem cell20_773159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_773159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773159 prefixEnd_773159 := by exact prefixLift 773159
  have htrace : WordTrace (prefixWord ++ tailWord_773159) baseStart_773159 baseEnd_773159 := by
    simpa [prefixWord, tailWord_773159, baseEnd_773159] using wordTrace_append hprefix tailTrace_773159
  have hstable : (prefixWord ++ tailWord_773159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773159).length < 2 ^ (prefixWord ++ tailWord_773159).sum := by decide
  have hdescent : baseEnd_773159 < baseStart_773159 := by decide
  rcases family_descends (prefixWord ++ tailWord_773159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773163 : List Nat := [1, 1, 1, 1, 2, 1, 9, 4]
def baseStart_773163 : Nat := 118140960795 + 773163 * 2 ^ 59
def prefixEnd_773163 : Nat := 4983230072969 + 3 ^ 40 * 773163 * 2
def baseEnd_773163 : Nat := 117630886895485549602013

theorem tailTrace_773163 : CollatzResearch.WordTrace tailWord_773163 prefixEnd_773163 117630886895485549602013 := by
  unfold tailWord_773163
  simp only [CollatzResearch.WordTrace]
  refine ⟨28199571297969971572812143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18799714198646647715208095 28199571297969971572812143)
  ·
    refine ⟨42299356946954957359218215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28199571297969971572812143 42299356946954957359218215)
    ·
      refine ⟨63449035420432436038827323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42299356946954957359218215 63449035420432436038827323)
      ·
        refine ⟨95173553130648654058240985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63449035420432436038827323 95173553130648654058240985)
        ·
          refine ⟨71380164847986490543680739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95173553130648654058240985 71380164847986490543680739)
          ·
            refine ⟨107070247271979735815521109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71380164847986490543680739 107070247271979735815521109)
            ·
              refine ⟨627364730109256264544069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 107070247271979735815521109 627364730109256264544069)
              ·
                refine ⟨117630886895485549602013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627364730109256264544069 117630886895485549602013)
                ·
                  rfl

theorem cell20_773163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_773163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773163 prefixEnd_773163 := by exact prefixLift 773163
  have htrace : WordTrace (prefixWord ++ tailWord_773163) baseStart_773163 baseEnd_773163 := by
    simpa [prefixWord, tailWord_773163, baseEnd_773163] using wordTrace_append hprefix tailTrace_773163
  have hstable : (prefixWord ++ tailWord_773163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773163).length < 2 ^ (prefixWord ++ tailWord_773163).sum := by decide
  have hdescent : baseEnd_773163 < baseStart_773163 := by decide
  rcases family_descends (prefixWord ++ tailWord_773163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773170 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_773170 : Nat := 118140960795 + 773170 * 2 ^ 59
def prefixEnd_773170 : Nat := 4983230072969 + 3 ^ 40 * 773170 * 2
def baseEnd_773170 : Nat := 352895855677195735572677

theorem tailTrace_773170 : CollatzResearch.WordTrace tailWord_773170 prefixEnd_773170 352895855677195735572677 := by
  unfold tailWord_773170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049956652236152942079241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18799884405963074512211309 7049956652236152942079241)
  ·
    refine ⟨5287467489177114706559431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7049956652236152942079241 5287467489177114706559431)
    ·
      refine ⟨7931201233765672059839147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287467489177114706559431 7931201233765672059839147)
      ·
        refine ⟨11896801850648508089758721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7931201233765672059839147 11896801850648508089758721)
        ·
          refine ⟨8922601387986381067319041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11896801850648508089758721 8922601387986381067319041)
          ·
            refine ⟨6691951040989785800489281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8922601387986381067319041 6691951040989785800489281)
            ·
              refine ⟨5018963280742339350366961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6691951040989785800489281 5018963280742339350366961)
              ·
                refine ⟨3764222460556754512775221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5018963280742339350366961 3764222460556754512775221)
                ·
                  refine ⟨352895855677195735572677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3764222460556754512775221 352895855677195735572677)
                  ·
                    rfl

theorem cell20_773170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_773170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773170 prefixEnd_773170 := by exact prefixLift 773170
  have htrace : WordTrace (prefixWord ++ tailWord_773170) baseStart_773170 baseEnd_773170 := by
    simpa [prefixWord, tailWord_773170, baseEnd_773170] using wordTrace_append hprefix tailTrace_773170
  have hstable : (prefixWord ++ tailWord_773170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773170).length < 2 ^ (prefixWord ++ tailWord_773170).sum := by decide
  have hdescent : baseEnd_773170 < baseStart_773170 := by decide
  rcases family_descends (prefixWord ++ tailWord_773170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773184 : List Nat := [2, 1, 1, 2, 2, 3, 9]
def baseStart_773184 : Nat := 118140960795 + 773184 * 2 ^ 59
def prefixEnd_773184 : Nat := 4983230072969 + 3 ^ 40 * 773184 * 2
def baseEnd_773184 : Nat := 39211360628741545456217

theorem tailTrace_773184 : CollatzResearch.WordTrace tailWord_773184 prefixEnd_773184 39211360628741545456217 := by
  unfold tailWord_773184
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100168615446946079663303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18800224820595928106217737 14100168615446946079663303)
  ·
    refine ⟨21150252923170419119494955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14100168615446946079663303 21150252923170419119494955)
    ·
      refine ⟨31725379384755628679242433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21150252923170419119494955 31725379384755628679242433)
      ·
        refine ⟨23794034538566721509431825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31725379384755628679242433 23794034538566721509431825)
        ·
          refine ⟨17845525903925041132073869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23794034538566721509431825 17845525903925041132073869)
          ·
            refine ⟨6692072213971890424527701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17845525903925041132073869 6692072213971890424527701)
            ·
              refine ⟨39211360628741545456217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6692072213971890424527701 39211360628741545456217)
              ·
                rfl

theorem cell20_773184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_773184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773184 prefixEnd_773184 := by exact prefixLift 773184
  have htrace : WordTrace (prefixWord ++ tailWord_773184) baseStart_773184 baseEnd_773184 := by
    simpa [prefixWord, tailWord_773184, baseEnd_773184] using wordTrace_append hprefix tailTrace_773184
  have hstable : (prefixWord ++ tailWord_773184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773184).length < 2 ^ (prefixWord ++ tailWord_773184).sum := by decide
  have hdescent : baseEnd_773184 < baseStart_773184 := by decide
  rcases family_descends (prefixWord ++ tailWord_773184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773190 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_773190 : Nat := 118140960795 + 773190 * 2 ^ 59
def prefixEnd_773190 : Nat := 4983230072969 + 3 ^ 40 * 773190 * 2
def baseEnd_773190 : Nat := 352904984222164554905929

theorem tailTrace_773190 : CollatzResearch.WordTrace tailWord_773190 prefixEnd_773190 352904984222164554905929 := by
  unfold tailWord_773190
  simp only [CollatzResearch.WordTrace]
  refine ⟨881267377152254849501407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18800370712581436789363349 881267377152254849501407)
  ·
    refine ⟨1321901065728382274252111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 881267377152254849501407 1321901065728382274252111)
    ·
      refine ⟨1982851598592573411378167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321901065728382274252111 1982851598592573411378167)
      ·
        refine ⟨2974277397888860117067251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982851598592573411378167 2974277397888860117067251)
        ·
          refine ⟨4461416096833290175600877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974277397888860117067251 4461416096833290175600877)
          ·
            refine ⟨1673031036312483815850329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4461416096833290175600877 1673031036312483815850329)
            ·
              refine ⟨1254773277234362861887747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673031036312483815850329 1254773277234362861887747)
              ·
                refine ⟨1882159915851544292831621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254773277234362861887747 1882159915851544292831621)
                ·
                  refine ⟨352904984222164554905929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882159915851544292831621 352904984222164554905929)
                  ·
                    rfl

theorem cell20_773190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_773190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773190 prefixEnd_773190 := by exact prefixLift 773190
  have htrace : WordTrace (prefixWord ++ tailWord_773190) baseStart_773190 baseEnd_773190 := by
    simpa [prefixWord, tailWord_773190, baseEnd_773190] using wordTrace_append hprefix tailTrace_773190
  have hstable : (prefixWord ++ tailWord_773190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773190).length < 2 ^ (prefixWord ++ tailWord_773190).sum := by decide
  have hdescent : baseEnd_773190 < baseStart_773190 := by decide
  rcases family_descends (prefixWord ++ tailWord_773190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773214 : List Nat := [4, 4, 1, 1, 1, 1, 4, 4]
def baseStart_773214 : Nat := 118140960795 + 773214 * 2 ^ 59
def prefixEnd_773214 : Nat := 4983230072969 + 3 ^ 40 * 773214 * 2
def baseEnd_773214 : Nat := 117638646158709046035277

theorem tailTrace_773214 : CollatzResearch.WordTrace tailWord_773214 prefixEnd_773214 117638646158709046035277 := by
  unfold tailWord_773214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525178927598150910364837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18800954280523471521945797 3525178927598150910364837)
  ·
    refine ⟨660971048924653295693407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3525178927598150910364837 660971048924653295693407)
    ·
      refine ⟨991456573386979943540111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660971048924653295693407 991456573386979943540111)
      ·
        refine ⟨1487184860080469915310167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991456573386979943540111 1487184860080469915310167)
        ·
          refine ⟨2230777290120704872965251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487184860080469915310167 2230777290120704872965251)
          ·
            refine ⟨3346165935181057309447877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230777290120704872965251 3346165935181057309447877)
            ·
              refine ⟨627406112846448245521477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3346165935181057309447877 627406112846448245521477)
              ·
                refine ⟨117638646158709046035277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627406112846448245521477 117638646158709046035277)
                ·
                  rfl

theorem cell20_773214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_773214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773214 prefixEnd_773214 := by exact prefixLift 773214
  have htrace : WordTrace (prefixWord ++ tailWord_773214) baseStart_773214 baseEnd_773214 := by
    simpa [prefixWord, tailWord_773214, baseEnd_773214] using wordTrace_append hprefix tailTrace_773214
  have hstable : (prefixWord ++ tailWord_773214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773214).length < 2 ^ (prefixWord ++ tailWord_773214).sum := by decide
  have hdescent : baseEnd_773214 < baseStart_773214 := by decide
  rcases family_descends (prefixWord ++ tailWord_773214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773215 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_773215 : Nat := 118140960795 + 773215 * 2 ^ 59
def prefixEnd_773215 : Nat := 4983230072969 + 3 ^ 40 * 773215 * 2
def baseEnd_773215 : Nat := 352916394903375579072493

theorem tailTrace_773215 : CollatzResearch.WordTrace tailWord_773215 prefixEnd_773215 352916394903375579072493 := by
  unfold tailWord_773215
  simp only [CollatzResearch.WordTrace]
  refine ⟨28201467893781584453705099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18800978595854389635803399 28201467893781584453705099)
  ·
    refine ⟨42302201840672376680557649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28201467893781584453705099 42302201840672376680557649)
    ·
      refine ⟨31726651380504282510418237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42302201840672376680557649 31726651380504282510418237)
      ·
        refine ⟨11897494267689105941406839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31726651380504282510418237 11897494267689105941406839)
        ·
          refine ⟨17846241401533658912110259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11897494267689105941406839 17846241401533658912110259)
          ·
            refine ⟨26769362102300488368165389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17846241401533658912110259 26769362102300488368165389)
            ·
              refine ⟨10038510788362683138062021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26769362102300488368165389 10038510788362683138062021)
              ·
                refine ⟨1882220772818003088386629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10038510788362683138062021 1882220772818003088386629)
                ·
                  refine ⟨352916394903375579072493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882220772818003088386629 352916394903375579072493)
                  ·
                    rfl

theorem cell20_773215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_773215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773215 prefixEnd_773215 := by exact prefixLift 773215
  have htrace : WordTrace (prefixWord ++ tailWord_773215) baseStart_773215 baseEnd_773215 := by
    simpa [prefixWord, tailWord_773215, baseEnd_773215] using wordTrace_append hprefix tailTrace_773215
  have hstable : (prefixWord ++ tailWord_773215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773215).length < 2 ^ (prefixWord ++ tailWord_773215).sum := by decide
  have hdescent : baseEnd_773215 < baseStart_773215 := by decide
  rcases family_descends (prefixWord ++ tailWord_773215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773218 : List Nat := [3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_773218 : Nat := 118140960795 + 773218 * 2 ^ 59
def prefixEnd_773218 : Nat := 4983230072969 + 3 ^ 40 * 773218 * 2
def baseEnd_773218 : Nat := 117639254728373633990827

theorem tailTrace_773218 : CollatzResearch.WordTrace tailWord_773218 prefixEnd_773218 117639254728373633990827 := by
  unfold tailWord_773218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050394328192678991516077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18801051541847143977376205 7050394328192678991516077)
  ·
    refine ⟨2643897873072254621818529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7050394328192678991516077 2643897873072254621818529)
    ·
      refine ⟨1982923404804190966363897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2643897873072254621818529 1982923404804190966363897)
      ·
        refine ⟨1487192553603143224772923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1982923404804190966363897 1487192553603143224772923)
        ·
          refine ⟨2230788830404714837159385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487192553603143224772923 2230788830404714837159385)
          ·
            refine ⟨1673091622803536127869539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230788830404714837159385 1673091622803536127869539)
            ·
              refine ⟨2509637434205304191804309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673091622803536127869539 2509637434205304191804309)
              ·
                refine ⟨117639254728373633990827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2509637434205304191804309 117639254728373633990827)
                ·
                  rfl

theorem cell20_773218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_773218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773218 prefixEnd_773218 := by exact prefixLift 773218
  have htrace : WordTrace (prefixWord ++ tailWord_773218) baseStart_773218 baseEnd_773218 := by
    simpa [prefixWord, tailWord_773218, baseEnd_773218] using wordTrace_append hprefix tailTrace_773218
  have hstable : (prefixWord ++ tailWord_773218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773218).length < 2 ^ (prefixWord ++ tailWord_773218).sum := by decide
  have hdescent : baseEnd_773218 < baseStart_773218 := by decide
  rcases family_descends (prefixWord ++ tailWord_773218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773224 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 2]
def baseStart_773224 : Nat := 118140960795 + 773224 * 2 ^ 59
def prefixEnd_773224 : Nat := 4983230072969 + 3 ^ 40 * 773224 * 2
def baseEnd_773224 : Nat := 352920502748611547772457

theorem tailTrace_773224 : CollatzResearch.WordTrace tailWord_773224 prefixEnd_773224 352920502748611547772457 := by
  unfold tailWord_773224
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100898075374489495391363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18801197433832652660521817 14100898075374489495391363)
  ·
    refine ⟨21151347113061734243087045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14100898075374489495391363 21151347113061734243087045)
    ·
      refine ⟨3965877583699075170578821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21151347113061734243087045 3965877583699075170578821)
      ·
        refine ⟨743602046943576594483529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3965877583699075170578821 743602046943576594483529)
        ·
          refine ⟨557701535207682445862647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743602046943576594483529 557701535207682445862647)
          ·
            refine ⟨836552302811523668793971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557701535207682445862647 836552302811523668793971)
            ·
              refine ⟨1254828454217285503190957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836552302811523668793971 1254828454217285503190957)
              ·
                refine ⟨470560670331482063696609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254828454217285503190957 470560670331482063696609)
                ·
                  refine ⟨352920502748611547772457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470560670331482063696609 352920502748611547772457)
                  ·
                    rfl

theorem cell20_773224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_773224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773224 prefixEnd_773224 := by exact prefixLift 773224
  have htrace : WordTrace (prefixWord ++ tailWord_773224) baseStart_773224 baseEnd_773224 := by
    simpa [prefixWord, tailWord_773224, baseEnd_773224] using wordTrace_append hprefix tailTrace_773224
  have hstable : (prefixWord ++ tailWord_773224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773224).length < 2 ^ (prefixWord ++ tailWord_773224).sum := by decide
  have hdescent : baseEnd_773224 < baseStart_773224 := by decide
  rcases family_descends (prefixWord ++ tailWord_773224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773249 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 4]
def baseStart_773249 : Nat := 118140960795 + 773249 * 2 ^ 59
def prefixEnd_773249 : Nat := 4983230072969 + 3 ^ 40 * 773249 * 2
def baseEnd_773249 : Nat := 352931913429822571939021

theorem tailTrace_773249 : CollatzResearch.WordTrace tailWord_773249 prefixEnd_773249 352931913429822571939021 := by
  unfold tailWord_773249
  simp only [CollatzResearch.WordTrace]
  refine ⟨28202707975658408260442801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18801805317105605506961867 28202707975658408260442801)
  ·
    refine ⟨21152030981743806195332101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28202707975658408260442801 21152030981743806195332101)
    ·
      refine ⟨3966005809076963661624769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21152030981743806195332101 3966005809076963661624769)
      ·
        refine ⟨2974504356807722746218577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3966005809076963661624769 2974504356807722746218577)
        ·
          refine ⟨2230878267605792059663933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974504356807722746218577 2230878267605792059663933)
          ·
            refine ⟨836579350352172022373975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2230878267605792059663933 836579350352172022373975)
            ·
              refine ⟨1254869025528258033560963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836579350352172022373975 1254869025528258033560963)
              ·
                refine ⟨1882303538292387050341445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254869025528258033560963 1882303538292387050341445)
                ·
                  refine ⟨352931913429822571939021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882303538292387050341445 352931913429822571939021)
                  ·
                    rfl

theorem cell20_773249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_773249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773249 prefixEnd_773249 := by exact prefixLift 773249
  have htrace : WordTrace (prefixWord ++ tailWord_773249) baseStart_773249 baseEnd_773249 := by
    simpa [prefixWord, tailWord_773249, baseEnd_773249] using wordTrace_append hprefix tailTrace_773249
  have hstable : (prefixWord ++ tailWord_773249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773249).length < 2 ^ (prefixWord ++ tailWord_773249).sum := by decide
  have hdescent : baseEnd_773249 < baseStart_773249 := by decide
  rcases family_descends (prefixWord ++ tailWord_773249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773256 : List Nat := [2, 1, 3, 4, 2, 1, 2, 5]
def baseStart_773256 : Nat := 118140960795 + 773256 * 2 ^ 59
def prefixEnd_773256 : Nat := 4983230072969 + 3 ^ 40 * 773256 * 2
def baseEnd_773256 : Nat := 117645036140187219568553

theorem tailTrace_773256 : CollatzResearch.WordTrace tailWord_773256 prefixEnd_773256 117645036140187219568553 := by
  unfold tailWord_773256
  simp only [CollatzResearch.WordTrace]
  refine ⟨14101481643316524227973811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18801975524422032303965081 14101481643316524227973811)
  ·
    refine ⟨21152222464974786341960717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14101481643316524227973811 21152222464974786341960717)
    ·
      refine ⟨7932083424365544878235269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21152222464974786341960717 7932083424365544878235269)
      ·
        refine ⟨1487265642068539664669113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7932083424365544878235269 1487265642068539664669113)
        ·
          refine ⟨1115449231551404748501835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487265642068539664669113 1115449231551404748501835)
          ·
            refine ⟨1673173847327107122752753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115449231551404748501835 1673173847327107122752753)
            ·
              refine ⟨1254880385495330342064565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673173847327107122752753 1254880385495330342064565)
              ·
                refine ⟨117645036140187219568553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1254880385495330342064565 117645036140187219568553)
                ·
                  rfl

theorem cell20_773256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_773256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773256 prefixEnd_773256 := by exact prefixLift 773256
  have htrace : WordTrace (prefixWord ++ tailWord_773256) baseStart_773256 baseEnd_773256 := by
    simpa [prefixWord, tailWord_773256, baseEnd_773256] using wordTrace_append hprefix tailTrace_773256
  have hstable : (prefixWord ++ tailWord_773256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773256).length < 2 ^ (prefixWord ++ tailWord_773256).sum := by decide
  have hdescent : baseEnd_773256 < baseStart_773256 := by decide
  rcases family_descends (prefixWord ++ tailWord_773256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773298 : List Nat := [3, 2, 1, 1, 1, 12]
def baseStart_773298 : Nat := 118140960795 + 773298 * 2 ^ 59
def prefixEnd_773298 : Nat := 4983230072969 + 3 ^ 40 * 773298 * 2
def baseEnd_773298 : Nat := 13072380680185043677981

theorem tailTrace_773298 : CollatzResearch.WordTrace tailWord_773298 prefixEnd_773298 13072380680185043677981 := by
  unfold tailWord_773298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051123788120222407244137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18802996768320593085984365 7051123788120222407244137)
  ·
    refine ⟨5288342841090166805433103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7051123788120222407244137 5288342841090166805433103)
    ·
      refine ⟨7932514261635250208149655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288342841090166805433103 7932514261635250208149655)
      ·
        refine ⟨11898771392452875312224483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932514261635250208149655 11898771392452875312224483)
        ·
          refine ⟨17848157088679312968336725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898771392452875312224483 17848157088679312968336725)
          ·
            refine ⟨13072380680185043677981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17848157088679312968336725 13072380680185043677981)
            ·
              rfl

theorem cell20_773298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 12].length) (baseStart_773298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773298 prefixEnd_773298 := by exact prefixLift 773298
  have htrace : WordTrace (prefixWord ++ tailWord_773298) baseStart_773298 baseEnd_773298 := by
    simpa [prefixWord, tailWord_773298, baseEnd_773298] using wordTrace_append hprefix tailTrace_773298
  have hstable : (prefixWord ++ tailWord_773298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773298).length < 2 ^ (prefixWord ++ tailWord_773298).sum := by decide
  have hdescent : baseEnd_773298 < baseStart_773298 := by decide
  rcases family_descends (prefixWord ++ tailWord_773298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773408 : List Nat := [2, 1, 1, 5, 4, 1, 6]
def baseStart_773408 : Nat := 118140960795 + 773408 * 2 ^ 59
def prefixEnd_773408 : Nat := 4983230072969 + 3 ^ 40 * 773408 * 2
def baseEnd_773408 : Nat := 39222720595813853959819

theorem tailTrace_773408 : CollatzResearch.WordTrace tailWord_773408 prefixEnd_773408 39222720595813853959819 := by
  unfold tailWord_773408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14104253591041189207740439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18805671454721585610320585 14104253591041189207740439)
  ·
    refine ⟨21156380386561783811610659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14104253591041189207740439 21156380386561783811610659)
    ·
      refine ⟨31734570579842675717415989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21156380386561783811610659 31734570579842675717415989)
      ·
        refine ⟨2975115991860250848507749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31734570579842675717415989 2975115991860250848507749)
        ·
          refine ⟨557834248473797034095203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2975115991860250848507749 557834248473797034095203)
          ·
            refine ⟨836751372710695551142805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557834248473797034095203 836751372710695551142805)
            ·
              refine ⟨39222720595813853959819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 836751372710695551142805 39222720595813853959819)
              ·
                rfl

theorem cell20_773408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 6].length) (baseStart_773408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773408 prefixEnd_773408 := by exact prefixLift 773408
  have htrace : WordTrace (prefixWord ++ tailWord_773408) baseStart_773408 baseEnd_773408 := by
    simpa [prefixWord, tailWord_773408, baseEnd_773408] using wordTrace_append hprefix tailTrace_773408
  have hstable : (prefixWord ++ tailWord_773408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773408).length < 2 ^ (prefixWord ++ tailWord_773408).sum := by decide
  have hdescent : baseEnd_773408 < baseStart_773408 := by decide
  rcases family_descends (prefixWord ++ tailWord_773408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773429 : List Nat := [1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_773429 : Nat := 118140960795 + 773429 * 2 ^ 59
def prefixEnd_773429 : Nat := 4983230072969 + 3 ^ 40 * 773429 * 2
def baseEnd_773429 : Nat := 117671356778180648646095

theorem tailTrace_773429 : CollatzResearch.WordTrace tailWord_773429 prefixEnd_773429 117671356778180648646095 := by
  unfold tailWord_773429
  simp only [CollatzResearch.WordTrace]
  refine ⟨28209273115006299001995341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18806182076670866001330227 28209273115006299001995341)
  ·
    refine ⟨10578477418127362125748253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28209273115006299001995341 10578477418127362125748253)
    ·
      refine ⟨3966929031797760797155595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10578477418127362125748253 3966929031797760797155595)
      ·
        refine ⟨5950393547696641195733393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966929031797760797155595 5950393547696641195733393)
        ·
          refine ⟨4462795160772480896800045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950393547696641195733393 4462795160772480896800045)
          ·
            refine ⟨1673548185289680336300017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4462795160772480896800045 1673548185289680336300017)
            ·
              refine ⟨1255161138967260252225013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673548185289680336300017 1255161138967260252225013)
              ·
                refine ⟨117671356778180648646095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1255161138967260252225013 117671356778180648646095)
                ·
                  rfl

theorem cell20_773429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_773429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773429 prefixEnd_773429 := by exact prefixLift 773429
  have htrace : WordTrace (prefixWord ++ tailWord_773429) baseStart_773429 baseEnd_773429 := by
    simpa [prefixWord, tailWord_773429, baseEnd_773429] using wordTrace_append hprefix tailTrace_773429
  have hstable : (prefixWord ++ tailWord_773429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773429).length < 2 ^ (prefixWord ++ tailWord_773429).sum := by decide
  have hdescent : baseEnd_773429 < baseStart_773429 := by decide
  rcases family_descends (prefixWord ++ tailWord_773429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773469 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 2]
def baseStart_773469 : Nat := 118140960795 + 773469 * 2 ^ 59
def prefixEnd_773469 : Nat := 4983230072969 + 3 ^ 40 * 773469 * 2
def baseEnd_773469 : Nat := 353032327424479584604789

theorem tailTrace_773469 : CollatzResearch.WordTrace tailWord_773469 prefixEnd_773469 353032327424479584604789 := by
  unfold tailWord_773469
  simp only [CollatzResearch.WordTrace]
  refine ⟨28210732034861385833451461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18807154689907590555634307 28210732034861385833451461)
  ·
    refine ⟨5289512256536509843772149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28210732034861385833451461 5289512256536509843772149)
    ·
      refine ⟨495891774050297797853639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5289512256536509843772149 495891774050297797853639)
      ·
        refine ⟨743837661075446696780459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495891774050297797853639 743837661075446696780459)
        ·
          refine ⟨1115756491613170045170689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743837661075446696780459 1115756491613170045170689)
          ·
            refine ⟨836817368709877533878017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115756491613170045170689 836817368709877533878017)
            ·
              refine ⟨627613026532408150408513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836817368709877533878017 627613026532408150408513)
              ·
                refine ⟨470709769899306112806385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627613026532408150408513 470709769899306112806385)
                ·
                  refine ⟨353032327424479584604789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470709769899306112806385 353032327424479584604789)
                  ·
                    rfl

theorem cell20_773469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_773469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773469 prefixEnd_773469 := by exact prefixLift 773469
  have htrace : WordTrace (prefixWord ++ tailWord_773469) baseStart_773469 baseEnd_773469 := by
    simpa [prefixWord, tailWord_773469, baseEnd_773469] using wordTrace_append hprefix tailTrace_773469
  have hstable : (prefixWord ++ tailWord_773469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773469).length < 2 ^ (prefixWord ++ tailWord_773469).sum := by decide
  have hdescent : baseEnd_773469 < baseStart_773469 := by decide
  rcases family_descends (prefixWord ++ tailWord_773469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773522 : List Nat := [3, 2, 3, 3, 1, 1, 7]
def baseStart_773522 : Nat := 118140960795 + 773522 * 2 ^ 59
def prefixEnd_773522 : Nat := 4983230072969 + 3 ^ 40 * 773522 * 2
def baseEnd_773522 : Nat := 39228502007627439537545

theorem tailTrace_773522 : CollatzResearch.WordTrace tailWord_773522 prefixEnd_773522 39228502007627439537545 := by
  unfold tailWord_773522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053166275917343971282705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18808443402446250590087213 7053166275917343971282705)
  ·
    refine ⟨5289874706938007978462029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7053166275917343971282705 5289874706938007978462029)
    ·
      refine ⟨1983703015101752991923261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5289874706938007978462029 1983703015101752991923261)
      ·
        refine ⟨743888630663157371971223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1983703015101752991923261 743888630663157371971223)
        ·
          refine ⟨1115832945994736057956835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743888630663157371971223 1115832945994736057956835)
          ·
            refine ⟨1673749418992104086935253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115832945994736057956835 1673749418992104086935253)
            ·
              refine ⟨39228502007627439537545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1673749418992104086935253 39228502007627439537545)
              ·
                rfl

theorem cell20_773522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 7].length) (baseStart_773522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773522 prefixEnd_773522 := by exact prefixLift 773522
  have htrace : WordTrace (prefixWord ++ tailWord_773522) baseStart_773522 baseEnd_773522 := by
    simpa [prefixWord, tailWord_773522, baseEnd_773522] using wordTrace_append hprefix tailTrace_773522
  have hstable : (prefixWord ++ tailWord_773522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773522).length < 2 ^ (prefixWord ++ tailWord_773522).sum := by decide
  have hdescent : baseEnd_773522 < baseStart_773522 := by decide
  rcases family_descends (prefixWord ++ tailWord_773522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773529 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 3]
def baseStart_773529 : Nat := 118140960795 + 773529 * 2 ^ 59
def prefixEnd_773529 : Nat := 4983230072969 + 3 ^ 40 * 773529 * 2
def baseEnd_773529 : Nat := 353059713059386042604543

theorem tailTrace_773529 : CollatzResearch.WordTrace tailWord_773529 prefixEnd_773529 353059713059386042604543 := by
  unfold tailWord_773529
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212920414644016080635641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18808613609762677387090427 28212920414644016080635641)
  ·
    refine ⟨21159690310983012060476731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28212920414644016080635641 21159690310983012060476731)
    ·
      refine ⟨31739535466474518090715097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21159690310983012060476731 31739535466474518090715097)
      ·
        refine ⟨23804651599855888568036323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31739535466474518090715097 23804651599855888568036323)
        ·
          refine ⟨35706977399783832852054485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23804651599855888568036323 35706977399783832852054485)
          ·
            refine ⟨836882282807433582470027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35706977399783832852054485 836882282807433582470027)
            ·
              refine ⟨1255323424211150373705041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836882282807433582470027 1255323424211150373705041)
              ·
                refine ⟨941492568158362780278781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255323424211150373705041 941492568158362780278781)
                ·
                  refine ⟨353059713059386042604543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941492568158362780278781 353059713059386042604543)
                  ·
                    rfl

theorem cell20_773529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_773529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773529 prefixEnd_773529 := by exact prefixLift 773529
  have htrace : WordTrace (prefixWord ++ tailWord_773529) baseStart_773529 baseEnd_773529 := by
    simpa [prefixWord, tailWord_773529, baseEnd_773529] using wordTrace_append hprefix tailTrace_773529
  have hstable : (prefixWord ++ tailWord_773529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773529).length < 2 ^ (prefixWord ++ tailWord_773529).sum := by decide
  have hdescent : baseEnd_773529 < baseStart_773529 := by decide
  rcases family_descends (prefixWord ++ tailWord_773529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773536 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 2]
def baseStart_773536 : Nat := 118140960795 + 773536 * 2 ^ 59
def prefixEnd_773536 : Nat := 4983230072969 + 3 ^ 40 * 773536 * 2
def baseEnd_773536 : Nat := 353062908050125129371181

theorem tailTrace_773536 : CollatzResearch.WordTrace tailWord_773536 prefixEnd_773536 353062908050125129371181 := by
  unfold tailWord_773536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106587862809328138070231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18808783817079104184093641 14106587862809328138070231)
  ·
    refine ⟨21159881794213992207105347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14106587862809328138070231 21159881794213992207105347)
    ·
      refine ⟨31739822691320988310658021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21159881794213992207105347 31739822691320988310658021)
      ·
        refine ⟨5951216754622685308248379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31739822691320988310658021 5951216754622685308248379)
        ·
          refine ⟨8926825131934027962372569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951216754622685308248379 8926825131934027962372569)
          ·
            refine ⟨6695118848950520971779427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8926825131934027962372569 6695118848950520971779427)
            ·
              refine ⟨10042678273425781457669141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695118848950520971779427 10042678273425781457669141)
              ·
                refine ⟨470750544066833505828241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10042678273425781457669141 470750544066833505828241)
                ·
                  refine ⟨353062908050125129371181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470750544066833505828241 353062908050125129371181)
                  ·
                    rfl

theorem cell20_773536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_773536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773536 prefixEnd_773536 := by exact prefixLift 773536
  have htrace : WordTrace (prefixWord ++ tailWord_773536) baseStart_773536 baseEnd_773536 := by
    simpa [prefixWord, tailWord_773536, baseEnd_773536] using wordTrace_append hprefix tailTrace_773536
  have hstable : (prefixWord ++ tailWord_773536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773536).length < 2 ^ (prefixWord ++ tailWord_773536).sum := by decide
  have hdescent : baseEnd_773536 < baseStart_773536 := by decide
  rcases family_descends (prefixWord ++ tailWord_773536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773571 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_773571 : Nat := 118140960795 + 773571 * 2 ^ 59
def prefixEnd_773571 : Nat := 4983230072969 + 3 ^ 40 * 773571 * 2
def baseEnd_773571 : Nat := 353078883003820563204371

theorem tailTrace_773571 : CollatzResearch.WordTrace tailWord_773571 prefixEnd_773571 353078883003820563204371 := by
  unfold tailWord_773571
  simp only [CollatzResearch.WordTrace]
  refine ⟨28214452280491857253664567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18809634853661238169109711 28214452280491857253664567)
  ·
    refine ⟨42321678420737785880496851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28214452280491857253664567 42321678420737785880496851)
    ·
      refine ⟨63482517631106678820745277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42321678420737785880496851 63482517631106678820745277)
      ·
        refine ⟨23805944111665004557779479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63482517631106678820745277 23805944111665004557779479)
        ·
          refine ⟨35708916167497506836669219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23805944111665004557779479 35708916167497506836669219)
          ·
            refine ⟨53563374251246260255003829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35708916167497506836669219 53563374251246260255003829)
            ·
              refine ⟨5021566336054336898906609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53563374251246260255003829 5021566336054336898906609)
              ·
                refine ⟨3766174752040752674179957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021566336054336898906609 3766174752040752674179957)
                ·
                  refine ⟨353078883003820563204371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766174752040752674179957 353078883003820563204371)
                  ·
                    rfl

theorem cell20_773571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_773571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773571 prefixEnd_773571 := by exact prefixLift 773571
  have htrace : WordTrace (prefixWord ++ tailWord_773571) baseStart_773571 baseEnd_773571 := by
    simpa [prefixWord, tailWord_773571, baseEnd_773571] using wordTrace_append hprefix tailTrace_773571
  have hstable : (prefixWord ++ tailWord_773571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773571).length < 2 ^ (prefixWord ++ tailWord_773571).sum := by decide
  have hdescent : baseEnd_773571 < baseStart_773571 := by decide
  rcases family_descends (prefixWord ++ tailWord_773571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773605 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_773605 : Nat := 118140960795 + 773605 * 2 ^ 59
def prefixEnd_773605 : Nat := 4983230072969 + 3 ^ 40 * 773605 * 2
def baseEnd_773605 : Nat := 353094401530267556070899

theorem tailTrace_773605 : CollatzResearch.WordTrace tailWord_773605 prefixEnd_773605 353094401530267556070899 := by
  unfold tailWord_773605
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215692362368681060402269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18810461574912454040268179 28215692362368681060402269)
  ·
    refine ⟨10580884635888255397650851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28215692362368681060402269 10580884635888255397650851)
    ·
      refine ⟨15871326953832383096476277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10580884635888255397650851 15871326953832383096476277)
      ·
        refine ⟨1487936901921785915294651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15871326953832383096476277 1487936901921785915294651)
        ·
          refine ⟨2231905352882678872941977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487936901921785915294651 2231905352882678872941977)
          ·
            refine ⟨1673929014662009154706483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231905352882678872941977 1673929014662009154706483)
            ·
              refine ⟨2510893521993013732059725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673929014662009154706483 2510893521993013732059725)
              ·
                refine ⟨941585070747380149522397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510893521993013732059725 941585070747380149522397)
                ·
                  refine ⟨353094401530267556070899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941585070747380149522397 353094401530267556070899)
                  ·
                    rfl

theorem cell20_773605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_773605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773605 prefixEnd_773605 := by exact prefixLift 773605
  have htrace : WordTrace (prefixWord ++ tailWord_773605) baseStart_773605 baseEnd_773605 := by
    simpa [prefixWord, tailWord_773605, baseEnd_773605] using wordTrace_append hprefix tailTrace_773605
  have hstable : (prefixWord ++ tailWord_773605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773605).length < 2 ^ (prefixWord ++ tailWord_773605).sum := by decide
  have hdescent : baseEnd_773605 < baseStart_773605 := by decide
  rcases family_descends (prefixWord ++ tailWord_773605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773638 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_773638 : Nat := 118140960795 + 773638 * 2 ^ 59
def prefixEnd_773638 : Nat := 4983230072969 + 3 ^ 40 * 773638 * 2
def baseEnd_773638 : Nat := 353109463629466107970765

theorem tailTrace_773638 : CollatzResearch.WordTrace tailWord_773638 prefixEnd_773638 353109463629466107970765 := by
  unfold tailWord_773638
  simp only [CollatzResearch.WordTrace]
  refine ⟨881777999101535240511049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18811263980832751797569045 881777999101535240511049)
  ·
    refine ⟨661333499326151430383287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 881777999101535240511049 661333499326151430383287)
    ·
      refine ⟨992000248989227145574931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661333499326151430383287 992000248989227145574931)
      ·
        refine ⟨1488000373483840718362397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992000248989227145574931 1488000373483840718362397)
        ·
          refine ⟨558000140056440269385899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1488000373483840718362397 558000140056440269385899)
          ·
            refine ⟨837000210084660404078849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558000140056440269385899 837000210084660404078849)
            ·
              refine ⟨627750157563495303059137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837000210084660404078849 627750157563495303059137)
              ·
                refine ⟨470812618172621477294353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627750157563495303059137 470812618172621477294353)
                ·
                  refine ⟨353109463629466107970765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470812618172621477294353 353109463629466107970765)
                  ·
                    rfl

theorem cell20_773638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_773638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773638 prefixEnd_773638 := by exact prefixLift 773638
  have htrace : WordTrace (prefixWord ++ tailWord_773638) baseStart_773638 baseEnd_773638 := by
    simpa [prefixWord, tailWord_773638, baseEnd_773638] using wordTrace_append hprefix tailTrace_773638
  have hstable : (prefixWord ++ tailWord_773638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773638).length < 2 ^ (prefixWord ++ tailWord_773638).sum := by decide
  have hdescent : baseEnd_773638 < baseStart_773638 := by decide
  rcases family_descends (prefixWord ++ tailWord_773638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773643 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_773643 : Nat := 118140960795 + 773643 * 2 ^ 59
def prefixEnd_773643 : Nat := 4983230072969 + 3 ^ 40 * 773643 * 2
def baseEnd_773643 : Nat := 353111745765708312804077

theorem tailTrace_773643 : CollatzResearch.WordTrace tailWord_773643 prefixEnd_773643 353111745765708312804077 := by
  unfold tailWord_773643
  simp only [CollatzResearch.WordTrace]
  refine ⟨28217078336231013550285583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18811385557487342366857055 28217078336231013550285583)
  ·
    refine ⟨42325617504346520325428375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28217078336231013550285583 42325617504346520325428375)
    ·
      refine ⟨63488426256519780488142563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42325617504346520325428375 63488426256519780488142563)
      ·
        refine ⟨95232639384779670732213845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63488426256519780488142563 95232639384779670732213845)
        ·
          refine ⟨1116007492790386766393131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 95232639384779670732213845 1116007492790386766393131)
          ·
            refine ⟨1674011239185580149589697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116007492790386766393131 1674011239185580149589697)
            ·
              refine ⟨1255508429389185112192273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674011239185580149589697 1255508429389185112192273)
              ·
                refine ⟨941631322041888834144205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255508429389185112192273 941631322041888834144205)
                ·
                  refine ⟨353111745765708312804077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941631322041888834144205 353111745765708312804077)
                  ·
                    rfl

theorem cell20_773643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_773643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773643 prefixEnd_773643 := by exact prefixLift 773643
  have htrace : WordTrace (prefixWord ++ tailWord_773643) baseStart_773643 baseEnd_773643 := by
    simpa [prefixWord, tailWord_773643, baseEnd_773643] using wordTrace_append hprefix tailTrace_773643
  have hstable : (prefixWord ++ tailWord_773643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773643).length < 2 ^ (prefixWord ++ tailWord_773643).sum := by decide
  have hdescent : baseEnd_773643 < baseStart_773643 := by decide
  rcases family_descends (prefixWord ++ tailWord_773643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773688 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 2]
def baseStart_773688 : Nat := 118140960795 + 773688 * 2 ^ 59
def prefixEnd_773688 : Nat := 4983230072969 + 3 ^ 40 * 773688 * 2
def baseEnd_773688 : Nat := 353132284991888156303893

theorem tailTrace_773688 : CollatzResearch.WordTrace tailWord_773688 prefixEnd_773688 353132284991888156303893 := by
  unfold tailWord_773688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109359810533993117836859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18812479747378657490449145 14109359810533993117836859)
  ·
    refine ⟨21164039715800989676755289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14109359810533993117836859 21164039715800989676755289)
    ·
      refine ⟨15873029786850742257566467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21164039715800989676755289 15873029786850742257566467)
      ·
        refine ⟨23809544680276113386349701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15873029786850742257566467 23809544680276113386349701)
        ·
          refine ⟨4464289627551771259940569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23809544680276113386349701 4464289627551771259940569)
          ·
            refine ⟨3348217220663828444955427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4464289627551771259940569 3348217220663828444955427)
            ·
              refine ⟨5022325830995742667433141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348217220663828444955427 5022325830995742667433141)
              ·
                refine ⟨470843046655850875071857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5022325830995742667433141 470843046655850875071857)
                ·
                  refine ⟨353132284991888156303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470843046655850875071857 353132284991888156303893)
                  ·
                    rfl

theorem cell20_773688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_773688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773688 prefixEnd_773688 := by exact prefixLift 773688
  have htrace : WordTrace (prefixWord ++ tailWord_773688) baseStart_773688 baseEnd_773688 := by
    simpa [prefixWord, tailWord_773688, baseEnd_773688] using wordTrace_append hprefix tailTrace_773688
  have hstable : (prefixWord ++ tailWord_773688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773688).length < 2 ^ (prefixWord ++ tailWord_773688).sum := by decide
  have hdescent : baseEnd_773688 < baseStart_773688 := by decide
  rcases family_descends (prefixWord ++ tailWord_773688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773716 : List Nat := [2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_773716 : Nat := 118140960795 + 773716 * 2 ^ 59
def prefixEnd_773716 : Nat := 4983230072969 + 3 ^ 40 * 773716 * 2
def baseEnd_773716 : Nat := 117715021651614834456815

theorem tailTrace_773716 : CollatzResearch.WordTrace tailWord_773716 prefixEnd_773716 117715021651614834456815 := by
  unfold tailWord_773716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109870432483273508846501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18813160576644364678462001 14109870432483273508846501)
  ·
    refine ⟨2645600706090613782908719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14109870432483273508846501 2645600706090613782908719)
    ·
      refine ⟨3968401059135920674363079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645600706090613782908719 3968401059135920674363079)
      ·
        refine ⟨5952601588703881011544619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968401059135920674363079 5952601588703881011544619)
        ·
          refine ⟨8928902383055821517316929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952601588703881011544619 8928902383055821517316929)
          ·
            refine ⟨6696676787291866137987697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8928902383055821517316929 6696676787291866137987697)
            ·
              refine ⟨5022507590468899603490773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696676787291866137987697 5022507590468899603490773)
              ·
                refine ⟨117715021651614834456815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5022507590468899603490773 117715021651614834456815)
                ·
                  rfl

theorem cell20_773716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_773716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773716 prefixEnd_773716 := by exact prefixLift 773716
  have htrace : WordTrace (prefixWord ++ tailWord_773716) baseStart_773716 baseEnd_773716 := by
    simpa [prefixWord, tailWord_773716, baseEnd_773716] using wordTrace_append hprefix tailTrace_773716
  have hstable : (prefixWord ++ tailWord_773716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773716).length < 2 ^ (prefixWord ++ tailWord_773716).sum := by decide
  have hdescent : baseEnd_773716 < baseStart_773716 := by decide
  rcases family_descends (prefixWord ++ tailWord_773716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773719 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 3]
def baseStart_773719 : Nat := 118140960795 + 773719 * 2 ^ 59
def prefixEnd_773719 : Nat := 4983230072969 + 3 ^ 40 * 773719 * 2
def baseEnd_773719 : Nat := 353146434236589826270433

theorem tailTrace_773719 : CollatzResearch.WordTrace tailWord_773719 prefixEnd_773719 353146434236589826270433 := by
  unfold tailWord_773719
  simp only [CollatzResearch.WordTrace]
  refine ⟨28219850283955678530052211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18813233522637119020034807 28219850283955678530052211)
  ·
    refine ⟨42329775425933517795078317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28219850283955678530052211 42329775425933517795078317)
    ·
      refine ⟨15873665784725069173154369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42329775425933517795078317 15873665784725069173154369)
      ·
        refine ⟨11905249338543801879865777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15873665784725069173154369 11905249338543801879865777)
        ·
          refine ⟨8928937003907851409899333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11905249338543801879865777 8928937003907851409899333)
          ·
            refine ⟨1674175688232722139356125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8928937003907851409899333 1674175688232722139356125)
            ·
              refine ⟨627815883087270802258547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1674175688232722139356125 627815883087270802258547)
              ·
                refine ⟨941723824630906203387821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627815883087270802258547 941723824630906203387821)
                ·
                  refine ⟨353146434236589826270433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941723824630906203387821 353146434236589826270433)
                  ·
                    rfl

theorem cell20_773719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_773719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773719 prefixEnd_773719 := by exact prefixLift 773719
  have htrace : WordTrace (prefixWord ++ tailWord_773719) baseStart_773719 baseEnd_773719 := by
    simpa [prefixWord, tailWord_773719, baseEnd_773719] using wordTrace_append hprefix tailTrace_773719
  have hstable : (prefixWord ++ tailWord_773719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773719).length < 2 ^ (prefixWord ++ tailWord_773719).sum := by decide
  have hdescent : baseEnd_773719 < baseStart_773719 := by decide
  rcases family_descends (prefixWord ++ tailWord_773719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773733 : List Nat := [1, 3, 1, 3, 3, 1, 4, 4]
def baseStart_773733 : Nat := 118140960795 + 773733 * 2 ^ 59
def prefixEnd_773733 : Nat := 4983230072969 + 3 ^ 40 * 773733 * 2
def baseEnd_773733 : Nat := 117717608072689333267903

theorem tailTrace_773733 : CollatzResearch.WordTrace tailWord_773733 prefixEnd_773733 117717608072689333267903 := by
  unfold tailWord_773733
  simp only [CollatzResearch.WordTrace]
  refine ⟨28220360905904958921061853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18813573937269972614041235 28220360905904958921061853)
  ·
    refine ⟨10582635339714359595398195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28220360905904958921061853 10582635339714359595398195)
    ·
      refine ⟨15873953009571539393097293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10582635339714359595398195 15873953009571539393097293)
      ·
        refine ⟨5952732378589327272411485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15873953009571539393097293 5952732378589327272411485)
        ·
          refine ⟨2232274641970997727154307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5952732378589327272411485 2232274641970997727154307)
          ·
            refine ⟨3348411962956496590731461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232274641970997727154307 3348411962956496590731461)
            ·
              refine ⟨627827243054343110762149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3348411962956496590731461 627827243054343110762149)
              ·
                refine ⟨117717608072689333267903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627827243054343110762149 117717608072689333267903)
                ·
                  rfl

theorem cell20_773733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_773733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773733 prefixEnd_773733 := by exact prefixLift 773733
  have htrace : WordTrace (prefixWord ++ tailWord_773733) baseStart_773733 baseEnd_773733 := by
    simpa [prefixWord, tailWord_773733, baseEnd_773733] using wordTrace_append hprefix tailTrace_773733
  have hstable : (prefixWord ++ tailWord_773733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773733).length < 2 ^ (prefixWord ++ tailWord_773733).sum := by decide
  have hdescent : baseEnd_773733 < baseStart_773733 := by decide
  rcases family_descends (prefixWord ++ tailWord_773733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773774 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_773774 : Nat := 118140960795 + 773774 * 2 ^ 59
def prefixEnd_773774 : Nat := 4983230072969 + 3 ^ 40 * 773774 * 2
def baseEnd_773774 : Nat := 353171537735254079436875

theorem tailTrace_773774 : CollatzResearch.WordTrace tailWord_773774 prefixEnd_773774 353171537735254079436875 := by
  unfold tailWord_773774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527732037344552865413047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18814570865837615282202917 3527732037344552865413047)
  ·
    refine ⟨5291598056016829298119571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3527732037344552865413047 5291598056016829298119571)
    ·
      refine ⟨7937397084025243947179357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5291598056016829298119571 7937397084025243947179357)
      ·
        refine ⟨2976523906509466480192259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7937397084025243947179357 2976523906509466480192259)
        ·
          refine ⟨4464785859764199720288389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976523906509466480192259 4464785859764199720288389)
          ·
            refine ⟨837147348705787447554073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4464785859764199720288389 837147348705787447554073)
            ·
              refine ⟨627860511529340585665555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837147348705787447554073 627860511529340585665555)
              ·
                refine ⟨941790767294010878498333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627860511529340585665555 941790767294010878498333)
                ·
                  refine ⟨353171537735254079436875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941790767294010878498333 353171537735254079436875)
                  ·
                    rfl

theorem cell20_773774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_773774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773774 prefixEnd_773774 := by exact prefixLift 773774
  have htrace : WordTrace (prefixWord ++ tailWord_773774) baseStart_773774 baseEnd_773774 := by
    simpa [prefixWord, tailWord_773774, baseEnd_773774] using wordTrace_append hprefix tailTrace_773774
  have hstable : (prefixWord ++ tailWord_773774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773774).length < 2 ^ (prefixWord ++ tailWord_773774).sum := by decide
  have hdescent : baseEnd_773774 < baseStart_773774 := by decide
  rcases family_descends (prefixWord ++ tailWord_773774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773792 : List Nat := [2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_773792 : Nat := 118140960795 + 773792 * 2 ^ 59
def prefixEnd_773792 : Nat := 4983230072969 + 3 ^ 40 * 773792 * 2
def baseEnd_773792 : Nat := 117726584475242005612267

theorem tailTrace_773792 : CollatzResearch.WordTrace tailWord_773792 prefixEnd_773792 117726584475242005612267 := by
  unfold tailWord_773792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14111256406345605998729815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18815008541794141331639753 14111256406345605998729815)
  ·
    refine ⟨21166884609518408998094723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14111256406345605998729815 21166884609518408998094723)
    ·
      refine ⟨31750326914277613497142085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21166884609518408998094723 31750326914277613497142085)
      ·
        refine ⟨5953186296427052530714141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31750326914277613497142085 5953186296427052530714141)
        ·
          refine ⟨2232444861160144699017803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5953186296427052530714141 2232444861160144699017803)
          ·
            refine ⟨3348667291740217048526705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232444861160144699017803 3348667291740217048526705)
            ·
              refine ⟨2511500468805162786395029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3348667291740217048526705 2511500468805162786395029)
              ·
                refine ⟨117726584475242005612267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2511500468805162786395029 117726584475242005612267)
                ·
                  rfl

theorem cell20_773792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_773792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773792 prefixEnd_773792 := by exact prefixLift 773792
  have htrace : WordTrace (prefixWord ++ tailWord_773792) baseStart_773792 baseEnd_773792 := by
    simpa [prefixWord, tailWord_773792, baseEnd_773792] using wordTrace_append hprefix tailTrace_773792
  have hstable : (prefixWord ++ tailWord_773792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773792).length < 2 ^ (prefixWord ++ tailWord_773792).sum := by decide
  have hdescent : baseEnd_773792 < baseStart_773792 := by decide
  rcases family_descends (prefixWord ++ tailWord_773792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773857 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 2]
def baseStart_773857 : Nat := 118140960795 + 773857 * 2 ^ 59
def prefixEnd_773857 : Nat := 4983230072969 + 3 ^ 40 * 773857 * 2
def baseEnd_773857 : Nat := 353209421196874679669869

theorem tailTrace_773857 : CollatzResearch.WordTrace tailWord_773857 prefixEnd_773857 353209421196874679669869 := by
  unfold tailWord_773857
  simp only [CollatzResearch.WordTrace]
  refine ⟨28224883557455728098575825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18816589038303818732383883 28224883557455728098575825)
  ·
    refine ⟨21168662668091796073931869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28224883557455728098575825 21168662668091796073931869)
    ·
      refine ⟨7938248500534423527724451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21168662668091796073931869 7938248500534423527724451)
      ·
        refine ⟨11907372750801635291586677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938248500534423527724451 11907372750801635291586677)
        ·
          refine ⟨1116316195387653308586251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11907372750801635291586677 1116316195387653308586251)
          ·
            refine ⟨1674474293081479962879377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116316195387653308586251 1674474293081479962879377)
            ·
              refine ⟨1255855719811109972159533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674474293081479962879377 1255855719811109972159533)
              ·
                refine ⟨470945894929166239559825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255855719811109972159533 470945894929166239559825)
                ·
                  refine ⟨353209421196874679669869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470945894929166239559825 353209421196874679669869)
                  ·
                    rfl

theorem cell20_773857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_773857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773857 prefixEnd_773857 := by exact prefixLift 773857
  have htrace : WordTrace (prefixWord ++ tailWord_773857) baseStart_773857 baseEnd_773857 := by
    simpa [prefixWord, tailWord_773857, baseEnd_773857] using wordTrace_append hprefix tailTrace_773857
  have hstable : (prefixWord ++ tailWord_773857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773857).length < 2 ^ (prefixWord ++ tailWord_773857).sum := by decide
  have hdescent : baseEnd_773857 < baseStart_773857 := by decide
  rcases family_descends (prefixWord ++ tailWord_773857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773878 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_773878 : Nat := 118140960795 + 773878 * 2 ^ 59
def prefixEnd_773878 : Nat := 4983230072969 + 3 ^ 40 * 773878 * 2
def baseEnd_773878 : Nat := 353219006169091939969783

theorem tailTrace_773878 : CollatzResearch.WordTrace tailWord_773878 prefixEnd_773878 353219006169091939969783 := by
  unfold tailWord_773878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764103093148728042818143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18817099660253099123393525 1764103093148728042818143)
  ·
    refine ⟨2646154639723092064227215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764103093148728042818143 2646154639723092064227215)
    ·
      refine ⟨3969231959584638096340823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2646154639723092064227215 3969231959584638096340823)
      ·
        refine ⟨5953847939376957144511235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3969231959584638096340823 5953847939376957144511235)
        ·
          refine ⟨8930771909065435716766853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953847939376957144511235 8930771909065435716766853)
          ·
            refine ⟨1674519732949769196893785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8930771909065435716766853 1674519732949769196893785)
            ·
              refine ⟨1255889799712326897670339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674519732949769196893785 1255889799712326897670339)
              ·
                refine ⟨1883834699568490346505509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255889799712326897670339 1883834699568490346505509)
                ·
                  refine ⟨353219006169091939969783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883834699568490346505509 353219006169091939969783)
                  ·
                    rfl

theorem cell20_773878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_773878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773878 prefixEnd_773878 := by exact prefixLift 773878
  have htrace : WordTrace (prefixWord ++ tailWord_773878) baseStart_773878 baseEnd_773878 := by
    simpa [prefixWord, tailWord_773878, baseEnd_773878] using wordTrace_append hprefix tailTrace_773878
  have hstable : (prefixWord ++ tailWord_773878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773878).length < 2 ^ (prefixWord ++ tailWord_773878).sum := by decide
  have hdescent : baseEnd_773878 < baseStart_773878 := by decide
  rcases family_descends (prefixWord ++ tailWord_773878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773894 : List Nat := [6, 2, 2, 1, 1, 2, 2, 4]
def baseStart_773894 : Nat := 118140960795 + 773894 * 2 ^ 59
def prefixEnd_773894 : Nat := 4983230072969 + 3 ^ 40 * 773894 * 2
def baseEnd_773894 : Nat := 117742103001688998478795

theorem tailTrace_773894 : CollatzResearch.WordTrace tailWord_773894 prefixEnd_773894 117742103001688998478795 := by
  unfold tailWord_773894
  simp only [CollatzResearch.WordTrace]
  refine ⟨882069783072552606802273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18817488705547788945115157 882069783072552606802273)
  ·
    refine ⟨661552337304414455101705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 882069783072552606802273 661552337304414455101705)
    ·
      refine ⟨496164252978310841326279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 661552337304414455101705 496164252978310841326279)
      ·
        refine ⟨744246379467466261989419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496164252978310841326279 744246379467466261989419)
        ·
          refine ⟨1116369569201199392984129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744246379467466261989419 1116369569201199392984129)
          ·
            refine ⟨837277176900899544738097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116369569201199392984129 837277176900899544738097)
            ·
              refine ⟨627957882675674658553573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837277176900899544738097 627957882675674658553573)
              ·
                refine ⟨117742103001688998478795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627957882675674658553573 117742103001688998478795)
                ·
                  rfl

theorem cell20_773894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_773894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773894 prefixEnd_773894 := by exact prefixLift 773894
  have htrace : WordTrace (prefixWord ++ tailWord_773894) baseStart_773894 baseEnd_773894 := by
    simpa [prefixWord, tailWord_773894, baseEnd_773894] using wordTrace_append hprefix tailTrace_773894
  have hstable : (prefixWord ++ tailWord_773894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773894).length < 2 ^ (prefixWord ++ tailWord_773894).sum := by decide
  have hdescent : baseEnd_773894 < baseStart_773894 := by decide
  rcases family_descends (prefixWord ++ tailWord_773894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773908 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 2]
def baseStart_773908 : Nat := 118140960795 + 773908 * 2 ^ 59
def prefixEnd_773908 : Nat := 4983230072969 + 3 ^ 40 * 773908 * 2
def baseEnd_773908 : Nat := 353232698986545168969661

theorem tailTrace_773908 : CollatzResearch.WordTrace tailWord_773908 prefixEnd_773908 353232698986545168969661 := by
  unfold tailWord_773908
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113371840135481904341189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18817829120180642539121585 14113371840135481904341189)
  ·
    refine ⟨2646257220025402857063973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14113371840135481904341189 2646257220025402857063973)
    ·
      refine ⟨496173228754763035699495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2646257220025402857063973 496173228754763035699495)
      ·
        refine ⟨744259843132144553549243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496173228754763035699495 744259843132144553549243)
        ·
          refine ⟨1116389764698216830323865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744259843132144553549243 1116389764698216830323865)
          ·
            refine ⟨837292323523662622742899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116389764698216830323865 837292323523662622742899)
            ·
              refine ⟨1255938485285493934114349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837292323523662622742899 1255938485285493934114349)
              ·
                refine ⟨470976931982060225292881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255938485285493934114349 470976931982060225292881)
                ·
                  refine ⟨353232698986545168969661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470976931982060225292881 353232698986545168969661)
                  ·
                    rfl

theorem cell20_773908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_773908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773908 prefixEnd_773908 := by exact prefixLift 773908
  have htrace : WordTrace (prefixWord ++ tailWord_773908) baseStart_773908 baseEnd_773908 := by
    simpa [prefixWord, tailWord_773908, baseEnd_773908] using wordTrace_append hprefix tailTrace_773908
  have hstable : (prefixWord ++ tailWord_773908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773908).length < 2 ^ (prefixWord ++ tailWord_773908).sum := by decide
  have hdescent : baseEnd_773908 < baseStart_773908 := by decide
  rcases family_descends (prefixWord ++ tailWord_773908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773937 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_773937 : Nat := 118140960795 + 773937 * 2 ^ 59
def prefixEnd_773937 : Nat := 4983230072969 + 3 ^ 40 * 773937 * 2
def baseEnd_773937 : Nat := 353245935376749957002875

theorem tailTrace_773937 : CollatzResearch.WordTrace tailWord_773937 prefixEnd_773937 353245935376749957002875 := by
  unfold tailWord_773937
  simp only [CollatzResearch.WordTrace]
  refine ⟨28227801397165901761488065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18818534264777267840992043 28227801397165901761488065)
  ·
    refine ⟨21170851047874426321116049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28227801397165901761488065 21170851047874426321116049)
    ·
      refine ⟨15878138285905819740837037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21170851047874426321116049 15878138285905819740837037)
      ·
        refine ⟨5954301857214682402813889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15878138285905819740837037 5954301857214682402813889)
        ·
          refine ⟨4465726392911011802110417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954301857214682402813889 4465726392911011802110417)
          ·
            refine ⟨3349294794683258851582813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465726392911011802110417 3349294794683258851582813)
            ·
              refine ⟨1255985548006222069343555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3349294794683258851582813 1255985548006222069343555)
              ·
                refine ⟨1883978322009333104015333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255985548006222069343555 1883978322009333104015333)
                ·
                  refine ⟨353245935376749957002875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883978322009333104015333 353245935376749957002875)
                  ·
                    rfl

theorem cell20_773937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_773937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773937 prefixEnd_773937 := by exact prefixLift 773937
  have htrace : WordTrace (prefixWord ++ tailWord_773937) baseStart_773937 baseEnd_773937 := by
    simpa [prefixWord, tailWord_773937, baseEnd_773937] using wordTrace_append hprefix tailTrace_773937
  have hstable : (prefixWord ++ tailWord_773937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773937).length < 2 ^ (prefixWord ++ tailWord_773937).sum := by decide
  have hdescent : baseEnd_773937 < baseStart_773937 := by decide
  rcases family_descends (prefixWord ++ tailWord_773937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773944 : List Nat := [2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_773944 : Nat := 118140960795 + 773944 * 2 ^ 59
def prefixEnd_773944 : Nat := 4983230072969 + 3 ^ 40 * 773944 * 2
def baseEnd_773944 : Nat := 117749710122496347923171

theorem tailTrace_773944 : CollatzResearch.WordTrace tailWord_773944 prefixEnd_773944 117749710122496347923171 := by
  unfold tailWord_773944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114028354070270978496443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18818704472093694637995257 14114028354070270978496443)
  ·
    refine ⟨21171042531105406467744665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14114028354070270978496443 21171042531105406467744665)
    ·
      refine ⟨15878281898329054850808499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21171042531105406467744665 15878281898329054850808499)
      ·
        refine ⟨23817422847493582276212749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15878281898329054850808499 23817422847493582276212749)
        ·
          refine ⟨8931533567810093353579781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23817422847493582276212749 8931533567810093353579781)
          ·
            refine ⟨1674662543964392503796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8931533567810093353579781 1674662543964392503796209)
            ·
              refine ⟨1255996907973294377847157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674662543964392503796209 1255996907973294377847157)
              ·
                refine ⟨117749710122496347923171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1255996907973294377847157 117749710122496347923171)
                ·
                  rfl

theorem cell20_773944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_773944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773944 prefixEnd_773944 := by exact prefixLift 773944
  have htrace : WordTrace (prefixWord ++ tailWord_773944) baseStart_773944 baseEnd_773944 := by
    simpa [prefixWord, tailWord_773944, baseEnd_773944] using wordTrace_append hprefix tailTrace_773944
  have hstable : (prefixWord ++ tailWord_773944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773944).length < 2 ^ (prefixWord ++ tailWord_773944).sum := by decide
  have hdescent : baseEnd_773944 < baseStart_773944 := by decide
  rcases family_descends (prefixWord ++ tailWord_773944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773982 : List Nat := [4, 4, 12]
def baseStart_773982 : Nat := 118140960795 + 773982 * 2 ^ 59
def prefixEnd_773982 : Nat := 4983230072969 + 3 ^ 40 * 773982 * 2
def baseEnd_773982 : Nat := 484590500141193141979

theorem tailTrace_773982 : CollatzResearch.WordTrace tailWord_773982 prefixEnd_773982 484590500141193141979 := by
  unfold tailWord_773982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528680335250359305859525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18819628454668582964584133 3528680335250359305859525)
  ·
    refine ⟨661627562859442369848661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3528680335250359305859525 661627562859442369848661)
    ·
      refine ⟨484590500141193141979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 661627562859442369848661 484590500141193141979)
      ·
        rfl

theorem cell20_773982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 12].length) (baseStart_773982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773982 prefixEnd_773982 := by exact prefixLift 773982
  have htrace : WordTrace (prefixWord ++ tailWord_773982) baseStart_773982 baseEnd_773982 := by
    simpa [prefixWord, tailWord_773982, baseEnd_773982] using wordTrace_append hprefix tailTrace_773982
  have hstable : (prefixWord ++ tailWord_773982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773982).length < 2 ^ (prefixWord ++ tailWord_773982).sum := by decide
  have hdescent : baseEnd_773982 < baseStart_773982 := by decide
  rcases family_descends (prefixWord ++ tailWord_773982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773988 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 2]
def baseStart_773988 : Nat := 118140960795 + 773988 * 2 ^ 59
def prefixEnd_773988 : Nat := 4983230072969 + 3 ^ 40 * 773988 * 2
def baseEnd_773988 : Nat := 353269213166420446302667

theorem tailTrace_773988 : CollatzResearch.WordTrace tailWord_773988 prefixEnd_773988 353269213166420446302667 := by
  unfold tailWord_773988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114830759990568735797309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18819774346654091647729745 14114830759990568735797309)
  ·
    refine ⟨5293061534996463275923991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14114830759990568735797309 5293061534996463275923991)
    ·
      refine ⟨7939592302494694913885987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293061534996463275923991 7939592302494694913885987)
      ·
        refine ⟨11909388453742042370828981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939592302494694913885987 11909388453742042370828981)
        ·
          refine ⟨1116505167538316472265217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11909388453742042370828981 1116505167538316472265217)
          ·
            refine ⟨837378875653737354198913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116505167538316472265217 837378875653737354198913)
            ·
              refine ⟨628034156740303015649185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837378875653737354198913 628034156740303015649185)
              ·
                refine ⟨471025617555227261736889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628034156740303015649185 471025617555227261736889)
                ·
                  refine ⟨353269213166420446302667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471025617555227261736889 353269213166420446302667)
                  ·
                    rfl

theorem cell20_773988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_773988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773988 prefixEnd_773988 := by exact prefixLift 773988
  have htrace : WordTrace (prefixWord ++ tailWord_773988) baseStart_773988 baseEnd_773988 := by
    simpa [prefixWord, tailWord_773988, baseEnd_773988] using wordTrace_append hprefix tailTrace_773988
  have hstable : (prefixWord ++ tailWord_773988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773988).length < 2 ^ (prefixWord ++ tailWord_773988).sum := by decide
  have hdescent : baseEnd_773988 < baseStart_773988 := by decide
  rcases family_descends (prefixWord ++ tailWord_773988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773992 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 2]
def baseStart_773992 : Nat := 118140960795 + 773992 * 2 ^ 59
def prefixEnd_773992 : Nat := 4983230072969 + 3 ^ 40 * 773992 * 2
def baseEnd_773992 : Nat := 353271038875414210169317

theorem tailTrace_773992 : CollatzResearch.WordTrace tailWord_773992 prefixEnd_773992 353271038875414210169317 := by
  unfold tailWord_773992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114903705983323077370115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18819871607977764103160153 14114903705983323077370115)
  ·
    refine ⟨21172355558974984616055173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14114903705983323077370115 21172355558974984616055173)
    ·
      refine ⟨3969816667307809615510345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21172355558974984616055173 3969816667307809615510345)
      ·
        refine ⟨2977362500480857211632759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3969816667307809615510345 2977362500480857211632759)
        ·
          refine ⟨4466043750721285817449139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977362500480857211632759 4466043750721285817449139)
          ·
            refine ⟨6699065626081928726173709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466043750721285817449139 6699065626081928726173709)
            ·
              refine ⟨2512149609780723272315141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6699065626081928726173709 2512149609780723272315141)
              ·
                refine ⟨471028051833885613559089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2512149609780723272315141 471028051833885613559089)
                ·
                  refine ⟨353271038875414210169317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471028051833885613559089 353271038875414210169317)
                  ·
                    rfl

theorem cell20_773992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_773992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_773992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_773992 prefixEnd_773992 := by exact prefixLift 773992
  have htrace : WordTrace (prefixWord ++ tailWord_773992) baseStart_773992 baseEnd_773992 := by
    simpa [prefixWord, tailWord_773992, baseEnd_773992] using wordTrace_append hprefix tailTrace_773992
  have hstable : (prefixWord ++ tailWord_773992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773992).length < 2 ^ (prefixWord ++ tailWord_773992).sum := by decide
  have hdescent : baseEnd_773992 < baseStart_773992 := by decide
  rcases family_descends (prefixWord ++ tailWord_773992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774040 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_774040 : Nat := 118140960795 + 774040 * 2 ^ 59
def prefixEnd_774040 : Nat := 4983230072969 + 3 ^ 40 * 774040 * 2
def baseEnd_774040 : Nat := 353292947383339376569121

theorem tailTrace_774040 : CollatzResearch.WordTrace tailWord_774040 prefixEnd_774040 353292947383339376569121 := by
  unfold tailWord_774040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115779057896375176243787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18821038743861833568325049 14115779057896375176243787)
  ·
    refine ⟨21173668586844562764365681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14115779057896375176243787 21173668586844562764365681)
    ·
      refine ⟨15880251440133422073274261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21173668586844562764365681 15880251440133422073274261)
      ·
        refine ⟨744386786256254159684731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15880251440133422073274261 744386786256254159684731)
        ·
          refine ⟨1116580179384381239527097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744386786256254159684731 1116580179384381239527097)
          ·
            refine ⟨837435134538285929645323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116580179384381239527097 837435134538285929645323)
            ·
              refine ⟨1256152701807428894467985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837435134538285929645323 1256152701807428894467985)
              ·
                refine ⟨942114526355571670850989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256152701807428894467985 942114526355571670850989)
                ·
                  refine ⟨353292947383339376569121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942114526355571670850989 353292947383339376569121)
                  ·
                    rfl

theorem cell20_774040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_774040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774040 prefixEnd_774040 := by exact prefixLift 774040
  have htrace : WordTrace (prefixWord ++ tailWord_774040) baseStart_774040 baseEnd_774040 := by
    simpa [prefixWord, tailWord_774040, baseEnd_774040] using wordTrace_append hprefix tailTrace_774040
  have hstable : (prefixWord ++ tailWord_774040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774040).length < 2 ^ (prefixWord ++ tailWord_774040).sum := by decide
  have hdescent : baseEnd_774040 < baseStart_774040 := by decide
  rcases family_descends (prefixWord ++ tailWord_774040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774044 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_774044 : Nat := 118140960795 + 774044 * 2 ^ 59
def prefixEnd_774044 : Nat := 4983230072969 + 3 ^ 40 * 774044 * 2
def baseEnd_774044 : Nat := 353294773092333140435771

theorem tailTrace_774044 : CollatzResearch.WordTrace tailWord_774044 prefixEnd_774044 353294773092333140435771 := by
  unfold tailWord_774044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115852003889129517816593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18821136005185506023755457 14115852003889129517816593)
  ·
    refine ⟨10586889002916847138362445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14115852003889129517816593 10586889002916847138362445)
    ·
      refine ⟨3970083376093817676885917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10586889002916847138362445 3970083376093817676885917)
      ·
        refine ⟨1488781266035181628832219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3970083376093817676885917 1488781266035181628832219)
        ·
          refine ⟨2233171899052772443248329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488781266035181628832219 2233171899052772443248329)
          ·
            refine ⟨1674878924289579332436247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2233171899052772443248329 1674878924289579332436247)
            ·
              refine ⟨2512318386434368998654371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674878924289579332436247 2512318386434368998654371)
              ·
                refine ⟨3768477579651553497981557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512318386434368998654371 3768477579651553497981557)
                ·
                  refine ⟨353294773092333140435771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3768477579651553497981557 353294773092333140435771)
                  ·
                    rfl

theorem cell20_774044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_774044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774044 prefixEnd_774044 := by exact prefixLift 774044
  have htrace : WordTrace (prefixWord ++ tailWord_774044) baseStart_774044 baseEnd_774044 := by
    simpa [prefixWord, tailWord_774044, baseEnd_774044] using wordTrace_append hprefix tailTrace_774044
  have hstable : (prefixWord ++ tailWord_774044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774044).length < 2 ^ (prefixWord ++ tailWord_774044).sum := by decide
  have hdescent : baseEnd_774044 < baseStart_774044 := by decide
  rcases family_descends (prefixWord ++ tailWord_774044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774072 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_774072 : Nat := 118140960795 + 774072 * 2 ^ 59
def prefixEnd_774072 : Nat := 4983230072969 + 3 ^ 40 * 774072 * 2
def baseEnd_774072 : Nat := 353307553055289487502323

theorem tailTrace_774072 : CollatzResearch.WordTrace tailWord_774072 prefixEnd_774072 353307553055289487502323 := by
  unfold tailWord_774072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116362625838409908826235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18821816834451213211768313 14116362625838409908826235)
  ·
    refine ⟨21174543938757614863239353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14116362625838409908826235 21174543938757614863239353)
    ·
      refine ⟨15880907954068211147429515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21174543938757614863239353 15880907954068211147429515)
      ·
        refine ⟨23821361931102316721144273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15880907954068211147429515 23821361931102316721144273)
        ·
          refine ⟨17866021448326737540858205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23821361931102316721144273 17866021448326737540858205)
          ·
            refine ⟨6699758043122526577821827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17866021448326737540858205 6699758043122526577821827)
            ·
              refine ⟨10049637064683789866732741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699758043122526577821827 10049637064683789866732741)
              ·
                refine ⟨1884306949628210600012389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10049637064683789866732741 1884306949628210600012389)
                ·
                  refine ⟨353307553055289487502323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1884306949628210600012389 353307553055289487502323)
                  ·
                    rfl

theorem cell20_774072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_774072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774072 prefixEnd_774072 := by exact prefixLift 774072
  have htrace : WordTrace (prefixWord ++ tailWord_774072) baseStart_774072 baseEnd_774072 := by
    simpa [prefixWord, tailWord_774072, baseEnd_774072] using wordTrace_append hprefix tailTrace_774072
  have hstable : (prefixWord ++ tailWord_774072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774072).length < 2 ^ (prefixWord ++ tailWord_774072).sum := by decide
  have hdescent : baseEnd_774072 < baseStart_774072 := by decide
  rcases family_descends (prefixWord ++ tailWord_774072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774079 : List Nat := [1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_774079 : Nat := 118140960795 + 774079 * 2 ^ 59
def prefixEnd_774079 : Nat := 4983230072969 + 3 ^ 40 * 774079 * 2
def baseEnd_774079 : Nat := 117770249348676191422987

theorem tailTrace_774079 : CollatzResearch.WordTrace tailWord_774079 prefixEnd_774079 117770249348676191422987 := by
  unfold tailWord_774079
  simp only [CollatzResearch.WordTrace]
  refine ⟨28232980562651460013157291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18821987041767640008771527 28232980562651460013157291)
  ·
    refine ⟨42349470843977190019735937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28232980562651460013157291 42349470843977190019735937)
    ·
      refine ⟨31762103132982892514801953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42349470843977190019735937 31762103132982892514801953)
      ·
        refine ⟨23821577349737169386101465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31762103132982892514801953 23821577349737169386101465)
        ·
          refine ⟨17866183012302877039576099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23821577349737169386101465 17866183012302877039576099)
          ·
            refine ⟨26799274518454315559364149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17866183012302877039576099 26799274518454315559364149)
            ·
              refine ⟨2512431986105092083690389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26799274518454315559364149 2512431986105092083690389)
              ·
                refine ⟨117770249348676191422987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2512431986105092083690389 117770249348676191422987)
                ·
                  rfl

theorem cell20_774079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_774079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774079 prefixEnd_774079 := by exact prefixLift 774079
  have htrace : WordTrace (prefixWord ++ tailWord_774079) baseStart_774079 baseEnd_774079 := by
    simpa [prefixWord, tailWord_774079, baseEnd_774079] using wordTrace_append hprefix tailTrace_774079
  have hstable : (prefixWord ++ tailWord_774079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774079).length < 2 ^ (prefixWord ++ tailWord_774079).sum := by decide
  have hdescent : baseEnd_774079 < baseStart_774079 := by decide
  rcases family_descends (prefixWord ++ tailWord_774079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774102 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_774102 : Nat := 118140960795 + 774102 * 2 ^ 59
def prefixEnd_774102 : Nat := 4983230072969 + 3 ^ 40 * 774102 * 2
def baseEnd_774102 : Nat := 353321245872742716502201

theorem tailTrace_774102 : CollatzResearch.WordTrace tailWord_774102 prefixEnd_774102 353321245872742716502201 := by
  unfold tailWord_774102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764613715098008433827785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18822546294378756627496373 1764613715098008433827785)
  ·
    refine ⟨1323460286323506325370839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1764613715098008433827785 1323460286323506325370839)
    ·
      refine ⟨1985190429485259488056259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323460286323506325370839 1985190429485259488056259)
      ·
        refine ⟨2977785644227889232084389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985190429485259488056259 2977785644227889232084389)
        ·
          refine ⟨558334808292729231015823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2977785644227889232084389 558334808292729231015823)
          ·
            refine ⟨837502212439093846523735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558334808292729231015823 837502212439093846523735)
            ·
              refine ⟨1256253318658640769785603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837502212439093846523735 1256253318658640769785603)
              ·
                refine ⟨1884379977987961154678405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256253318658640769785603 1884379977987961154678405)
                ·
                  refine ⟨353321245872742716502201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1884379977987961154678405 353321245872742716502201)
                  ·
                    rfl

theorem cell20_774102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_774102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774102 prefixEnd_774102 := by exact prefixLift 774102
  have htrace : WordTrace (prefixWord ++ tailWord_774102) baseStart_774102 baseEnd_774102 := by
    simpa [prefixWord, tailWord_774102, baseEnd_774102] using wordTrace_append hprefix tailTrace_774102
  have hstable : (prefixWord ++ tailWord_774102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774102).length < 2 ^ (prefixWord ++ tailWord_774102).sum := by decide
  have hdescent : baseEnd_774102 < baseStart_774102 := by decide
  rcases family_descends (prefixWord ++ tailWord_774102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774103 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_774103 : Nat := 118140960795 + 774103 * 2 ^ 59
def prefixEnd_774103 : Nat := 4983230072969 + 3 ^ 40 * 774103 * 2
def baseEnd_774103 : Nat := 353321702299991157468863

theorem tailTrace_774103 : CollatzResearch.WordTrace tailWord_774103 prefixEnd_774103 353321702299991157468863 := by
  unfold tailWord_774103
  simp only [CollatzResearch.WordTrace]
  refine ⟨28233855914564512112030963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18822570609709674741353975 28233855914564512112030963)
  ·
    refine ⟨42350783871846768168046445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28233855914564512112030963 42350783871846768168046445)
    ·
      refine ⟨15881543951942538063017417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42350783871846768168046445 15881543951942538063017417)
      ·
        refine ⟨11911157963956903547263063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15881543951942538063017417 11911157963956903547263063)
        ·
          refine ⟨17866736945935355320894595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11911157963956903547263063 17866736945935355320894595)
          ·
            refine ⟨26800105418903032981341893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17866736945935355320894595 26800105418903032981341893)
            ·
              refine ⟨5025019766044318684001605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26800105418903032981341893 5025019766044318684001605)
              ·
                refine ⟨942191206133309753250301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5025019766044318684001605 942191206133309753250301)
                ·
                  refine ⟨353321702299991157468863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942191206133309753250301 353321702299991157468863)
                  ·
                    rfl

theorem cell20_774103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_774103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774103 prefixEnd_774103 := by exact prefixLift 774103
  have htrace : WordTrace (prefixWord ++ tailWord_774103) baseStart_774103 baseEnd_774103 := by
    simpa [prefixWord, tailWord_774103, baseEnd_774103] using wordTrace_append hprefix tailTrace_774103
  have hstable : (prefixWord ++ tailWord_774103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774103).length < 2 ^ (prefixWord ++ tailWord_774103).sum := by decide
  have hdescent : baseEnd_774103 < baseStart_774103 := by decide
  rcases family_descends (prefixWord ++ tailWord_774103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774106 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_774106 : Nat := 118140960795 + 774106 * 2 ^ 59
def prefixEnd_774106 : Nat := 4983230072969 + 3 ^ 40 * 774106 * 2
def baseEnd_774106 : Nat := 353323071581736480368851

theorem tailTrace_774106 : CollatzResearch.WordTrace tailWord_774106 prefixEnd_774106 353323071581736480368851 := by
  unfold tailWord_774106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7058491333388410906097543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18822643555702429082926781 7058491333388410906097543)
  ·
    refine ⟨10587737000082616359146315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7058491333388410906097543 10587737000082616359146315)
    ·
      refine ⟨15881605500123924538719473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10587737000082616359146315 15881605500123924538719473)
      ·
        refine ⟨11911204125092943404039605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15881605500123924538719473 11911204125092943404039605)
        ·
          refine ⟨1116675386727463444128713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11911204125092943404039605 1116675386727463444128713)
          ·
            refine ⟨837506540045597583096535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116675386727463444128713 837506540045597583096535)
            ·
              refine ⟨1256259810068396374644803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837506540045597583096535 1256259810068396374644803)
              ·
                refine ⟨1884389715102594561967205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256259810068396374644803 1884389715102594561967205)
                ·
                  refine ⟨353323071581736480368851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1884389715102594561967205 353323071581736480368851)
                  ·
                    rfl

theorem cell20_774106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_774106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774106 prefixEnd_774106 := by exact prefixLift 774106
  have htrace : WordTrace (prefixWord ++ tailWord_774106) baseStart_774106 baseEnd_774106 := by
    simpa [prefixWord, tailWord_774106, baseEnd_774106] using wordTrace_append hprefix tailTrace_774106
  have hstable : (prefixWord ++ tailWord_774106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774106).length < 2 ^ (prefixWord ++ tailWord_774106).sum := by decide
  have hdescent : baseEnd_774106 < baseStart_774106 := by decide
  rcases family_descends (prefixWord ++ tailWord_774106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774150 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_774150 : Nat := 118140960795 + 774150 * 2 ^ 59
def prefixEnd_774150 : Nat := 4983230072969 + 3 ^ 40 * 774150 * 2
def baseEnd_774150 : Nat := 353343154380667882902005

theorem tailTrace_774150 : CollatzResearch.WordTrace tailWord_774150 prefixEnd_774150 353343154380667882902005 := by
  unfold tailWord_774150
  simp only [CollatzResearch.WordTrace]
  refine ⟨882361567043569973093497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18823713430262826092661269 882361567043569973093497)
  ·
    refine ⟨661771175282677479820123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 882361567043569973093497 661771175282677479820123)
    ·
      refine ⟨992656762924016219730185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661771175282677479820123 992656762924016219730185)
      ·
        refine ⟨744492572193012164797639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992656762924016219730185 744492572193012164797639)
        ·
          refine ⟨1116738858289518247196459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744492572193012164797639 1116738858289518247196459)
          ·
            refine ⟨1675108287434277370794689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116738858289518247196459 1675108287434277370794689)
            ·
              refine ⟨1256331215575708028096017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675108287434277370794689 1256331215575708028096017)
              ·
                refine ⟨942248411681781021072013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256331215575708028096017 942248411681781021072013)
                ·
                  refine ⟨353343154380667882902005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942248411681781021072013 353343154380667882902005)
                  ·
                    rfl

theorem cell20_774150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_774150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774150 prefixEnd_774150 := by exact prefixLift 774150
  have htrace : WordTrace (prefixWord ++ tailWord_774150) baseStart_774150 baseEnd_774150 := by
    simpa [prefixWord, tailWord_774150, baseEnd_774150] using wordTrace_append hprefix tailTrace_774150
  have hstable : (prefixWord ++ tailWord_774150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774150).length < 2 ^ (prefixWord ++ tailWord_774150).sum := by decide
  have hdescent : baseEnd_774150 < baseStart_774150 := by decide
  rcases family_descends (prefixWord ++ tailWord_774150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774157 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 2]
def baseStart_774157 : Nat := 118140960795 + 774157 * 2 ^ 59
def prefixEnd_774157 : Nat := 4983230072969 + 3 ^ 40 * 774157 * 2
def baseEnd_774157 : Nat := 353346349371406969668643

theorem tailTrace_774157 : CollatzResearch.WordTrace tailWord_774157 prefixEnd_774157 353346349371406969668643 := by
  unfold tailWord_774157
  simp only [CollatzResearch.WordTrace]
  refine ⟨28235825456368879334496725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18823883637579252889664483 28235825456368879334496725)
  ·
    refine ⟨661777159133645609402267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28235825456368879334496725 661777159133645609402267)
    ·
      refine ⟨992665738700468414103401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661777159133645609402267 992665738700468414103401)
      ·
        refine ⟨744499304025351310577551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992665738700468414103401 744499304025351310577551)
        ·
          refine ⟨1116748956038026965866327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744499304025351310577551 1116748956038026965866327)
          ·
            refine ⟨1675123434057040448799491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116748956038026965866327 1675123434057040448799491)
            ·
              refine ⟨2512685151085560673199237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675123434057040448799491 2512685151085560673199237)
              ·
                refine ⟨471128465828542626224857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2512685151085560673199237 471128465828542626224857)
                ·
                  refine ⟨353346349371406969668643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471128465828542626224857 353346349371406969668643)
                  ·
                    rfl

theorem cell20_774157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_774157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774157 prefixEnd_774157 := by exact prefixLift 774157
  have htrace : WordTrace (prefixWord ++ tailWord_774157) baseStart_774157 baseEnd_774157 := by
    simpa [prefixWord, tailWord_774157, baseEnd_774157] using wordTrace_append hprefix tailTrace_774157
  have hstable : (prefixWord ++ tailWord_774157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774157).length < 2 ^ (prefixWord ++ tailWord_774157).sum := by decide
  have hdescent : baseEnd_774157 < baseStart_774157 := by decide
  rcases family_descends (prefixWord ++ tailWord_774157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774158 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_774158 : Nat := 118140960795 + 774158 * 2 ^ 59
def prefixEnd_774158 : Nat := 4983230072969 + 3 ^ 40 * 774158 * 2
def baseEnd_774158 : Nat := 353346805798655410635305

theorem tailTrace_774158 : CollatzResearch.WordTrace tailWord_774158 prefixEnd_774158 353346805798655410635305 := by
  unfold tailWord_774158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3529482741170657063160391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18823907952910171003522085 3529482741170657063160391)
  ·
    refine ⟨5294224111755985594740587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3529482741170657063160391 5294224111755985594740587)
    ·
      refine ⟨7941336167633978392110881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5294224111755985594740587 7941336167633978392110881)
      ·
        refine ⟨5956002125725483794083161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7941336167633978392110881 5956002125725483794083161)
        ·
          refine ⟨4467001594294112845562371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5956002125725483794083161 4467001594294112845562371)
          ·
            refine ⟨6700502391441169268343557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467001594294112845562371 6700502391441169268343557)
            ·
              refine ⟨1256344198395219237814417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6700502391441169268343557 1256344198395219237814417)
              ·
                refine ⟨942258148796414428360813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256344198395219237814417 942258148796414428360813)
                ·
                  refine ⟨353346805798655410635305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942258148796414428360813 353346805798655410635305)
                  ·
                    rfl

theorem cell20_774158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_774158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774158 prefixEnd_774158 := by exact prefixLift 774158
  have htrace : WordTrace (prefixWord ++ tailWord_774158) baseStart_774158 baseEnd_774158 := by
    simpa [prefixWord, tailWord_774158, baseEnd_774158] using wordTrace_append hprefix tailTrace_774158
  have hstable : (prefixWord ++ tailWord_774158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774158).length < 2 ^ (prefixWord ++ tailWord_774158).sum := by decide
  have hdescent : baseEnd_774158 < baseStart_774158 := by decide
  rcases family_descends (prefixWord ++ tailWord_774158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774172 : List Nat := [2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_774172 : Nat := 118140960795 + 774172 * 2 ^ 59
def prefixEnd_774172 : Nat := 4983230072969 + 3 ^ 40 * 774172 * 2
def baseEnd_774172 : Nat := 117784398593377861389527

theorem tailTrace_774172 : CollatzResearch.WordTrace tailWord_774172 prefixEnd_774172 117784398593377861389527 := by
  unfold tailWord_774172
  simp only [CollatzResearch.WordTrace]
  refine ⟨14118186275657268448146385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18824248367543024597528513 14118186275657268448146385)
  ·
    refine ⟨10588639706742951336109789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14118186275657268448146385 10588639706742951336109789)
    ·
      refine ⟨3970739890028606751041171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10588639706742951336109789 3970739890028606751041171)
      ·
        refine ⟨5956109835042910126561757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3970739890028606751041171 5956109835042910126561757)
        ·
          refine ⟨2233541188141091297460659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5956109835042910126561757 2233541188141091297460659)
          ·
            refine ⟨3350311782211636946190989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233541188141091297460659 3350311782211636946190989)
            ·
              refine ⟨1256366918329363854821621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3350311782211636946190989 1256366918329363854821621)
              ·
                refine ⟨117784398593377861389527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1256366918329363854821621 117784398593377861389527)
                ·
                  rfl

theorem cell20_774172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_774172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774172 prefixEnd_774172 := by exact prefixLift 774172
  have htrace : WordTrace (prefixWord ++ tailWord_774172) baseStart_774172 baseEnd_774172 := by
    simpa [prefixWord, tailWord_774172, baseEnd_774172] using wordTrace_append hprefix tailTrace_774172
  have hstable : (prefixWord ++ tailWord_774172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774172).length < 2 ^ (prefixWord ++ tailWord_774172).sum := by decide
  have hdescent : baseEnd_774172 < baseStart_774172 := by decide
  rcases family_descends (prefixWord ++ tailWord_774172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774179 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_774179 : Nat := 118140960795 + 774179 * 2 ^ 59
def prefixEnd_774179 : Nat := 4983230072969 + 3 ^ 40 * 774179 * 2
def baseEnd_774179 : Nat := 353356390770872670935219

theorem tailTrace_774179 : CollatzResearch.WordTrace tailWord_774179 prefixEnd_774179 353356390770872670935219 := by
  unfold tailWord_774179
  simp only [CollatzResearch.WordTrace]
  refine ⟨28236627862289177091797591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18824418574859451394531727 28236627862289177091797591)
  ·
    refine ⟨42354941793433765637696387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28236627862289177091797591 42354941793433765637696387)
    ·
      refine ⟨63532412690150648456544581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42354941793433765637696387 63532412690150648456544581)
      ·
        refine ⟨11912327379403246585602109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63532412690150648456544581 11912327379403246585602109)
        ·
          refine ⟨4467122767276217469600791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11912327379403246585602109 4467122767276217469600791)
          ·
            refine ⟨6700684150914326204401187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467122767276217469600791 6700684150914326204401187)
            ·
              refine ⟨10051026226371489306601781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700684150914326204401187 10051026226371489306601781)
              ·
                refine ⟨942283708722327122493917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10051026226371489306601781 942283708722327122493917)
                ·
                  refine ⟨353356390770872670935219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942283708722327122493917 353356390770872670935219)
                  ·
                    rfl

theorem cell20_774179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_774179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774179 prefixEnd_774179 := by exact prefixLift 774179
  have htrace : WordTrace (prefixWord ++ tailWord_774179) baseStart_774179 baseEnd_774179 := by
    simpa [prefixWord, tailWord_774179, baseEnd_774179] using wordTrace_append hprefix tailTrace_774179
  have hstable : (prefixWord ++ tailWord_774179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774179).length < 2 ^ (prefixWord ++ tailWord_774179).sum := by decide
  have hdescent : baseEnd_774179 < baseStart_774179 := by decide
  rcases family_descends (prefixWord ++ tailWord_774179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774234 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_774234 : Nat := 118140960795 + 774234 * 2 ^ 59
def prefixEnd_774234 : Nat := 4983230072969 + 3 ^ 40 * 774234 * 2
def baseEnd_774234 : Nat := 353381494269536924101661

theorem tailTrace_774234 : CollatzResearch.WordTrace tailWord_774234 prefixEnd_774234 353381494269536924101661 := by
  unfold tailWord_774234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059658469272480371262439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18825755918059947656699837 7059658469272480371262439)
  ·
    refine ⟨10589487703908720556893659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7059658469272480371262439 10589487703908720556893659)
    ·
      refine ⟨15884231555863080835340489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10589487703908720556893659 15884231555863080835340489)
      ·
        refine ⟨11913173666897310626505367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15884231555863080835340489 11913173666897310626505367)
        ·
          refine ⟨17869760500345965939758051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11913173666897310626505367 17869760500345965939758051)
          ·
            refine ⟨26804640750518948909637077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17869760500345965939758051 26804640750518948909637077)
            ·
              refine ⟨628233767590287865069619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26804640750518948909637077 628233767590287865069619)
              ·
                refine ⟨942350651385431797604429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628233767590287865069619 942350651385431797604429)
                ·
                  refine ⟨353381494269536924101661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942350651385431797604429 353381494269536924101661)
                  ·
                    rfl

theorem cell20_774234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_774234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774234 prefixEnd_774234 := by exact prefixLift 774234
  have htrace : WordTrace (prefixWord ++ tailWord_774234) baseStart_774234 baseEnd_774234 := by
    simpa [prefixWord, tailWord_774234, baseEnd_774234] using wordTrace_append hprefix tailTrace_774234
  have hstable : (prefixWord ++ tailWord_774234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774234).length < 2 ^ (prefixWord ++ tailWord_774234).sum := by decide
  have hdescent : baseEnd_774234 < baseStart_774234 := by decide
  rcases family_descends (prefixWord ++ tailWord_774234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774258 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_774258 : Nat := 118140960795 + 774258 * 2 ^ 59
def prefixEnd_774258 : Nat := 4983230072969 + 3 ^ 40 * 774258 * 2
def baseEnd_774258 : Nat := 353392448523499507301563

theorem tailTrace_774258 : CollatzResearch.WordTrace tailWord_774258 prefixEnd_774258 353392448523499507301563 := by
  unfold tailWord_774258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059877307250743395980857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18826339486001982389282285 7059877307250743395980857)
  ·
    refine ⟨5294907980438057546985643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7059877307250743395980857 5294907980438057546985643)
    ·
      refine ⟨7942361970657086320478465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5294907980438057546985643 7942361970657086320478465)
      ·
        refine ⟨5956771477992814740358849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7942361970657086320478465 5956771477992814740358849)
        ·
          refine ⟨4467578608494611055269137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5956771477992814740358849 4467578608494611055269137)
          ·
            refine ⟨3350683956370958291451853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4467578608494611055269137 3350683956370958291451853)
            ·
              refine ⟨1256506483639109359294445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3350683956370958291451853 1256506483639109359294445)
              ·
                refine ⟨471189931364666009735417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1256506483639109359294445 471189931364666009735417)
                ·
                  refine ⟨353392448523499507301563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471189931364666009735417 353392448523499507301563)
                  ·
                    rfl

theorem cell20_774258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_774258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774258 prefixEnd_774258 := by exact prefixLift 774258
  have htrace : WordTrace (prefixWord ++ tailWord_774258) baseStart_774258 baseEnd_774258 := by
    simpa [prefixWord, tailWord_774258, baseEnd_774258] using wordTrace_append hprefix tailTrace_774258
  have hstable : (prefixWord ++ tailWord_774258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774258).length < 2 ^ (prefixWord ++ tailWord_774258).sum := by decide
  have hdescent : baseEnd_774258 < baseStart_774258 := by decide
  rcases family_descends (prefixWord ++ tailWord_774258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774269 : List Nat := [1, 4, 1, 1, 3, 2, 8]
def baseStart_774269 : Nat := 118140960795 + 774269 * 2 ^ 59
def prefixEnd_774269 : Nat := 4983230072969 + 3 ^ 40 * 774269 * 2
def baseEnd_774269 : Nat := 39266385469248039770539

theorem tailTrace_774269 : CollatzResearch.WordTrace tailWord_774269 prefixEnd_774269 39266385469248039770539 := by
  unfold tailWord_774269
  simp only [CollatzResearch.WordTrace]
  refine ⟨28239910431963122462573861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18826606954642081641715907 28239910431963122462573861)
  ·
    refine ⟨5294983205993085461732599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28239910431963122462573861 5294983205993085461732599)
    ·
      refine ⟨7942474808989628192598899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5294983205993085461732599 7942474808989628192598899)
      ·
        refine ⟨11913712213484442288898349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7942474808989628192598899 11913712213484442288898349)
        ·
          refine ⟨4467642080056665858336881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11913712213484442288898349 4467642080056665858336881)
          ·
            refine ⟨3350731560042499393752661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4467642080056665858336881 3350731560042499393752661)
            ·
              refine ⟨39266385469248039770539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3350731560042499393752661 39266385469248039770539)
              ·
                rfl

theorem cell20_774269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_774269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774269 prefixEnd_774269 := by exact prefixLift 774269
  have htrace : WordTrace (prefixWord ++ tailWord_774269) baseStart_774269 baseEnd_774269 := by
    simpa [prefixWord, tailWord_774269, baseEnd_774269] using wordTrace_append hprefix tailTrace_774269
  have hstable : (prefixWord ++ tailWord_774269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774269).length < 2 ^ (prefixWord ++ tailWord_774269).sum := by decide
  have hdescent : baseEnd_774269 < baseStart_774269 := by decide
  rcases family_descends (prefixWord ++ tailWord_774269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774279 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 2]
def baseStart_774279 : Nat := 118140960795 + 774279 * 2 ^ 59
def prefixEnd_774279 : Nat := 4983230072969 + 3 ^ 40 * 774279 * 2
def baseEnd_774279 : Nat := 353402033495716767601477

theorem tailTrace_774279 : CollatzResearch.WordTrace tailWord_774279 prefixEnd_774279 353402033495716767601477 := by
  unfold tailWord_774279
  simp only [CollatzResearch.WordTrace]
  refine ⟨28240275161926894170437891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18826850107951262780291927 28240275161926894170437891)
  ·
    refine ⟨42360412742890341255656837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28240275161926894170437891 42360412742890341255656837)
    ·
      refine ⟨7942577389291938985435657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42360412742890341255656837 7942577389291938985435657)
      ·
        refine ⟨5956933041968954239076743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7942577389291938985435657 5956933041968954239076743)
        ·
          refine ⟨8935399562953431358615115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956933041968954239076743 8935399562953431358615115)
          ·
            refine ⟨13403099344430147037922673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8935399562953431358615115 13403099344430147037922673)
            ·
              refine ⟨10052324508322610278442005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13403099344430147037922673 10052324508322610278442005)
              ·
                refine ⟨471202711327622356801969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10052324508322610278442005 471202711327622356801969)
                ·
                  refine ⟨353402033495716767601477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471202711327622356801969 353402033495716767601477)
                  ·
                    rfl

theorem cell20_774279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 2].length) (baseStart_774279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774279 prefixEnd_774279 := by exact prefixLift 774279
  have htrace : WordTrace (prefixWord ++ tailWord_774279) baseStart_774279 baseEnd_774279 := by
    simpa [prefixWord, tailWord_774279, baseEnd_774279] using wordTrace_append hprefix tailTrace_774279
  have hstable : (prefixWord ++ tailWord_774279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774279).length < 2 ^ (prefixWord ++ tailWord_774279).sum := by decide
  have hdescent : baseEnd_774279 < baseStart_774279 := by decide
  rcases family_descends (prefixWord ++ tailWord_774279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774293 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_774293 : Nat := 118140960795 + 774293 * 2 ^ 59
def prefixEnd_774293 : Nat := 4983230072969 + 3 ^ 40 * 774293 * 2
def baseEnd_774293 : Nat := 353408423477194941134753

theorem tailTrace_774293 : CollatzResearch.WordTrace tailWord_774293 prefixEnd_774293 353408423477194941134753 := by
  unfold tailWord_774293
  simp only [CollatzResearch.WordTrace]
  refine ⟨28240785783876174561447533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18827190522584116374298355 28240785783876174561447533)
  ·
    refine ⟨10590294668953565460542825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28240785783876174561447533 10590294668953565460542825)
    ·
      refine ⟨7942721001715174095407119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10590294668953565460542825 7942721001715174095407119)
      ·
        refine ⟨11914081502572761143110679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7942721001715174095407119 11914081502572761143110679)
        ·
          refine ⟨17871122253859141714666019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11914081502572761143110679 17871122253859141714666019)
          ·
            refine ⟨26806683380788712571999029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17871122253859141714666019 26806683380788712571999029)
            ·
              refine ⟨2513126566948941803624909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26806683380788712571999029 2513126566948941803624909)
              ·
                refine ⟨942422462605853176359341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2513126566948941803624909 942422462605853176359341)
                ·
                  refine ⟨353408423477194941134753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942422462605853176359341 353408423477194941134753)
                  ·
                    rfl

theorem cell20_774293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_774293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774293 prefixEnd_774293 := by exact prefixLift 774293
  have htrace : WordTrace (prefixWord ++ tailWord_774293) baseStart_774293 baseEnd_774293 := by
    simpa [prefixWord, tailWord_774293, baseEnd_774293] using wordTrace_append hprefix tailTrace_774293
  have hstable : (prefixWord ++ tailWord_774293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774293).length < 2 ^ (prefixWord ++ tailWord_774293).sum := by decide
  have hdescent : baseEnd_774293 < baseStart_774293 := by decide
  rcases family_descends (prefixWord ++ tailWord_774293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774300 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_774300 : Nat := 118140960795 + 774300 * 2 ^ 59
def prefixEnd_774300 : Nat := 4983230072969 + 3 ^ 40 * 774300 * 2
def baseEnd_774300 : Nat := 353411618467934027901391

theorem tailTrace_774300 : CollatzResearch.WordTrace tailWord_774300 prefixEnd_774300 353411618467934027901391 := by
  unfold tailWord_774300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120520547425407378476177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18827360729900543171301569 14120520547425407378476177)
  ·
    refine ⟨10590390410569055533857133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14120520547425407378476177 10590390410569055533857133)
    ·
      refine ⟨3971396403963395825196425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10590390410569055533857133 3971396403963395825196425)
      ·
        refine ⟨2978547302972546868897319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3971396403963395825196425 2978547302972546868897319)
        ·
          refine ⟨4467820954458820303345979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978547302972546868897319 4467820954458820303345979)
          ·
            refine ⟨6701731431688230455018969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467820954458820303345979 6701731431688230455018969)
            ·
              refine ⟨5026298573766172841264227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6701731431688230455018969 5026298573766172841264227)
              ·
                refine ⟨7539447860649259261896341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026298573766172841264227 7539447860649259261896341)
                ·
                  refine ⟨353411618467934027901391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7539447860649259261896341 353411618467934027901391)
                  ·
                    rfl

theorem cell20_774300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_774300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774300 prefixEnd_774300 := by exact prefixLift 774300
  have htrace : WordTrace (prefixWord ++ tailWord_774300) baseStart_774300 baseEnd_774300 := by
    simpa [prefixWord, tailWord_774300, baseEnd_774300] using wordTrace_append hprefix tailTrace_774300
  have hstable : (prefixWord ++ tailWord_774300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774300).length < 2 ^ (prefixWord ++ tailWord_774300).sum := by decide
  have hdescent : baseEnd_774300 < baseStart_774300 := by decide
  rcases family_descends (prefixWord ++ tailWord_774300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774331 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_774331 : Nat := 118140960795 + 774331 * 2 ^ 59
def prefixEnd_774331 : Nat := 4983230072969 + 3 ^ 40 * 774331 * 2
def baseEnd_774331 : Nat := 353425767712635697867931

theorem tailTrace_774331 : CollatzResearch.WordTrace tailWord_774331 prefixEnd_774331 353425767712635697867931 := by
  unfold tailWord_774331
  simp only [CollatzResearch.WordTrace]
  refine ⟨28242171757738507051330847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18828114505159004700887231 28242171757738507051330847)
  ·
    refine ⟨42363257636607760576996271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28242171757738507051330847 42363257636607760576996271)
    ·
      refine ⟨63544886454911640865494407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42363257636607760576996271 63544886454911640865494407)
      ·
        refine ⟨95317329682367461298241611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63544886454911640865494407 95317329682367461298241611)
        ·
          refine ⟨142975994523551191947362417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95317329682367461298241611 142975994523551191947362417)
          ·
            refine ⟨107231995892663393960521813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142975994523551191947362417 107231995892663393960521813)
            ·
              refine ⟨1256624951867149147974865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 107231995892663393960521813 1256624951867149147974865)
              ·
                refine ⟨942468713900361860981149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256624951867149147974865 942468713900361860981149)
                ·
                  refine ⟨353425767712635697867931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942468713900361860981149 353425767712635697867931)
                  ·
                    rfl

theorem cell20_774331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_774331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774331 prefixEnd_774331 := by exact prefixLift 774331
  have htrace : WordTrace (prefixWord ++ tailWord_774331) baseStart_774331 baseEnd_774331 := by
    simpa [prefixWord, tailWord_774331, baseEnd_774331] using wordTrace_append hprefix tailTrace_774331
  have hstable : (prefixWord ++ tailWord_774331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774331).length < 2 ^ (prefixWord ++ tailWord_774331).sum := by decide
  have hdescent : baseEnd_774331 < baseStart_774331 := by decide
  rcases family_descends (prefixWord ++ tailWord_774331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774358 : List Nat := [5, 2, 1, 2, 1, 2, 3, 4]
def baseStart_774358 : Nat := 118140960795 + 774358 * 2 ^ 59
def prefixEnd_774358 : Nat := 4983230072969 + 3 ^ 40 * 774358 * 2
def baseEnd_774358 : Nat := 117812697082781201322607

theorem tailTrace_774358 : CollatzResearch.WordTrace tailWord_774358 prefixEnd_774358 117812697082781201322607 := by
  unfold tailWord_774358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765197283040043166410233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18828771019093793775042485 1765197283040043166410233)
  ·
    refine ⟨1323897962280032374807675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1765197283040043166410233 1323897962280032374807675)
    ·
      refine ⟨1985846943420048562211513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323897962280032374807675 1985846943420048562211513)
      ·
        refine ⟨1489385207565036421658635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1985846943420048562211513 1489385207565036421658635)
        ·
          refine ⟨2234077811347554632487953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489385207565036421658635 2234077811347554632487953)
          ·
            refine ⟨1675558358510665974365965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234077811347554632487953 1675558358510665974365965)
            ·
              refine ⟨628334384441499740387237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1675558358510665974365965 628334384441499740387237)
              ·
                refine ⟨117812697082781201322607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628334384441499740387237 117812697082781201322607)
                ·
                  rfl

theorem cell20_774358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_774358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774358 prefixEnd_774358 := by exact prefixLift 774358
  have htrace : WordTrace (prefixWord ++ tailWord_774358) baseStart_774358 baseEnd_774358 := by
    simpa [prefixWord, tailWord_774358, baseEnd_774358] using wordTrace_append hprefix tailTrace_774358
  have hstable : (prefixWord ++ tailWord_774358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774358).length < 2 ^ (prefixWord ++ tailWord_774358).sum := by decide
  have hdescent : baseEnd_774358 < baseStart_774358 := by decide
  rcases family_descends (prefixWord ++ tailWord_774358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774383 : List Nat := [1, 1, 2, 1, 6, 2, 7]
def baseStart_774383 : Nat := 118140960795 + 774383 * 2 ^ 59
def prefixEnd_774383 : Nat := 4983230072969 + 3 ^ 40 * 774383 * 2
def baseEnd_774383 : Nat := 39272166881061625348265

theorem tailTrace_774383 : CollatzResearch.WordTrace tailWord_774383 prefixEnd_774383 39272166881061625348265 := by
  unfold tailWord_774383
  simp only [CollatzResearch.WordTrace]
  refine ⟨28244068353550119932223803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18829378902366746621482535 28244068353550119932223803)
  ·
    refine ⟨42366102530325179898335705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28244068353550119932223803 42366102530325179898335705)
    ·
      refine ⟨31774576897743884923751779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42366102530325179898335705 31774576897743884923751779)
      ·
        refine ⟨47661865346615827385627669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31774576897743884923751779 47661865346615827385627669)
        ·
          refine ⟨2234149938122616908701297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47661865346615827385627669 2234149938122616908701297)
          ·
            refine ⟨1675612453591962681525973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234149938122616908701297 1675612453591962681525973)
            ·
              refine ⟨39272166881061625348265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1675612453591962681525973 39272166881061625348265)
              ·
                rfl

theorem cell20_774383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_774383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774383 prefixEnd_774383 := by exact prefixLift 774383
  have htrace : WordTrace (prefixWord ++ tailWord_774383) baseStart_774383 baseEnd_774383 := by
    simpa [prefixWord, tailWord_774383, baseEnd_774383] using wordTrace_append hprefix tailTrace_774383
  have hstable : (prefixWord ++ tailWord_774383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774383).length < 2 ^ (prefixWord ++ tailWord_774383).sum := by decide
  have hdescent : baseEnd_774383 < baseStart_774383 := by decide
  rcases family_descends (prefixWord ++ tailWord_774383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774386 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_774386 : Nat := 118140960795 + 774386 * 2 ^ 59
def prefixEnd_774386 : Nat := 4983230072969 + 3 ^ 40 * 774386 * 2
def baseEnd_774386 : Nat := 353450871211299951034373

theorem tailTrace_774386 : CollatzResearch.WordTrace tailWord_774386 prefixEnd_774386 353450871211299951034373 := by
  unfold tailWord_774386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061044443134812861145753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18829451848359500963055341 7061044443134812861145753)
  ·
    refine ⟨5295783332351109645859315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7061044443134812861145753 5295783332351109645859315)
    ·
      refine ⟨7943674998526664468788973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295783332351109645859315 7943674998526664468788973)
      ·
        refine ⟨2978878124447499175795865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7943674998526664468788973 2978878124447499175795865)
        ·
          refine ⟨2234158593335624381846899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2978878124447499175795865 2234158593335624381846899)
          ·
            refine ⟨3351237890003436572770349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234158593335624381846899 3351237890003436572770349)
            ·
              refine ⟨1256714208751288714788881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3351237890003436572770349 1256714208751288714788881)
              ·
                refine ⟨942535656563466536091661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256714208751288714788881 942535656563466536091661)
                ·
                  refine ⟨353450871211299951034373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942535656563466536091661 353450871211299951034373)
                  ·
                    rfl

theorem cell20_774386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_774386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774386 prefixEnd_774386 := by exact prefixLift 774386
  have htrace : WordTrace (prefixWord ++ tailWord_774386) baseStart_774386 baseEnd_774386 := by
    simpa [prefixWord, tailWord_774386, baseEnd_774386] using wordTrace_append hprefix tailTrace_774386
  have hstable : (prefixWord ++ tailWord_774386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774386).length < 2 ^ (prefixWord ++ tailWord_774386).sum := by decide
  have hdescent : baseEnd_774386 < baseStart_774386 := by decide
  rcases family_descends (prefixWord ++ tailWord_774386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774414 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_774414 : Nat := 118140960795 + 774414 * 2 ^ 59
def prefixEnd_774414 : Nat := 4983230072969 + 3 ^ 40 * 774414 * 2
def baseEnd_774414 : Nat := 353463651174256298100925

theorem tailTrace_774414 : CollatzResearch.WordTrace tailWord_774414 prefixEnd_774414 353463651174256298100925 := by
  unfold tailWord_774414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530649877054726528325287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18830132677625208151068197 3530649877054726528325287)
  ·
    refine ⟨5295974815582089792487931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3530649877054726528325287 5295974815582089792487931)
    ·
      refine ⟨7943962223373134688731897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295974815582089792487931 7943962223373134688731897)
      ·
        refine ⟨5957971667529851016548923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7943962223373134688731897 5957971667529851016548923)
        ·
          refine ⟨8936957501294776524823385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957971667529851016548923 8936957501294776524823385)
          ·
            refine ⟨6702718125971082393617539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8936957501294776524823385 6702718125971082393617539)
            ·
              refine ⟨10054077188956623590426309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6702718125971082393617539 10054077188956623590426309)
              ·
                refine ⟨1885139472929366923204933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10054077188956623590426309 1885139472929366923204933)
                ·
                  refine ⟨353463651174256298100925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885139472929366923204933 353463651174256298100925)
                  ·
                    rfl

theorem cell20_774414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_774414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774414 prefixEnd_774414 := by exact prefixLift 774414
  have htrace : WordTrace (prefixWord ++ tailWord_774414) baseStart_774414 baseEnd_774414 := by
    simpa [prefixWord, tailWord_774414, baseEnd_774414] using wordTrace_append hprefix tailTrace_774414
  have hstable : (prefixWord ++ tailWord_774414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774414).length < 2 ^ (prefixWord ++ tailWord_774414).sum := by decide
  have hdescent : baseEnd_774414 < baseStart_774414 := by decide
  rcases family_descends (prefixWord ++ tailWord_774414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774462 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_774462 : Nat := 118140960795 + 774462 * 2 ^ 59
def prefixEnd_774462 : Nat := 4983230072969 + 3 ^ 40 * 774462 * 2
def baseEnd_774462 : Nat := 353485559682181464500729

theorem tailTrace_774462 : CollatzResearch.WordTrace tailWord_774462 prefixEnd_774462 353485559682181464500729 := by
  unfold tailWord_774462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530868715032989553043705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18831299813509277616233093 3530868715032989553043705)
  ·
    refine ⟨2648151536274742164782779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3530868715032989553043705 2648151536274742164782779)
    ·
      refine ⟨3972227304412113247174169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648151536274742164782779 3972227304412113247174169)
      ·
        refine ⟨2979170478309084935380627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3972227304412113247174169 2979170478309084935380627)
        ·
          refine ⟨4468755717463627403070941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979170478309084935380627 4468755717463627403070941)
          ·
            refine ⟨1675783394048860276151603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4468755717463627403070941 1675783394048860276151603)
            ·
              refine ⟨2513675091073290414227405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675783394048860276151603 2513675091073290414227405)
              ·
                refine ⟨942628159152483905335277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2513675091073290414227405 942628159152483905335277)
                ·
                  refine ⟨353485559682181464500729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942628159152483905335277 353485559682181464500729)
                  ·
                    rfl

theorem cell20_774462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_774462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774462 prefixEnd_774462 := by exact prefixLift 774462
  have htrace : WordTrace (prefixWord ++ tailWord_774462) baseStart_774462 baseEnd_774462 := by
    simpa [prefixWord, tailWord_774462, baseEnd_774462] using wordTrace_append hprefix tailTrace_774462
  have hstable : (prefixWord ++ tailWord_774462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774462).length < 2 ^ (prefixWord ++ tailWord_774462).sum := by decide
  have hdescent : baseEnd_774462 < baseStart_774462 := by decide
  rcases family_descends (prefixWord ++ tailWord_774462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774473 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_774473 : Nat := 118140960795 + 774473 * 2 ^ 59
def prefixEnd_774473 : Nat := 4983230072969 + 3 ^ 40 * 774473 * 2
def baseEnd_774473 : Nat := 353490580381914315134017

theorem tailTrace_774473 : CollatzResearch.WordTrace tailWord_774473 prefixEnd_774473 353490580381914315134017 := by
  unfold tailWord_774473
  simp only [CollatzResearch.WordTrace]
  refine ⟨28247350923224065303000073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18831567282149376868666715 28247350923224065303000073)
  ·
    refine ⟨21185513192418048977250055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28247350923224065303000073 21185513192418048977250055)
    ·
      refine ⟨31778269788627073465875083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21185513192418048977250055 31778269788627073465875083)
      ·
        refine ⟨47667404682940610198812625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31778269788627073465875083 47667404682940610198812625)
        ·
          refine ⟨35750553512205457649109469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47667404682940610198812625 35750553512205457649109469)
          ·
            refine ⟨13406457567077046618416051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35750553512205457649109469 13406457567077046618416051)
            ·
              refine ⟨20109686350615569927624077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406457567077046618416051 20109686350615569927624077)
              ·
                refine ⟨7541132381480838722859029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20109686350615569927624077 7541132381480838722859029)
                ·
                  refine ⟨353490580381914315134017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7541132381480838722859029 353490580381914315134017)
                  ·
                    rfl

theorem cell20_774473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_774473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774473 prefixEnd_774473 := by exact prefixLift 774473
  have htrace : WordTrace (prefixWord ++ tailWord_774473) baseStart_774473 baseEnd_774473 := by
    simpa [prefixWord, tailWord_774473, baseEnd_774473] using wordTrace_append hprefix tailTrace_774473
  have hstable : (prefixWord ++ tailWord_774473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774473).length < 2 ^ (prefixWord ++ tailWord_774473).sum := by decide
  have hdescent : baseEnd_774473 < baseStart_774473 := by decide
  rcases family_descends (prefixWord ++ tailWord_774473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774503 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 2]
def baseStart_774503 : Nat := 118140960795 + 774503 * 2 ^ 59
def prefixEnd_774503 : Nat := 4983230072969 + 3 ^ 40 * 774503 * 2
def baseEnd_774503 : Nat := 353504273199367544133895

theorem tailTrace_774503 : CollatzResearch.WordTrace tailWord_774503 prefixEnd_774503 353504273199367544133895 := by
  unfold tailWord_774503
  simp only [CollatzResearch.WordTrace]
  refine ⟨28248445113115380426592163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18832296742076920284394775 28248445113115380426592163)
  ·
    refine ⟨42372667669673070639888245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28248445113115380426592163 42372667669673070639888245)
    ·
      refine ⟨3972437594031850372489523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42372667669673070639888245 3972437594031850372489523)
      ·
        refine ⟨5958656391047775558734285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972437594031850372489523 5958656391047775558734285)
        ·
          refine ⟨2234496146642915834525357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5958656391047775558734285 2234496146642915834525357)
          ·
            refine ⟨837936054991093437947009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2234496146642915834525357 837936054991093437947009)
            ·
              refine ⟨628452041243320078460257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837936054991093437947009 628452041243320078460257)
              ·
                refine ⟨471339030932490058845193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628452041243320078460257 471339030932490058845193)
                ·
                  refine ⟨353504273199367544133895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471339030932490058845193 353504273199367544133895)
                  ·
                    rfl

theorem cell20_774503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 2].length) (baseStart_774503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774503 prefixEnd_774503 := by exact prefixLift 774503
  have htrace : WordTrace (prefixWord ++ tailWord_774503) baseStart_774503 baseEnd_774503 := by
    simpa [prefixWord, tailWord_774503, baseEnd_774503] using wordTrace_append hprefix tailTrace_774503
  have hstable : (prefixWord ++ tailWord_774503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774503).length < 2 ^ (prefixWord ++ tailWord_774503).sum := by decide
  have hdescent : baseEnd_774503 < baseStart_774503 := by decide
  rcases family_descends (prefixWord ++ tailWord_774503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774514 : List Nat := [3, 2, 1, 2, 1, 5, 1, 5]
def baseStart_774514 : Nat := 118140960795 + 774514 * 2 ^ 59
def prefixEnd_774514 : Nat := 4983230072969 + 3 ^ 40 * 774514 * 2
def baseEnd_774514 : Nat := 117836431299700131589061

theorem tailTrace_774514 : CollatzResearch.WordTrace tailWord_774514 prefixEnd_774514 117836431299700131589061 := by
  unfold tailWord_774514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062211579018882326310649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18832564210717019536828397 7062211579018882326310649)
  ·
    refine ⟨5296658684264161744732987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7062211579018882326310649 5296658684264161744732987)
    ·
      refine ⟨7944988026396242617099481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5296658684264161744732987 7944988026396242617099481)
      ·
        refine ⟨5958741019797181962824611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7944988026396242617099481 5958741019797181962824611)
        ·
          refine ⟨8938111529695772944236917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958741019797181962824611 8938111529695772944236917)
          ·
            refine ⟨837947955908978713522211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8938111529695772944236917 837947955908978713522211)
            ·
              refine ⟨1256921933863468070283317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837947955908978713522211 1256921933863468070283317)
              ·
                refine ⟨117836431299700131589061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1256921933863468070283317 117836431299700131589061)
                ·
                  rfl

theorem cell20_774514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_774514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774514 prefixEnd_774514 := by exact prefixLift 774514
  have htrace : WordTrace (prefixWord ++ tailWord_774514) baseStart_774514 baseEnd_774514 := by
    simpa [prefixWord, tailWord_774514, baseEnd_774514] using wordTrace_append hprefix tailTrace_774514
  have hstable : (prefixWord ++ tailWord_774514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774514).length < 2 ^ (prefixWord ++ tailWord_774514).sum := by decide
  have hdescent : baseEnd_774514 < baseStart_774514 := by decide
  rcases family_descends (prefixWord ++ tailWord_774514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774549 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_774549 : Nat := 118140960795 + 774549 * 2 ^ 59
def prefixEnd_774549 : Nat := 4983230072969 + 3 ^ 40 * 774549 * 2
def baseEnd_774549 : Nat := 353525268852795828600373

theorem tailTrace_774549 : CollatzResearch.WordTrace tailWord_774549 prefixEnd_774549 353525268852795828600373 := by
  unfold tailWord_774549
  simp only [CollatzResearch.WordTrace]
  refine ⟨28250122870948730282766701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18833415247299153521844467 28250122870948730282766701)
  ·
    refine ⟨10593796076605773856037513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28250122870948730282766701 10593796076605773856037513)
    ·
      refine ⟨7945347057454330392028135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10593796076605773856037513 7945347057454330392028135)
      ·
        refine ⟨11918020586181495588042203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7945347057454330392028135 11918020586181495588042203)
        ·
          refine ⟨17877030879272243382063305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918020586181495588042203 17877030879272243382063305)
          ·
            refine ⟨13407773159454182536547479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17877030879272243382063305 13407773159454182536547479)
            ·
              refine ⟨20111659739181273804821219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13407773159454182536547479 20111659739181273804821219)
              ·
                refine ⟨30167489608771910707231829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20111659739181273804821219 30167489608771910707231829)
                ·
                  refine ⟨353525268852795828600373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30167489608771910707231829 353525268852795828600373)
                  ·
                    rfl

theorem cell20_774549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_774549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774549 prefixEnd_774549 := by exact prefixLift 774549
  have htrace : WordTrace (prefixWord ++ tailWord_774549) baseStart_774549 baseEnd_774549 := by
    simpa [prefixWord, tailWord_774549, baseEnd_774549] using wordTrace_append hprefix tailTrace_774549
  have hstable : (prefixWord ++ tailWord_774549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774549).length < 2 ^ (prefixWord ++ tailWord_774549).sum := by decide
  have hdescent : baseEnd_774549 < baseStart_774549 := by decide
  rcases family_descends (prefixWord ++ tailWord_774549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774590 : List Nat := [4, 2, 1, 1, 1, 1, 6, 4]
def baseStart_774590 : Nat := 118140960795 + 774590 * 2 ^ 59
def prefixEnd_774590 : Nat := 4983230072969 + 3 ^ 40 * 774590 * 2
def baseEnd_774590 : Nat := 117847994123327302744513

theorem tailTrace_774590 : CollatzResearch.WordTrace tailWord_774590 prefixEnd_774590 117847994123327302744513 := by
  unfold tailWord_774590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531452282975024285626153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18834412175866796190006149 3531452282975024285626153)
  ·
    refine ⟨2648589212231268214219615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3531452282975024285626153 2648589212231268214219615)
    ·
      refine ⟨3972883818346902321329423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648589212231268214219615 3972883818346902321329423)
      ·
        refine ⟨5959325727520353481994135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972883818346902321329423 5959325727520353481994135)
        ·
          refine ⟨8938988591280530222991203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5959325727520353481994135 8938988591280530222991203)
          ·
            refine ⟨13408482886920795334486805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8938988591280530222991203 13408482886920795334486805)
            ·
              refine ⟨628522635324412281304069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13408482886920795334486805 628522635324412281304069)
              ·
                refine ⟨117847994123327302744513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628522635324412281304069 117847994123327302744513)
                ·
                  rfl

theorem cell20_774590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_774590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774590 prefixEnd_774590 := by exact prefixLift 774590
  have htrace : WordTrace (prefixWord ++ tailWord_774590) baseStart_774590 baseEnd_774590 := by
    simpa [prefixWord, tailWord_774590, baseEnd_774590] using wordTrace_append hprefix tailTrace_774590
  have hstable : (prefixWord ++ tailWord_774590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774590).length < 2 ^ (prefixWord ++ tailWord_774590).sum := by decide
  have hdescent : baseEnd_774590 < baseStart_774590 := by decide
  rcases family_descends (prefixWord ++ tailWord_774590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774596 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 2]
def baseStart_774596 : Nat := 118140960795 + 774596 * 2 ^ 59
def prefixEnd_774596 : Nat := 4983230072969 + 3 ^ 40 * 774596 * 2
def baseEnd_774596 : Nat := 353546720933472554033515

theorem tailTrace_774596 : CollatzResearch.WordTrace tailWord_774596 prefixEnd_774596 353546720933472554033515 := by
  unfold tailWord_774596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125918550889228654863821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18834558067852304873151761 14125918550889228654863821)
  ·
    refine ⟨5297219456583460745573933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14125918550889228654863821 5297219456583460745573933)
    ·
      refine ⟨1986457296218797779590225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5297219456583460745573933 1986457296218797779590225)
      ·
        refine ⟨1489842972164098334692669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986457296218797779590225 1489842972164098334692669)
        ·
          refine ⟨558691114561536875509751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1489842972164098334692669 558691114561536875509751)
          ·
            refine ⟨838036671842305313264627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558691114561536875509751 838036671842305313264627)
            ·
              refine ⟨1257055007763457969896941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838036671842305313264627 1257055007763457969896941)
              ·
                refine ⟨471395627911296738711353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257055007763457969896941 471395627911296738711353)
                ·
                  refine ⟨353546720933472554033515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471395627911296738711353 353546720933472554033515)
                  ·
                    rfl

theorem cell20_774596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_774596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774596 prefixEnd_774596 := by exact prefixLift 774596
  have htrace : WordTrace (prefixWord ++ tailWord_774596) baseStart_774596 baseEnd_774596 := by
    simpa [prefixWord, tailWord_774596, baseEnd_774596] using wordTrace_append hprefix tailTrace_774596
  have hstable : (prefixWord ++ tailWord_774596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774596).length < 2 ^ (prefixWord ++ tailWord_774596).sum := by decide
  have hdescent : baseEnd_774596 < baseStart_774596 := by decide
  rcases family_descends (prefixWord ++ tailWord_774596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774600 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 2]
def baseStart_774600 : Nat := 118140960795 + 774600 * 2 ^ 59
def prefixEnd_774600 : Nat := 4983230072969 + 3 ^ 40 * 774600 * 2
def baseEnd_774600 : Nat := 353548546642466317900165

theorem tailTrace_774600 : CollatzResearch.WordTrace tailWord_774600 prefixEnd_774600 353548546642466317900165 := by
  unfold tailWord_774600
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125991496881982996436627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18834655329175977328582169 14125991496881982996436627)
  ·
    refine ⟨21188987245322974494654941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14125991496881982996436627 21188987245322974494654941)
    ·
      refine ⟨7945870216996115435495603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21188987245322974494654941 7945870216996115435495603)
      ·
        refine ⟨11918805325494173153243405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7945870216996115435495603 11918805325494173153243405)
        ·
          refine ⟨4469551997060314932466277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11918805325494173153243405 4469551997060314932466277)
          ·
            refine ⟨838040999448809049837427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4469551997060314932466277 838040999448809049837427)
            ·
              refine ⟨1257061499173213574756141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838040999448809049837427 1257061499173213574756141)
              ·
                refine ⟨471398062189955090533553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257061499173213574756141 471398062189955090533553)
                ·
                  refine ⟨353548546642466317900165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471398062189955090533553 353548546642466317900165)
                  ·
                    rfl

theorem cell20_774600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_774600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774600 prefixEnd_774600 := by exact prefixLift 774600
  have htrace : WordTrace (prefixWord ++ tailWord_774600) baseStart_774600 baseEnd_774600 := by
    simpa [prefixWord, tailWord_774600, baseEnd_774600] using wordTrace_append hprefix tailTrace_774600
  have hstable : (prefixWord ++ tailWord_774600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774600).length < 2 ^ (prefixWord ++ tailWord_774600).sum := by decide
  have hdescent : baseEnd_774600 < baseStart_774600 := by decide
  rcases family_descends (prefixWord ++ tailWord_774600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774614 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_774614 : Nat := 118140960795 + 774614 * 2 ^ 59
def prefixEnd_774614 : Nat := 4983230072969 + 3 ^ 40 * 774614 * 2
def baseEnd_774614 : Nat := 353554936623944491433441

theorem tailTrace_774614 : CollatzResearch.WordTrace tailWord_774614 prefixEnd_774614 353554936623944491433441 := by
  unfold tailWord_774614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765780850982077898992681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18834995743808830922588597 1765780850982077898992681)
  ·
    refine ⟨1324335638236558424244511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1765780850982077898992681 1324335638236558424244511)
    ·
      refine ⟨1986503457354837636366767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324335638236558424244511 1986503457354837636366767)
      ·
        refine ⟨2979755186032256454550151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986503457354837636366767 2979755186032256454550151)
        ·
          refine ⟨4469632779048384681825227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979755186032256454550151 4469632779048384681825227)
          ·
            refine ⟨6704449168572577022737841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469632779048384681825227 6704449168572577022737841)
            ·
              refine ⟨5028336876429432767053381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6704449168572577022737841 5028336876429432767053381)
              ·
                refine ⟨942813164330518643822509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5028336876429432767053381 942813164330518643822509)
                ·
                  refine ⟨353554936623944491433441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942813164330518643822509 353554936623944491433441)
                  ·
                    rfl

theorem cell20_774614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_774614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774614 prefixEnd_774614 := by exact prefixLift 774614
  have htrace : WordTrace (prefixWord ++ tailWord_774614) baseStart_774614 baseEnd_774614 := by
    simpa [prefixWord, tailWord_774614, baseEnd_774614] using wordTrace_append hprefix tailTrace_774614
  have hstable : (prefixWord ++ tailWord_774614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774614).length < 2 ^ (prefixWord ++ tailWord_774614).sum := by decide
  have hdescent : baseEnd_774614 < baseStart_774614 := by decide
  rcases family_descends (prefixWord ++ tailWord_774614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774618 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_774618 : Nat := 118140960795 + 774618 * 2 ^ 59
def prefixEnd_774618 : Nat := 4983230072969 + 3 ^ 40 * 774618 * 2
def baseEnd_774618 : Nat := 353556762332938255300091

theorem tailTrace_774618 : CollatzResearch.WordTrace tailWord_774618 prefixEnd_774618 353556762332938255300091 := by
  unfold tailWord_774618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7063159876924688766757127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18835093005132503378019005 7063159876924688766757127)
  ·
    refine ⟨10594739815387033150135691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7063159876924688766757127 10594739815387033150135691)
    ·
      refine ⟨15892109723080549725203537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10594739815387033150135691 15892109723080549725203537)
      ·
        refine ⟨11919082292310412293902653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15892109723080549725203537 11919082292310412293902653)
        ·
          refine ⟨4469655859616404610213495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11919082292310412293902653 4469655859616404610213495)
          ·
            refine ⟨6704483789424606915320243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469655859616404610213495 6704483789424606915320243)
            ·
              refine ⟨10056725684136910372980365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6704483789424606915320243 10056725684136910372980365)
              ·
                refine ⟨3771272131551341389867637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10056725684136910372980365 3771272131551341389867637)
                ·
                  refine ⟨353556762332938255300091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771272131551341389867637 353556762332938255300091)
                  ·
                    rfl

theorem cell20_774618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_774618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774618 prefixEnd_774618 := by exact prefixLift 774618
  have htrace : WordTrace (prefixWord ++ tailWord_774618) baseStart_774618 baseEnd_774618 := by
    simpa [prefixWord, tailWord_774618, baseEnd_774618] using wordTrace_append hprefix tailTrace_774618
  have hstable : (prefixWord ++ tailWord_774618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774618).length < 2 ^ (prefixWord ++ tailWord_774618).sum := by decide
  have hdescent : baseEnd_774618 < baseStart_774618 := by decide
  rcases family_descends (prefixWord ++ tailWord_774618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774669 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 3]
def baseStart_774669 : Nat := 118140960795 + 774669 * 2 ^ 59
def prefixEnd_774669 : Nat := 4983230072969 + 3 ^ 40 * 774669 * 2
def baseEnd_774669 : Nat := 353580040122608744599883

theorem tailTrace_774669 : CollatzResearch.WordTrace tailWord_774669 prefixEnd_774669 353580040122608744599883 := by
  unfold tailWord_774669
  simp only [CollatzResearch.WordTrace]
  refine ⟨28254499630513990777135061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18836333087009327184756707 28254499630513990777135061)
  ·
    refine ⟨662214835090171658839103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28254499630513990777135061 662214835090171658839103)
    ·
      refine ⟨993322252635257488258655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 662214835090171658839103 993322252635257488258655)
      ·
        refine ⟨1489983378952886232387983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993322252635257488258655 1489983378952886232387983)
        ·
          refine ⟨2234975068429329348581975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489983378952886232387983 2234975068429329348581975)
          ·
            refine ⟨3352462602643994022872963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234975068429329348581975 3352462602643994022872963)
            ·
              refine ⟨5028693903965991034309445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352462602643994022872963 5028693903965991034309445)
              ·
                refine ⟨942880106993623318933021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5028693903965991034309445 942880106993623318933021)
                ·
                  refine ⟨353580040122608744599883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942880106993623318933021 353580040122608744599883)
                  ·
                    rfl

theorem cell20_774669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_774669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774669 prefixEnd_774669 := by exact prefixLift 774669
  have htrace : WordTrace (prefixWord ++ tailWord_774669) baseStart_774669 baseEnd_774669 := by
    simpa [prefixWord, tailWord_774669, baseEnd_774669] using wordTrace_append hprefix tailTrace_774669
  have hstable : (prefixWord ++ tailWord_774669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774669).length < 2 ^ (prefixWord ++ tailWord_774669).sum := by decide
  have hdescent : baseEnd_774669 < baseStart_774669 := by decide
  rcases family_descends (prefixWord ++ tailWord_774669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774732 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_774732 : Nat := 118140960795 + 774732 * 2 ^ 59
def prefixEnd_774732 : Nat := 4983230072969 + 3 ^ 40 * 774732 * 2
def baseEnd_774732 : Nat := 353608795039260525499625

theorem tailTrace_774732 : CollatzResearch.WordTrace tailWord_774732 prefixEnd_774732 353608795039260525499625 := by
  unfold tailWord_774732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128398714642876268339225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18837864952857168357785633 14128398714642876268339225)
  ·
    refine ⟨10596299035982157201254419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14128398714642876268339225 10596299035982157201254419)
    ·
      refine ⟨15894448553973235801881629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10596299035982157201254419 15894448553973235801881629)
      ·
        refine ⟨5960418207739963425705611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15894448553973235801881629 5960418207739963425705611)
        ·
          refine ⟨8940627311609945138558417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960418207739963425705611 8940627311609945138558417)
          ·
            refine ⟨6705470483707458853918813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8940627311609945138558417 6705470483707458853918813)
            ·
              refine ⟨2514551431390297070219555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6705470483707458853918813 2514551431390297070219555)
              ·
                refine ⟨3771827147085445605329333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514551431390297070219555 3771827147085445605329333)
                ·
                  refine ⟨353608795039260525499625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771827147085445605329333 353608795039260525499625)
                  ·
                    rfl

theorem cell20_774732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_774732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774732 prefixEnd_774732 := by exact prefixLift 774732
  have htrace : WordTrace (prefixWord ++ tailWord_774732) baseStart_774732 baseEnd_774732 := by
    simpa [prefixWord, tailWord_774732, baseEnd_774732] using wordTrace_append hprefix tailTrace_774732
  have hstable : (prefixWord ++ tailWord_774732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774732).length < 2 ^ (prefixWord ++ tailWord_774732).sum := by decide
  have hdescent : baseEnd_774732 < baseStart_774732 := by decide
  rcases family_descends (prefixWord ++ tailWord_774732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774784 : List Nat := [2, 1, 1, 2, 1, 5, 8]
def baseStart_774784 : Nat := 118140960795 + 774784 * 2 ^ 59
def prefixEnd_774784 : Nat := 4983230072969 + 3 ^ 40 * 774784 * 2
def baseEnd_774784 : Nat := 39292503250686606196231

theorem tailTrace_774784 : CollatzResearch.WordTrace tailWord_774784 prefixEnd_774784 39292503250686606196231 := by
  unfold tailWord_774784
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129347012548682708785703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18839129350064910278380937 14129347012548682708785703)
  ·
    refine ⟨21194020518823024063178555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14129347012548682708785703 21194020518823024063178555)
    ·
      refine ⟨31791030778234536094767833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21194020518823024063178555 31791030778234536094767833)
      ·
        refine ⟨23843273083675902071075875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31791030778234536094767833 23843273083675902071075875)
        ·
          refine ⟨35764909625513853106613813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23843273083675902071075875 35764909625513853106613813)
          ·
            refine ⟨3352960277391923728745045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35764909625513853106613813 3352960277391923728745045)
            ·
              refine ⟨39292503250686606196231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3352960277391923728745045 39292503250686606196231)
              ·
                rfl

theorem cell20_774784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_774784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774784 prefixEnd_774784 := by exact prefixLift 774784
  have htrace : WordTrace (prefixWord ++ tailWord_774784) baseStart_774784 baseEnd_774784 := by
    simpa [prefixWord, tailWord_774784, baseEnd_774784] using wordTrace_append hprefix tailTrace_774784
  have hstable : (prefixWord ++ tailWord_774784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774784).length < 2 ^ (prefixWord ++ tailWord_774784).sum := by decide
  have hdescent : baseEnd_774784 < baseStart_774784 := by decide
  rcases family_descends (prefixWord ++ tailWord_774784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774786 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_774786 : Nat := 118140960795 + 774786 * 2 ^ 59
def prefixEnd_774786 : Nat := 4983230072969 + 3 ^ 40 * 774786 * 2
def baseEnd_774786 : Nat := 353633442110676337699405

theorem tailTrace_774786 : CollatzResearch.WordTrace tailWord_774786 prefixEnd_774786 353633442110676337699405 := by
  unfold tailWord_774786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064691742772529939786053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18839177980726746506096141 7064691742772529939786053)
  ·
    refine ⟨1324629701769849363709885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7064691742772529939786053 1324629701769849363709885)
    ·
      refine ⟨496736138163693511391207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1324629701769849363709885 496736138163693511391207)
      ·
        refine ⟨745104207245540267086811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496736138163693511391207 745104207245540267086811)
        ·
          refine ⟨1117656310868310400630217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745104207245540267086811 1117656310868310400630217)
          ·
            refine ⟨838242233151232800472663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117656310868310400630217 838242233151232800472663)
            ·
              refine ⟨1257363349726849200708995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838242233151232800472663 1257363349726849200708995)
              ·
                refine ⟨1886045024590273801063493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257363349726849200708995 1886045024590273801063493)
                ·
                  refine ⟨353633442110676337699405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886045024590273801063493 353633442110676337699405)
                  ·
                    rfl

theorem cell20_774786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_774786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774786 prefixEnd_774786 := by exact prefixLift 774786
  have htrace : WordTrace (prefixWord ++ tailWord_774786) baseStart_774786 baseEnd_774786 := by
    simpa [prefixWord, tailWord_774786, baseEnd_774786] using wordTrace_append hprefix tailTrace_774786
  have hstable : (prefixWord ++ tailWord_774786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774786).length < 2 ^ (prefixWord ++ tailWord_774786).sum := by decide
  have hdescent : baseEnd_774786 < baseStart_774786 := by decide
  rcases family_descends (prefixWord ++ tailWord_774786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774804 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_774804 : Nat := 118140960795 + 774804 * 2 ^ 59
def prefixEnd_774804 : Nat := 4983230072969 + 3 ^ 40 * 774804 * 2
def baseEnd_774804 : Nat := 353641657801148275099331

theorem tailTrace_774804 : CollatzResearch.WordTrace tailWord_774804 prefixEnd_774804 353641657801148275099331 := by
  unfold tailWord_774804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129711742512454416649733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18839615656683272555532977 14129711742512454416649733)
  ·
    refine ⟨2649320951721085203121825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14129711742512454416649733 2649320951721085203121825)
    ·
      refine ⟨1986990713790813902341369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2649320951721085203121825 1986990713790813902341369)
      ·
        refine ⟨1490243035343110426756027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986990713790813902341369 1490243035343110426756027)
        ·
          refine ⟨2235364553014665640134041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490243035343110426756027 2235364553014665640134041)
          ·
            refine ⟨1676523414760999230100531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235364553014665640134041 1676523414760999230100531)
            ·
              refine ⟨2514785122141498845150797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676523414760999230100531 2514785122141498845150797)
              ·
                refine ⟨943044420803062066931549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2514785122141498845150797 943044420803062066931549)
                ·
                  refine ⟨353641657801148275099331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943044420803062066931549 353641657801148275099331)
                  ·
                    rfl

theorem cell20_774804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_774804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774804 prefixEnd_774804 := by exact prefixLift 774804
  have htrace : WordTrace (prefixWord ++ tailWord_774804) baseStart_774804 baseEnd_774804 := by
    simpa [prefixWord, tailWord_774804, baseEnd_774804] using wordTrace_append hprefix tailTrace_774804
  have hstable : (prefixWord ++ tailWord_774804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774804).length < 2 ^ (prefixWord ++ tailWord_774804).sum := by decide
  have hdescent : baseEnd_774804 < baseStart_774804 := by decide
  rcases family_descends (prefixWord ++ tailWord_774804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774832 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 2]
def baseStart_774832 : Nat := 118140960795 + 774832 * 2 ^ 59
def prefixEnd_774832 : Nat := 4983230072969 + 3 ^ 40 * 774832 * 2
def baseEnd_774832 : Nat := 353654437764104622165883

theorem tailTrace_774832 : CollatzResearch.WordTrace tailWord_774832 prefixEnd_774832 353654437764104622165883 := by
  unfold tailWord_774832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130222364461734807659375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18840296485948979743545833 14130222364461734807659375)
  ·
    refine ⟨21195333546692602211489063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14130222364461734807659375 21195333546692602211489063)
    ·
      refine ⟨31793000320038903317233595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21195333546692602211489063 31793000320038903317233595)
      ·
        refine ⟨47689500480058354975850393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31793000320038903317233595 47689500480058354975850393)
        ·
          refine ⟨35767125360043766231887795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47689500480058354975850393 35767125360043766231887795)
          ·
            refine ⟨53650688040065649347831693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35767125360043766231887795 53650688040065649347831693)
            ·
              refine ⟨20119008015024618505436885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53650688040065649347831693 20119008015024618505436885)
              ·
                refine ⟨471539250352139496221177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20119008015024618505436885 471539250352139496221177)
                ·
                  refine ⟨353654437764104622165883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471539250352139496221177 353654437764104622165883)
                  ·
                    rfl

theorem cell20_774832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_774832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774832 prefixEnd_774832 := by exact prefixLift 774832
  have htrace : WordTrace (prefixWord ++ tailWord_774832) baseStart_774832 baseEnd_774832 := by
    simpa [prefixWord, tailWord_774832, baseEnd_774832] using wordTrace_append hprefix tailTrace_774832
  have hstable : (prefixWord ++ tailWord_774832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774832).length < 2 ^ (prefixWord ++ tailWord_774832).sum := by decide
  have hdescent : baseEnd_774832 < baseStart_774832 := by decide
  rcases family_descends (prefixWord ++ tailWord_774832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774839 : List Nat := [1, 1, 3, 1, 7, 7]
def baseStart_774839 : Nat := 118140960795 + 774839 * 2 ^ 59
def prefixEnd_774839 : Nat := 4983230072969 + 3 ^ 40 * 774839 * 2
def baseEnd_774839 : Nat := 13098430842771989219723

theorem tailTrace_774839 : CollatzResearch.WordTrace tailWord_774839 prefixEnd_774839 13098430842771989219723 := by
  unfold tailWord_774839
  simp only [CollatzResearch.WordTrace]
  refine ⟨28260700039898109810823571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18840466693265406540549047 28260700039898109810823571)
  ·
    refine ⟨42391050059847164716235357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28260700039898109810823571 42391050059847164716235357)
    ·
      refine ⟨15896643772442686768588259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42391050059847164716235357 15896643772442686768588259)
      ·
        refine ⟨23844965658664030152882389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15896643772442686768588259 23844965658664030152882389)
        ·
          refine ⟨558866382624938206708181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 23844965658664030152882389 558866382624938206708181)
          ·
            refine ⟨13098430842771989219723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 558866382624938206708181 13098430842771989219723)
            ·
              rfl

theorem cell20_774839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 7].length) (baseStart_774839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774839 prefixEnd_774839 := by exact prefixLift 774839
  have htrace : WordTrace (prefixWord ++ tailWord_774839) baseStart_774839 baseEnd_774839 := by
    simpa [prefixWord, tailWord_774839, baseEnd_774839] using wordTrace_append hprefix tailTrace_774839
  have hstable : (prefixWord ++ tailWord_774839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774839).length < 2 ^ (prefixWord ++ tailWord_774839).sum := by decide
  have hdescent : baseEnd_774839 < baseStart_774839 := by decide
  rcases family_descends (prefixWord ++ tailWord_774839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774908 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_774908 : Nat := 118140960795 + 774908 * 2 ^ 59
def prefixEnd_774908 : Nat := 4983230072969 + 3 ^ 40 * 774908 * 2
def baseEnd_774908 : Nat := 353689126234986135632239

theorem tailTrace_774908 : CollatzResearch.WordTrace tailWord_774908 prefixEnd_774908 353689126234986135632239 := by
  unfold tailWord_774908
  simp only [CollatzResearch.WordTrace]
  refine ⟨14131608338324067297542689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18842144451098756396723585 14131608338324067297542689)
  ·
    refine ⟨10598706253743050473157017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14131608338324067297542689 10598706253743050473157017)
    ·
      refine ⟨7949029690307287854867763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10598706253743050473157017 7949029690307287854867763)
      ·
        refine ⟨11923544535460931782301645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7949029690307287854867763 11923544535460931782301645)
        ·
          refine ⟨4471329200797849418363117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11923544535460931782301645 4471329200797849418363117)
          ·
            refine ⟨1676748450299193531886169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4471329200797849418363117 1676748450299193531886169)
            ·
              refine ⟨1257561337724395148914627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676748450299193531886169 1257561337724395148914627)
              ·
                refine ⟨1886342006586592723371941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257561337724395148914627 1886342006586592723371941)
                ·
                  refine ⟨353689126234986135632239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886342006586592723371941 353689126234986135632239)
                  ·
                    rfl

theorem cell20_774908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_774908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774908 prefixEnd_774908 := by exact prefixLift 774908
  have htrace : WordTrace (prefixWord ++ tailWord_774908) baseStart_774908 baseEnd_774908 := by
    simpa [prefixWord, tailWord_774908, baseEnd_774908] using wordTrace_append hprefix tailTrace_774908
  have hstable : (prefixWord ++ tailWord_774908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774908).length < 2 ^ (prefixWord ++ tailWord_774908).sum := by decide
  have hdescent : baseEnd_774908 < baseStart_774908 := by decide
  rcases family_descends (prefixWord ++ tailWord_774908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774929 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_774929 : Nat := 118140960795 + 774929 * 2 ^ 59
def prefixEnd_774929 : Nat := 4983230072969 + 3 ^ 40 * 774929 * 2
def baseEnd_774929 : Nat := 353698711207203395932153

theorem tailTrace_774929 : CollatzResearch.WordTrace tailWord_774929 prefixEnd_774929 353698711207203395932153 := by
  unfold tailWord_774929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28263982609572055181599841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18842655073048036787733227 28263982609572055181599841)
  ·
    refine ⟨21197986957179041386199881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28263982609572055181599841 21197986957179041386199881)
    ·
      refine ⟨15898490217884281039649911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21197986957179041386199881 15898490217884281039649911)
      ·
        refine ⟨23847735326826421559474867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15898490217884281039649911 23847735326826421559474867)
        ·
          refine ⟨35771602990239632339212301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23847735326826421559474867 35771602990239632339212301)
          ·
            refine ⟨13414351121339862127204613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35771602990239632339212301 13414351121339862127204613)
            ·
              refine ⟨2515190835251224148850865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13414351121339862127204613 2515190835251224148850865)
              ·
                refine ⟨1886393126438418111638149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515190835251224148850865 1886393126438418111638149)
                ·
                  refine ⟨353698711207203395932153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886393126438418111638149 353698711207203395932153)
                  ·
                    rfl

theorem cell20_774929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_774929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774929 prefixEnd_774929 := by exact prefixLift 774929
  have htrace : WordTrace (prefixWord ++ tailWord_774929) baseStart_774929 baseEnd_774929 := by
    simpa [prefixWord, tailWord_774929, baseEnd_774929] using wordTrace_append hprefix tailTrace_774929
  have hstable : (prefixWord ++ tailWord_774929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774929).length < 2 ^ (prefixWord ++ tailWord_774929).sum := by decide
  have hdescent : baseEnd_774929 < baseStart_774929 := by decide
  rcases family_descends (prefixWord ++ tailWord_774929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774973 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 3]
def baseStart_774973 : Nat := 118140960795 + 774973 * 2 ^ 59
def prefixEnd_774973 : Nat := 4983230072969 + 3 ^ 40 * 774973 * 2
def baseEnd_774973 : Nat := 353718794006134798465307

theorem tailTrace_774973 : CollatzResearch.WordTrace tailWord_774973 prefixEnd_774973 353718794006134798465307 := by
  unfold tailWord_774973
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265587421412650696201573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18843724947608433797467715 28265587421412650696201573)
  ·
    refine ⟨5299797641514872005537795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28265587421412650696201573 5299797641514872005537795)
    ·
      refine ⟨7949696462272308008306693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5299797641514872005537795 7949696462272308008306693)
      ·
        refine ⟨1490568086676057751557505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7949696462272308008306693 1490568086676057751557505)
        ·
          refine ⟨1117926065007043313668129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1490568086676057751557505 1117926065007043313668129)
          ·
            refine ⟨838444548755282485251097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117926065007043313668129 838444548755282485251097)
            ·
              refine ⟨628833411566461863938323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838444548755282485251097 628833411566461863938323)
              ·
                refine ⟨943250117349692795907485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628833411566461863938323 943250117349692795907485)
                ·
                  refine ⟨353718794006134798465307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943250117349692795907485 353718794006134798465307)
                  ·
                    rfl

theorem cell20_774973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_774973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774973 prefixEnd_774973 := by exact prefixLift 774973
  have htrace : WordTrace (prefixWord ++ tailWord_774973) baseStart_774973 baseEnd_774973 := by
    simpa [prefixWord, tailWord_774973, baseEnd_774973] using wordTrace_append hprefix tailTrace_774973
  have hstable : (prefixWord ++ tailWord_774973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774973).length < 2 ^ (prefixWord ++ tailWord_774973).sum := by decide
  have hdescent : baseEnd_774973 < baseStart_774973 := by decide
  rcases family_descends (prefixWord ++ tailWord_774973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774981 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_774981 : Nat := 118140960795 + 774981 * 2 ^ 59
def prefixEnd_774981 : Nat := 4983230072969 + 3 ^ 40 * 774981 * 2
def baseEnd_774981 : Nat := 353722445424122326198607

theorem tailTrace_774981 : CollatzResearch.WordTrace tailWord_774981 prefixEnd_774981 353722445424122326198607 := by
  unfold tailWord_774981
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265879205383668062492797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18843919470255778708328531 28265879205383668062492797)
  ·
    refine ⟨10599704702018875523434799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28265879205383668062492797 10599704702018875523434799)
    ·
      refine ⟨15899557053028313285152199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599704702018875523434799 15899557053028313285152199)
      ·
        refine ⟨23849335579542469927728299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15899557053028313285152199 23849335579542469927728299)
        ·
          refine ⟨35774003369313704891592449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23849335579542469927728299 35774003369313704891592449)
          ·
            refine ⟨26830502526985278668694337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35774003369313704891592449 26830502526985278668694337)
            ·
              refine ⟨20122876895238959001520753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26830502526985278668694337 20122876895238959001520753)
              ·
                refine ⟨15092157671429219251140565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20122876895238959001520753 15092157671429219251140565)
                ·
                  refine ⟨353722445424122326198607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15092157671429219251140565 353722445424122326198607)
                  ·
                    rfl

theorem cell20_774981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_774981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_774981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_774981 prefixEnd_774981 := by exact prefixLift 774981
  have htrace : WordTrace (prefixWord ++ tailWord_774981) baseStart_774981 baseEnd_774981 := by
    simpa [prefixWord, tailWord_774981, baseEnd_774981] using wordTrace_append hprefix tailTrace_774981
  have hstable : (prefixWord ++ tailWord_774981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774981).length < 2 ^ (prefixWord ++ tailWord_774981).sum := by decide
  have hdescent : baseEnd_774981 < baseStart_774981 := by decide
  rcases family_descends (prefixWord ++ tailWord_774981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775012 : List Nat := [2, 3, 1, 1, 4, 9]
def baseStart_775012 : Nat := 118140960795 + 775012 * 2 ^ 59
def prefixEnd_775012 : Nat := 4983230072969 + 3 ^ 40 * 775012 * 2
def baseEnd_775012 : Nat := 13101355358104592450561

theorem tailTrace_775012 : CollatzResearch.WordTrace tailWord_775012 prefixEnd_775012 13101355358104592450561 := by
  unfold tailWord_775012
  simp only [CollatzResearch.WordTrace]
  refine ⟨14133504934135680178435645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18844673245514240237914193 14133504934135680178435645)
  ·
    refine ⟨5300064350300880066913367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14133504934135680178435645 5300064350300880066913367)
    ·
      refine ⟨7950096525451320100370051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300064350300880066913367 7950096525451320100370051)
      ·
        refine ⟨11925144788176980150555077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7950096525451320100370051 11925144788176980150555077)
        ·
          refine ⟨2235964647783183778229077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11925144788176980150555077 2235964647783183778229077)
          ·
            refine ⟨13101355358104592450561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2235964647783183778229077 13101355358104592450561)
            ·
              rfl

theorem cell20_775012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 9].length) (baseStart_775012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775012 prefixEnd_775012 := by exact prefixLift 775012
  have htrace : WordTrace (prefixWord ++ tailWord_775012) baseStart_775012 baseEnd_775012 := by
    simpa [prefixWord, tailWord_775012, baseEnd_775012] using wordTrace_append hprefix tailTrace_775012
  have hstable : (prefixWord ++ tailWord_775012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775012).length < 2 ^ (prefixWord ++ tailWord_775012).sum := by decide
  have hdescent : baseEnd_775012 < baseStart_775012 := by decide
  rcases family_descends (prefixWord ++ tailWord_775012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775015 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_775015 : Nat := 118140960795 + 775015 * 2 ^ 59
def prefixEnd_775015 : Nat := 4983230072969 + 3 ^ 40 * 775015 * 2
def baseEnd_775015 : Nat := 353737963950569319065135

theorem tailTrace_775015 : CollatzResearch.WordTrace tailWord_775015 prefixEnd_775015 353737963950569319065135 := by
  unfold tailWord_775015
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267119287260491869230499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18844746191506994579486999 28267119287260491869230499)
  ·
    refine ⟨42400678930890737803845749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28267119287260491869230499 42400678930890737803845749)
    ·
      refine ⟨3975063649771006669110539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42400678930890737803845749 3975063649771006669110539)
      ·
        refine ⟨5962595474656510003665809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975063649771006669110539 5962595474656510003665809)
        ·
          refine ⟨4471946605992382502749357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5962595474656510003665809 4471946605992382502749357)
          ·
            refine ⟨1676979977247143438531009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4471946605992382502749357 1676979977247143438531009)
            ·
              refine ⟨1257734982935357578898257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676979977247143438531009 1257734982935357578898257)
              ·
                refine ⟨943301237201518184173693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257734982935357578898257 943301237201518184173693)
                ·
                  refine ⟨353737963950569319065135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943301237201518184173693 353737963950569319065135)
                  ·
                    rfl

theorem cell20_775015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_775015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775015 prefixEnd_775015 := by exact prefixLift 775015
  have htrace : WordTrace (prefixWord ++ tailWord_775015) baseStart_775015 baseEnd_775015 := by
    simpa [prefixWord, tailWord_775015, baseEnd_775015] using wordTrace_append hprefix tailTrace_775015
  have hstable : (prefixWord ++ tailWord_775015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775015).length < 2 ^ (prefixWord ++ tailWord_775015).sum := by decide
  have hdescent : baseEnd_775015 < baseStart_775015 := by decide
  rcases family_descends (prefixWord ++ tailWord_775015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775019 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_775019 : Nat := 118140960795 + 775019 * 2 ^ 59
def prefixEnd_775019 : Nat := 4983230072969 + 3 ^ 40 * 775019 * 2
def baseEnd_775019 : Nat := 353739789659563082931785

theorem tailTrace_775019 : CollatzResearch.WordTrace tailWord_775019 prefixEnd_775019 353739789659563082931785 := by
  unfold tailWord_775019
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267265179246000552376111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18844843452830667034917407 28267265179246000552376111)
  ·
    refine ⟨42400897768869000828564167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28267265179246000552376111 42400897768869000828564167)
    ·
      refine ⟨63601346653303501242846251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42400897768869000828564167 63601346653303501242846251)
      ·
        refine ⟨95402019979955251864269377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63601346653303501242846251 95402019979955251864269377)
        ·
          refine ⟨71551514984966438898202033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95402019979955251864269377 71551514984966438898202033)
          ·
            refine ⟨53663636238724829173651525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71551514984966438898202033 53663636238724829173651525)
            ·
              refine ⟨10061931794760905470059661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53663636238724829173651525 10061931794760905470059661)
              ·
                refine ⟨3773224423035339551272373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10061931794760905470059661 3773224423035339551272373)
                ·
                  refine ⟨353739789659563082931785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3773224423035339551272373 353739789659563082931785)
                  ·
                    rfl

theorem cell20_775019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_775019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775019 prefixEnd_775019 := by exact prefixLift 775019
  have htrace : WordTrace (prefixWord ++ tailWord_775019) baseStart_775019 baseEnd_775019 := by
    simpa [prefixWord, tailWord_775019, baseEnd_775019] using wordTrace_append hprefix tailTrace_775019
  have hstable : (prefixWord ++ tailWord_775019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775019).length < 2 ^ (prefixWord ++ tailWord_775019).sum := by decide
  have hdescent : baseEnd_775019 < baseStart_775019 := by decide
  rcases family_descends (prefixWord ++ tailWord_775019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775029 : List Nat := [1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_775029 : Nat := 118140960795 + 775029 * 2 ^ 59
def prefixEnd_775029 : Nat := 4983230072969 + 3 ^ 40 * 775029 * 2
def baseEnd_775029 : Nat := 117914784644015830866137

theorem tailTrace_775029 : CollatzResearch.WordTrace tailWord_775029 prefixEnd_775029 117914784644015830866137 := by
  unfold tailWord_775029
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267629909209772260240141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18845086606139848173493427 28267629909209772260240141)
  ·
    refine ⟨10600361215953664597590053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28267629909209772260240141 10600361215953664597590053)
    ·
      refine ⟨1987567727991312112048135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10600361215953664597590053 1987567727991312112048135)
      ·
        refine ⟨2981351591986968168072203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987567727991312112048135 2981351591986968168072203)
        ·
          refine ⟨4472027387980452252108305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981351591986968168072203 4472027387980452252108305)
          ·
            refine ⟨3354020540985339189081229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4472027387980452252108305 3354020540985339189081229)
            ·
              refine ⟨1257757702869502195905461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3354020540985339189081229 1257757702869502195905461)
              ·
                refine ⟨117914784644015830866137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1257757702869502195905461 117914784644015830866137)
                ·
                  rfl

theorem cell20_775029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_775029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775029 prefixEnd_775029 := by exact prefixLift 775029
  have htrace : WordTrace (prefixWord ++ tailWord_775029) baseStart_775029 baseEnd_775029 := by
    simpa [prefixWord, tailWord_775029, baseEnd_775029] using wordTrace_append hprefix tailTrace_775029
  have hstable : (prefixWord ++ tailWord_775029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775029).length < 2 ^ (prefixWord ++ tailWord_775029).sum := by decide
  have hdescent : baseEnd_775029 < baseStart_775029 := by decide
  rcases family_descends (prefixWord ++ tailWord_775029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775042 : List Nat := [3, 4, 2, 2, 1, 1, 3, 4]
def baseStart_775042 : Nat := 118140960795 + 775042 * 2 ^ 59
def prefixEnd_775042 : Nat := 4983230072969 + 3 ^ 40 * 775042 * 2
def baseEnd_775042 : Nat := 117916762495425741721675

theorem tailTrace_775042 : CollatzResearch.WordTrace tailWord_775042 prefixEnd_775042 117916762495425741721675 := by
  unfold tailWord_775042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067026014540668870115845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18845402705441783653642253 7067026014540668870115845)
  ·
    refine ⟨1325067377726375413146721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7067026014540668870115845 1325067377726375413146721)
    ·
      refine ⟨993800533294781559860041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1325067377726375413146721 993800533294781559860041)
      ·
        refine ⟨745350399971086169895031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993800533294781559860041 745350399971086169895031)
        ·
          refine ⟨1118025599956629254842547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745350399971086169895031 1118025599956629254842547)
          ·
            refine ⟨1677038399934943882263821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118025599956629254842547 1677038399934943882263821)
            ·
              refine ⟨628889399975603955848933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1677038399934943882263821 628889399975603955848933)
              ·
                refine ⟨117916762495425741721675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628889399975603955848933 117916762495425741721675)
                ·
                  rfl

theorem cell20_775042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_775042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775042 prefixEnd_775042 := by exact prefixLift 775042
  have htrace : WordTrace (prefixWord ++ tailWord_775042) baseStart_775042 baseEnd_775042 := by
    simpa [prefixWord, tailWord_775042, baseEnd_775042] using wordTrace_append hprefix tailTrace_775042
  have hstable : (prefixWord ++ tailWord_775042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775042).length < 2 ^ (prefixWord ++ tailWord_775042).sum := by decide
  have hdescent : baseEnd_775042 < baseStart_775042 := by decide
  rcases family_descends (prefixWord ++ tailWord_775042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775043 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_775043 : Nat := 118140960795 + 775043 * 2 ^ 59
def prefixEnd_775043 : Nat := 4983230072969 + 3 ^ 40 * 775043 * 2
def baseEnd_775043 : Nat := 353750743913525666131687

theorem tailTrace_775043 : CollatzResearch.WordTrace tailWord_775043 prefixEnd_775043 353750743913525666131687 := by
  unfold tailWord_775043
  simp only [CollatzResearch.WordTrace]
  refine ⟨28268140531159052651249783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18845427020772701767499855 28268140531159052651249783)
  ·
    refine ⟨42402210796738578976874675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28268140531159052651249783 42402210796738578976874675)
    ·
      refine ⟨63603316195107868465312013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42402210796738578976874675 63603316195107868465312013)
      ·
        refine ⟨23851243573165450674492005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63603316195107868465312013 23851243573165450674492005)
        ·
          refine ⟨4472108169968522001467251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23851243573165450674492005 4472108169968522001467251)
          ·
            refine ⟨6708162254952783002200877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472108169968522001467251 6708162254952783002200877)
            ·
              refine ⟨2515560845607293625825329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6708162254952783002200877 2515560845607293625825329)
              ·
                refine ⟨1886670634205470219368997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515560845607293625825329 1886670634205470219368997)
                ·
                  refine ⟨353750743913525666131687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886670634205470219368997 353750743913525666131687)
                  ·
                    rfl

theorem cell20_775043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_775043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775043 prefixEnd_775043 := by exact prefixLift 775043
  have htrace : WordTrace (prefixWord ++ tailWord_775043) baseStart_775043 baseEnd_775043 := by
    simpa [prefixWord, tailWord_775043, baseEnd_775043] using wordTrace_append hprefix tailTrace_775043
  have hstable : (prefixWord ++ tailWord_775043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775043).length < 2 ^ (prefixWord ++ tailWord_775043).sum := by decide
  have hdescent : baseEnd_775043 < baseStart_775043 := by decide
  rcases family_descends (prefixWord ++ tailWord_775043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775057 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_775057 : Nat := 118140960795 + 775057 * 2 ^ 59
def prefixEnd_775057 : Nat := 4983230072969 + 3 ^ 40 * 775057 * 2
def baseEnd_775057 : Nat := 353757133895003839664963

theorem tailTrace_775057 : CollatzResearch.WordTrace tailWord_775057 prefixEnd_775057 353757133895003839664963 := by
  unfold tailWord_775057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28268651153108333042259425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18845767435405555361506283 28268651153108333042259425)
  ·
    refine ⟨21201488364831249781694569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28268651153108333042259425 21201488364831249781694569)
    ·
      refine ⟨15901116273623437336270927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21201488364831249781694569 15901116273623437336270927)
      ·
        refine ⟨23851674410435156004406391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15901116273623437336270927 23851674410435156004406391)
        ·
          refine ⟨35777511615652734006609587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23851674410435156004406391 35777511615652734006609587)
          ·
            refine ⟨53666267423479101009914381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35777511615652734006609587 53666267423479101009914381)
            ·
              refine ⟨20124850283804662878717893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53666267423479101009914381 20124850283804662878717893)
              ·
                refine ⟨3773409428213374289759605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20124850283804662878717893 3773409428213374289759605)
                ·
                  refine ⟨353757133895003839664963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3773409428213374289759605 353757133895003839664963)
                  ·
                    rfl

theorem cell20_775057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_775057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775057 prefixEnd_775057 := by exact prefixLift 775057
  have htrace : WordTrace (prefixWord ++ tailWord_775057) baseStart_775057 baseEnd_775057 := by
    simpa [prefixWord, tailWord_775057, baseEnd_775057] using wordTrace_append hprefix tailTrace_775057
  have hstable : (prefixWord ++ tailWord_775057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775057).length < 2 ^ (prefixWord ++ tailWord_775057).sum := by decide
  have hdescent : baseEnd_775057 < baseStart_775057 := by decide
  rcases family_descends (prefixWord ++ tailWord_775057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775081 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_775081 : Nat := 118140960795 + 775081 * 2 ^ 59
def prefixEnd_775081 : Nat := 4983230072969 + 3 ^ 40 * 775081 * 2
def baseEnd_775081 : Nat := 353768088148966422864865

theorem tailTrace_775081 : CollatzResearch.WordTrace tailWord_775081 prefixEnd_775081 353768088148966422864865 := by
  unfold tailWord_775081
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269526505021385141133097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18846351003347590094088731 28269526505021385141133097)
  ·
    refine ⟨21202144878766038855849823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28269526505021385141133097 21202144878766038855849823)
    ·
      refine ⟨31803217318149058283774735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21202144878766038855849823 31803217318149058283774735)
      ·
        refine ⟨47704825977223587425662103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31803217318149058283774735 47704825977223587425662103)
        ·
          refine ⟨71557238965835381138493155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47704825977223587425662103 71557238965835381138493155)
          ·
            refine ⟨107335858448753071707739733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71557238965835381138493155 107335858448753071707739733)
            ·
              refine ⟨1257842091196325059075075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 107335858448753071707739733 1257842091196325059075075)
              ·
                refine ⟨1886763136794487588612613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257842091196325059075075 1886763136794487588612613)
                ·
                  refine ⟨353768088148966422864865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886763136794487588612613 353768088148966422864865)
                  ·
                    rfl

theorem cell20_775081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_775081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775081 prefixEnd_775081 := by exact prefixLift 775081
  have htrace : WordTrace (prefixWord ++ tailWord_775081) baseStart_775081 baseEnd_775081 := by
    simpa [prefixWord, tailWord_775081, baseEnd_775081] using wordTrace_append hprefix tailTrace_775081
  have hstable : (prefixWord ++ tailWord_775081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775081).length < 2 ^ (prefixWord ++ tailWord_775081).sum := by decide
  have hdescent : baseEnd_775081 < baseStart_775081 := by decide
  rcases family_descends (prefixWord ++ tailWord_775081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775101 : List Nat := [1, 4, 1, 2, 5, 1, 2, 4]
def baseStart_775101 : Nat := 118140960795 + 775101 * 2 ^ 59
def prefixEnd_775101 : Nat := 4983230072969 + 3 ^ 40 * 775101 * 2
def baseEnd_775101 : Nat := 117925738897978414066039

theorem tailTrace_775101 : CollatzResearch.WordTrace tailWord_775101 prefixEnd_775101 117925738897978414066039 := by
  unfold tailWord_775101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28270255964948928556861157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18846837309965952371240771 28270255964948928556861157)
  ·
    refine ⟨5300672993427924104411467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28270255964948928556861157 5300672993427924104411467)
    ·
      refine ⟨7951009490141886156617201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300672993427924104411467 7951009490141886156617201)
      ·
        refine ⟨5963257117606414617462901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7951009490141886156617201 5963257117606414617462901)
        ·
          refine ⟨559055354775601370387147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5963257117606414617462901 559055354775601370387147)
          ·
            refine ⟨838583032163402055580721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559055354775601370387147 838583032163402055580721)
            ·
              refine ⟨628937274122551541685541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838583032163402055580721 628937274122551541685541)
              ·
                refine ⟨117925738897978414066039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628937274122551541685541 117925738897978414066039)
                ·
                  rfl

theorem cell20_775101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].length) (baseStart_775101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775101 prefixEnd_775101 := by exact prefixLift 775101
  have htrace : WordTrace (prefixWord ++ tailWord_775101) baseStart_775101 baseEnd_775101 := by
    simpa [prefixWord, tailWord_775101, baseEnd_775101] using wordTrace_append hprefix tailTrace_775101
  have hstable : (prefixWord ++ tailWord_775101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775101).length < 2 ^ (prefixWord ++ tailWord_775101).sum := by decide
  have hdescent : baseEnd_775101 < baseStart_775101 := by decide
  rcases family_descends (prefixWord ++ tailWord_775101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775115 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 2]
def baseStart_775115 : Nat := 118140960795 + 775115 * 2 ^ 59
def prefixEnd_775115 : Nat := 4983230072969 + 3 ^ 40 * 775115 * 2
def baseEnd_775115 : Nat := 353783606675413415731393

theorem tailTrace_775115 : CollatzResearch.WordTrace tailWord_775115 prefixEnd_775115 353783606675413415731393 := by
  unfold tailWord_775115
  simp only [CollatzResearch.WordTrace]
  refine ⟨28270766586898208947870799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18847177724598805965247199 28270766586898208947870799)
  ·
    refine ⟨42406149880347313421806199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28270766586898208947870799 42406149880347313421806199)
    ·
      refine ⟨63609224820520970132709299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42406149880347313421806199 63609224820520970132709299)
      ·
        refine ⟨95413837230781455199063949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63609224820520970132709299 95413837230781455199063949)
        ·
          refine ⟨35780188961543045699648981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95413837230781455199063949 35780188961543045699648981)
          ·
            refine ⟨838598178786165133585523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35780188961543045699648981 838598178786165133585523)
            ·
              refine ⟨1257897268179247700378285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838598178786165133585523 1257897268179247700378285)
              ·
                refine ⟨471711475567217887641857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257897268179247700378285 471711475567217887641857)
                ·
                  refine ⟨353783606675413415731393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471711475567217887641857 353783606675413415731393)
                  ·
                    rfl

theorem cell20_775115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 2].length) (baseStart_775115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775115 prefixEnd_775115 := by exact prefixLift 775115
  have htrace : WordTrace (prefixWord ++ tailWord_775115) baseStart_775115 baseEnd_775115 := by
    simpa [prefixWord, tailWord_775115, baseEnd_775115] using wordTrace_append hprefix tailTrace_775115
  have hstable : (prefixWord ++ tailWord_775115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775115).length < 2 ^ (prefixWord ++ tailWord_775115).sum := by decide
  have hdescent : baseEnd_775115 < baseStart_775115 := by decide
  rcases family_descends (prefixWord ++ tailWord_775115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775143 : List Nat := [1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_775143 : Nat := 118140960795 + 775143 * 2 ^ 59
def prefixEnd_775143 : Nat := 4983230072969 + 3 ^ 40 * 775143 * 2
def baseEnd_775143 : Nat := 117932128879456587599315

theorem tailTrace_775143 : CollatzResearch.WordTrace tailWord_775143 prefixEnd_775143 117932128879456587599315 := by
  unfold tailWord_775143
  simp only [CollatzResearch.WordTrace]
  refine ⟨28271787830796769729890083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18847858553864513153260055 28271787830796769729890083)
  ·
    refine ⟨42407681746195154594835125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28271787830796769729890083 42407681746195154594835125)
    ·
      refine ⟨3975720163705795743265793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42407681746195154594835125 3975720163705795743265793)
      ·
        refine ⟨2981790122779346807449345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3975720163705795743265793 2981790122779346807449345)
        ·
          refine ⟨2236342592084510105587009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981790122779346807449345 2236342592084510105587009)
          ·
            refine ⟨1677256944063382579190257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236342592084510105587009 1677256944063382579190257)
            ·
              refine ⟨1257942708047536934392693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677256944063382579190257 1257942708047536934392693)
              ·
                refine ⟨117932128879456587599315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1257942708047536934392693 117932128879456587599315)
                ·
                  rfl

theorem cell20_775143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_775143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775143 prefixEnd_775143 := by exact prefixLift 775143
  have htrace : WordTrace (prefixWord ++ tailWord_775143) baseStart_775143 baseEnd_775143 := by
    simpa [prefixWord, tailWord_775143, baseEnd_775143] using wordTrace_append hprefix tailTrace_775143
  have hstable : (prefixWord ++ tailWord_775143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775143).length < 2 ^ (prefixWord ++ tailWord_775143).sum := by decide
  have hdescent : baseEnd_775143 < baseStart_775143 := by decide
  rcases family_descends (prefixWord ++ tailWord_775143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775146 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_775146 : Nat := 118140960795 + 775146 * 2 ^ 59
def prefixEnd_775146 : Nat := 4983230072969 + 3 ^ 40 * 775146 * 2
def baseEnd_775146 : Nat := 353797755920115085697933

theorem tailTrace_775146 : CollatzResearch.WordTrace tailWord_775146 prefixEnd_775146 353797755920115085697933 := by
  unfold tailWord_775146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067974312446475310562323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18847931499857267494832861 7067974312446475310562323)
  ·
    refine ⟨10601961468669712965843485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7067974312446475310562323 10601961468669712965843485)
    ·
      refine ⟨3975735550751142362191307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10601961468669712965843485 3975735550751142362191307)
      ·
        refine ⟨5963603326126713543286961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975735550751142362191307 5963603326126713543286961)
        ·
          refine ⟨4472702494595035157465221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5963603326126713543286961 4472702494595035157465221)
          ·
            refine ⟨838631717736569092024729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4472702494595035157465221 838631717736569092024729)
            ·
              refine ⟨628973788302426819018547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838631717736569092024729 628973788302426819018547)
              ·
                refine ⟨943460682453640228527821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628973788302426819018547 943460682453640228527821)
                ·
                  refine ⟨353797755920115085697933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943460682453640228527821 353797755920115085697933)
                  ·
                    rfl

theorem cell20_775146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_775146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775146 prefixEnd_775146 := by exact prefixLift 775146
  have htrace : WordTrace (prefixWord ++ tailWord_775146) baseStart_775146 baseEnd_775146 := by
    simpa [prefixWord, tailWord_775146, baseEnd_775146] using wordTrace_append hprefix tailTrace_775146
  have hstable : (prefixWord ++ tailWord_775146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775146).length < 2 ^ (prefixWord ++ tailWord_775146).sum := by decide
  have hdescent : baseEnd_775146 < baseStart_775146 := by decide
  rcases family_descends (prefixWord ++ tailWord_775146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775164 : List Nat := [2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_775164 : Nat := 118140960795 + 775164 * 2 ^ 59
def prefixEnd_775164 : Nat := 4983230072969 + 3 ^ 40 * 775164 * 2
def baseEnd_775164 : Nat := 117935323870195674365953

theorem tailTrace_775164 : CollatzResearch.WordTrace tailWord_775164 prefixEnd_775164 117935323870195674365953 := by
  unfold tailWord_775164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14136276881860345158202273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18848369175813793544269697 14136276881860345158202273)
  ·
    refine ⟨10602207661395258868651705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14136276881860345158202273 10602207661395258868651705)
    ·
      refine ⟨7951655746046444151488779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10602207661395258868651705 7951655746046444151488779)
      ·
        refine ⟨11927483619069666227233169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951655746046444151488779 11927483619069666227233169)
        ·
          refine ⟨8945612714302249670424877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11927483619069666227233169 8945612714302249670424877)
          ·
            refine ⟨3354604767863343626409329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8945612714302249670424877 3354604767863343626409329)
            ·
              refine ⟨2515953575897507719806997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3354604767863343626409329 2515953575897507719806997)
              ·
                refine ⟨117935323870195674365953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2515953575897507719806997 117935323870195674365953)
                ·
                  rfl

theorem cell20_775164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_775164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775164 prefixEnd_775164 := by exact prefixLift 775164
  have htrace : WordTrace (prefixWord ++ tailWord_775164) baseStart_775164 baseEnd_775164 := by
    simpa [prefixWord, tailWord_775164, baseEnd_775164] using wordTrace_append hprefix tailTrace_775164
  have hstable : (prefixWord ++ tailWord_775164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775164).length < 2 ^ (prefixWord ++ tailWord_775164).sum := by decide
  have hdescent : baseEnd_775164 < baseStart_775164 := by decide
  rcases family_descends (prefixWord ++ tailWord_775164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775181 : List Nat := [1, 7, 1, 11]
def baseStart_775181 : Nat := 118140960795 + 775181 * 2 ^ 59
def prefixEnd_775181 : Nat := 4983230072969 + 3 ^ 40 * 775181 * 2
def baseEnd_775181 : Nat := 1456023583842841644161

theorem tailTrace_775181 : CollatzResearch.WordTrace tailWord_775181 prefixEnd_775181 1456023583842841644161 := by
  unfold tailWord_775181
  simp only [CollatzResearch.WordTrace]
  refine ⟨28273173804659102219773397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18848782536439401479848931 28273173804659102219773397)
  ·
    refine ⟨662652511046697708275939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28273173804659102219773397 662652511046697708275939)
    ·
      refine ⟨993978766570046562413909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 662652511046697708275939 993978766570046562413909)
      ·
        refine ⟨1456023583842841644161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 993978766570046562413909 1456023583842841644161)
        ·
          rfl

theorem cell20_775181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 11].length) (baseStart_775181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775181 prefixEnd_775181 := by exact prefixLift 775181
  have htrace : WordTrace (prefixWord ++ tailWord_775181) baseStart_775181 baseEnd_775181 := by
    simpa [prefixWord, tailWord_775181, baseEnd_775181] using wordTrace_append hprefix tailTrace_775181
  have hstable : (prefixWord ++ tailWord_775181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775181).length < 2 ^ (prefixWord ++ tailWord_775181).sum := by decide
  have hdescent : baseEnd_775181 < baseStart_775181 := by decide
  rcases family_descends (prefixWord ++ tailWord_775181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775191 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 2]
def baseStart_775191 : Nat := 118140960795 + 775191 * 2 ^ 59
def prefixEnd_775191 : Nat := 4983230072969 + 3 ^ 40 * 775191 * 2
def baseEnd_775191 : Nat := 353818295146294929197749

theorem tailTrace_775191 : CollatzResearch.WordTrace tailWord_775191 prefixEnd_775191 353818295146294929197749 := by
  unfold tailWord_775191
  simp only [CollatzResearch.WordTrace]
  refine ⟨28273538534622873927637427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18849025689748582618424951 28273538534622873927637427)
  ·
    refine ⟨42410307801934310891456141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28273538534622873927637427 42410307801934310891456141)
    ·
      refine ⟨15903865425725366584296053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42410307801934310891456141 15903865425725366584296053)
      ·
        refine ⟨1490987383661753117277755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15903865425725366584296053 1490987383661753117277755)
        ·
          refine ⟨2236481075492629675916633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490987383661753117277755 2236481075492629675916633)
          ·
            refine ⟨1677360806619472256937475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236481075492629675916633 1677360806619472256937475)
            ·
              refine ⟨2516041209929208385406213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677360806619472256937475 2516041209929208385406213)
              ·
                refine ⟨471757726861726572263665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2516041209929208385406213 471757726861726572263665)
                ·
                  refine ⟨353818295146294929197749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471757726861726572263665 353818295146294929197749)
                  ·
                    rfl

theorem cell20_775191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 2].length) (baseStart_775191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775191 prefixEnd_775191 := by exact prefixLift 775191
  have htrace : WordTrace (prefixWord ++ tailWord_775191) baseStart_775191 baseEnd_775191 := by
    simpa [prefixWord, tailWord_775191, baseEnd_775191] using wordTrace_append hprefix tailTrace_775191
  have hstable : (prefixWord ++ tailWord_775191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775191).length < 2 ^ (prefixWord ++ tailWord_775191).sum := by decide
  have hdescent : baseEnd_775191 < baseStart_775191 := by decide
  rcases family_descends (prefixWord ++ tailWord_775191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775229 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 2]
def baseStart_775229 : Nat := 118140960795 + 775229 * 2 ^ 59
def prefixEnd_775229 : Nat := 4983230072969 + 3 ^ 40 * 775229 * 2
def baseEnd_775229 : Nat := 353835639381735685930927

theorem tailTrace_775229 : CollatzResearch.WordTrace tailWord_775229 prefixEnd_775229 353835639381735685930927 := by
  unfold tailWord_775229
  simp only [CollatzResearch.WordTrace]
  refine ⟨28274924508485206417520741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18849949672323470945013827 28274924508485206417520741)
  ·
    refine ⟨5301548345340976203285139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28274924508485206417520741 5301548345340976203285139)
    ·
      refine ⟨7952322518011464304927709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5301548345340976203285139 7952322518011464304927709)
      ·
        refine ⟨2982120944254299114347891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7952322518011464304927709 2982120944254299114347891)
        ·
          refine ⟨4473181416381448671521837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982120944254299114347891 4473181416381448671521837)
          ·
            refine ⟨1677443031143043251820689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4473181416381448671521837 1677443031143043251820689)
            ·
              refine ⟨1258082273357282438865517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677443031143043251820689 1258082273357282438865517)
              ·
                refine ⟨471780852508980914574569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258082273357282438865517 471780852508980914574569)
                ·
                  refine ⟨353835639381735685930927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471780852508980914574569 353835639381735685930927)
                  ·
                    rfl

theorem cell20_775229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_775229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775229 prefixEnd_775229 := by exact prefixLift 775229
  have htrace : WordTrace (prefixWord ++ tailWord_775229) baseStart_775229 baseEnd_775229 := by
    simpa [prefixWord, tailWord_775229, baseEnd_775229] using wordTrace_append hprefix tailTrace_775229
  have hstable : (prefixWord ++ tailWord_775229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775229).length < 2 ^ (prefixWord ++ tailWord_775229).sum := by decide
  have hdescent : baseEnd_775229 < baseStart_775229 := by decide
  rcases family_descends (prefixWord ++ tailWord_775229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775250 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_775250 : Nat := 118140960795 + 775250 * 2 ^ 59
def prefixEnd_775250 : Nat := 4983230072969 + 3 ^ 40 * 775250 * 2
def baseEnd_775250 : Nat := 353845224353952946230841

theorem tailTrace_775250 : CollatzResearch.WordTrace tailWord_775250 prefixEnd_775250 353845224353952946230841 := by
  unfold tailWord_775250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068922610352281751008801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18850460294272751336023469 7068922610352281751008801)
  ·
    refine ⟨5301691957764211313256601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7068922610352281751008801 5301691957764211313256601)
    ·
      refine ⟨3976268968323158484942451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5301691957764211313256601 3976268968323158484942451)
      ·
        refine ⟨5964403452484737727413677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976268968323158484942451 5964403452484737727413677)
        ·
          refine ⟨2236651294681776647780129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5964403452484737727413677 2236651294681776647780129)
          ·
            refine ⟨1677488471011332485835097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236651294681776647780129 1677488471011332485835097)
            ·
              refine ⟨1258116353258499364376323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677488471011332485835097 1258116353258499364376323)
              ·
                refine ⟨1887174529887749046564485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258116353258499364376323 1887174529887749046564485)
                ·
                  refine ⟨353845224353952946230841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887174529887749046564485 353845224353952946230841)
                  ·
                    rfl

theorem cell20_775250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_775250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775250 prefixEnd_775250 := by exact prefixLift 775250
  have htrace : WordTrace (prefixWord ++ tailWord_775250) baseStart_775250 baseEnd_775250 := by
    simpa [prefixWord, tailWord_775250, baseEnd_775250] using wordTrace_append hprefix tailTrace_775250
  have hstable : (prefixWord ++ tailWord_775250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775250).length < 2 ^ (prefixWord ++ tailWord_775250).sum := by decide
  have hdescent : baseEnd_775250 < baseStart_775250 := by decide
  rcases family_descends (prefixWord ++ tailWord_775250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775271 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_775271 : Nat := 118140960795 + 775271 * 2 ^ 59
def prefixEnd_775271 : Nat := 4983230072969 + 3 ^ 40 * 775271 * 2
def baseEnd_775271 : Nat := 353854809326170206530755

theorem tailTrace_775271 : CollatzResearch.WordTrace tailWord_775271 prefixEnd_775271 353854809326170206530755 := by
  unfold tailWord_775271
  simp only [CollatzResearch.WordTrace]
  refine ⟨28276456374333047590549667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18850970916222031727033111 28276456374333047590549667)
  ·
    refine ⟨42414684561499571385824501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28276456374333047590549667 42414684561499571385824501)
    ·
      refine ⟨3976376677640584817421047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42414684561499571385824501 3976376677640584817421047)
      ·
        refine ⟨5964565016460877226131571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976376677640584817421047 5964565016460877226131571)
        ·
          refine ⟨8946847524691315839197357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964565016460877226131571 8946847524691315839197357)
          ·
            refine ⟨3355067821759243439699009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8946847524691315839197357 3355067821759243439699009)
            ·
              refine ⟨2516300866319432579774257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355067821759243439699009 2516300866319432579774257)
              ·
                refine ⟨1887225649739574434830693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516300866319432579774257 1887225649739574434830693)
                ·
                  refine ⟨353854809326170206530755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887225649739574434830693 353854809326170206530755)
                  ·
                    rfl

theorem cell20_775271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_775271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775271 prefixEnd_775271 := by exact prefixLift 775271
  have htrace : WordTrace (prefixWord ++ tailWord_775271) baseStart_775271 baseEnd_775271 := by
    simpa [prefixWord, tailWord_775271, baseEnd_775271] using wordTrace_append hprefix tailTrace_775271
  have hstable : (prefixWord ++ tailWord_775271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775271).length < 2 ^ (prefixWord ++ tailWord_775271).sum := by decide
  have hdescent : baseEnd_775271 < baseStart_775271 := by decide
  rcases family_descends (prefixWord ++ tailWord_775271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775274 : List Nat := [3, 1, 3, 2, 2, 3, 2, 4]
def baseStart_775274 : Nat := 118140960795 + 775274 * 2 ^ 59
def prefixEnd_775274 : Nat := 4983230072969 + 3 ^ 40 * 775274 * 2
def baseEnd_775274 : Nat := 117952059535971843143581

theorem tailTrace_775274 : CollatzResearch.WordTrace tailWord_775274 prefixEnd_775274 117952059535971843143581 := by
  unfold tailWord_775274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069141448330544775727219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18851043862214786068605917 7069141448330544775727219)
  ·
    refine ⟨10603712172495817163590829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7069141448330544775727219 10603712172495817163590829)
    ·
      refine ⟨3976392064685931436346561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10603712172495817163590829 3976392064685931436346561)
      ·
        refine ⟨2982294048514448577259921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3976392064685931436346561 2982294048514448577259921)
        ·
          refine ⟨2236720536385836432944941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982294048514448577259921 2236720536385836432944941)
          ·
            refine ⟨838770201144688662354353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2236720536385836432944941 838770201144688662354353)
            ·
              refine ⟨629077650858516496765765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838770201144688662354353 629077650858516496765765)
              ·
                refine ⟨117952059535971843143581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629077650858516496765765 117952059535971843143581)
                ·
                  rfl

theorem cell20_775274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_775274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775274 prefixEnd_775274 := by exact prefixLift 775274
  have htrace : WordTrace (prefixWord ++ tailWord_775274) baseStart_775274 baseEnd_775274 := by
    simpa [prefixWord, tailWord_775274, baseEnd_775274] using wordTrace_append hprefix tailTrace_775274
  have hstable : (prefixWord ++ tailWord_775274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775274).length < 2 ^ (prefixWord ++ tailWord_775274).sum := by decide
  have hdescent : baseEnd_775274 < baseStart_775274 := by decide
  rcases family_descends (prefixWord ++ tailWord_775274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775288 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 2]
def baseStart_775288 : Nat := 118140960795 + 775288 * 2 ^ 59
def prefixEnd_775288 : Nat := 4983230072969 + 3 ^ 40 * 775288 * 2
def baseEnd_775288 : Nat := 353862568589393702964019

theorem tailTrace_775288 : CollatzResearch.WordTrace tailWord_775288 prefixEnd_775288 353862568589393702964019 := by
  unfold tailWord_775288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138538207635729746959259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18851384276847639662612345 14138538207635729746959259)
  ·
    refine ⟨21207807311453594620438889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14138538207635729746959259 21207807311453594620438889)
    ·
      refine ⟨15905855483590195965329167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21207807311453594620438889 15905855483590195965329167)
      ·
        refine ⟨23858783225385293947993751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15905855483590195965329167 23858783225385293947993751)
        ·
          refine ⟨35788174838077940921990627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23858783225385293947993751 35788174838077940921990627)
          ·
            refine ⟨53682262257116911382985941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35788174838077940921990627 53682262257116911382985941)
            ·
              refine ⟨1258178021651177610538733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53682262257116911382985941 1258178021651177610538733)
              ·
                refine ⟨471816758119191603952025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258178021651177610538733 471816758119191603952025)
                ·
                  refine ⟨353862568589393702964019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471816758119191603952025 353862568589393702964019)
                  ·
                    rfl

theorem cell20_775288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_775288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775288 prefixEnd_775288 := by exact prefixLift 775288
  have htrace : WordTrace (prefixWord ++ tailWord_775288) baseStart_775288 baseEnd_775288 := by
    simpa [prefixWord, tailWord_775288, baseEnd_775288] using wordTrace_append hprefix tailTrace_775288
  have hstable : (prefixWord ++ tailWord_775288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775288).length < 2 ^ (prefixWord ++ tailWord_775288).sum := by decide
  have hdescent : baseEnd_775288 < baseStart_775288 := by decide
  rcases family_descends (prefixWord ++ tailWord_775288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775305 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 2]
def baseStart_775305 : Nat := 118140960795 + 775305 * 2 ^ 59
def prefixEnd_775305 : Nat := 4983230072969 + 3 ^ 40 * 775305 * 2
def baseEnd_775305 : Nat := 353870327852617199397283

theorem tailTrace_775305 : CollatzResearch.WordTrace tailWord_775305 prefixEnd_775305 353870327852617199397283 := by
  unfold tailWord_775305
  simp only [CollatzResearch.WordTrace]
  refine ⟨28277696456209871397287369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18851797637473247598191579 28277696456209871397287369)
  ·
    refine ⟨21208272342157403547965527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28277696456209871397287369 21208272342157403547965527)
    ·
      refine ⟨31812408513236105321948291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21208272342157403547965527 31812408513236105321948291)
      ·
        refine ⟨47718612769854157982922437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31812408513236105321948291 47718612769854157982922437)
        ·
          refine ⟨8947239894347654621797957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47718612769854157982922437 8947239894347654621797957)
          ·
            refine ⟨1677607480190185241587117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8947239894347654621797957 1677607480190185241587117)
            ·
              refine ⟨629102805071319465595169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1677607480190185241587117 629102805071319465595169)
              ·
                refine ⟨471827103803489599196377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629102805071319465595169 471827103803489599196377)
                ·
                  refine ⟨353870327852617199397283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471827103803489599196377 353870327852617199397283)
                  ·
                    rfl

theorem cell20_775305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_775305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775305 prefixEnd_775305 := by exact prefixLift 775305
  have htrace : WordTrace (prefixWord ++ tailWord_775305) baseStart_775305 baseEnd_775305 := by
    simpa [prefixWord, tailWord_775305, baseEnd_775305] using wordTrace_append hprefix tailTrace_775305
  have hstable : (prefixWord ++ tailWord_775305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775305).length < 2 ^ (prefixWord ++ tailWord_775305).sum := by decide
  have hdescent : baseEnd_775305 < baseStart_775305 := by decide
  rcases family_descends (prefixWord ++ tailWord_775305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775319 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 3]
def baseStart_775319 : Nat := 118140960795 + 775319 * 2 ^ 59
def prefixEnd_775319 : Nat := 4983230072969 + 3 ^ 40 * 775319 * 2
def baseEnd_775319 : Nat := 353876717834095372930559

theorem tailTrace_775319 : CollatzResearch.WordTrace tailWord_775319 prefixEnd_775319 353876717834095372930559 := by
  unfold tailWord_775319
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278207078159151788297011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18852138052106101192198007 28278207078159151788297011)
  ·
    refine ⟨42417310617238727682445517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28278207078159151788297011 42417310617238727682445517)
    ·
      refine ⟨15906491481464522880917069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42417310617238727682445517 15906491481464522880917069)
      ·
        refine ⟨5964934305549196080343901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15906491481464522880917069 5964934305549196080343901)
        ·
          refine ⟨2236850364580948530128963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5964934305549196080343901 2236850364580948530128963)
          ·
            refine ⟨3355275546871422795193445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236850364580948530128963 3355275546871422795193445)
            ·
              refine ⟨629114165038391774098771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3355275546871422795193445 629114165038391774098771)
              ·
                refine ⟨943671247557587661148157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629114165038391774098771 943671247557587661148157)
                ·
                  refine ⟨353876717834095372930559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943671247557587661148157 353876717834095372930559)
                  ·
                    rfl

theorem cell20_775319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_775319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775319 prefixEnd_775319 := by exact prefixLift 775319
  have htrace : WordTrace (prefixWord ++ tailWord_775319) baseStart_775319 baseEnd_775319 := by
    simpa [prefixWord, tailWord_775319, baseEnd_775319] using wordTrace_append hprefix tailTrace_775319
  have hstable : (prefixWord ++ tailWord_775319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775319).length < 2 ^ (prefixWord ++ tailWord_775319).sum := by decide
  have hdescent : baseEnd_775319 < baseStart_775319 := by decide
  rcases family_descends (prefixWord ++ tailWord_775319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775350 : List Nat := [5, 1, 3, 2, 1, 8]
def baseStart_775350 : Nat := 118140960795 + 775350 * 2 ^ 59
def prefixEnd_775350 : Nat := 4983230072969 + 3 ^ 40 * 775350 * 2
def baseEnd_775350 : Nat := 13107069151066557144337

theorem tailTrace_775350 : CollatzResearch.WordTrace tailWord_775350 prefixEnd_775350 13107069151066557144337 := by
  unfold tailWord_775350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767458608815427755167219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18852891827364562721783669 1767458608815427755167219)
  ·
    refine ⟨2651187913223141632750829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1767458608815427755167219 2651187913223141632750829)
    ·
      refine ⟨994195467458678112281561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2651187913223141632750829 994195467458678112281561)
      ·
        refine ⟨745646600594008584211171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 994195467458678112281561 745646600594008584211171)
        ·
          refine ⟨1118469900891012876316757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745646600594008584211171 1118469900891012876316757)
          ·
            refine ⟨13107069151066557144337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1118469900891012876316757 13107069151066557144337)
            ·
              rfl

theorem cell20_775350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 8].length) (baseStart_775350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775350 prefixEnd_775350 := by exact prefixLift 775350
  have htrace : WordTrace (prefixWord ++ tailWord_775350) baseStart_775350 baseEnd_775350 := by
    simpa [prefixWord, tailWord_775350, baseEnd_775350] using wordTrace_append hprefix tailTrace_775350
  have hstable : (prefixWord ++ tailWord_775350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775350).length < 2 ^ (prefixWord ++ tailWord_775350).sum := by decide
  have hdescent : baseEnd_775350 < baseStart_775350 := by decide
  rcases family_descends (prefixWord ++ tailWord_775350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775360 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 2]
def baseStart_775360 : Nat := 118140960795 + 775360 * 2 ^ 59
def prefixEnd_775360 : Nat := 4983230072969 + 3 ^ 40 * 775360 * 2
def baseEnd_775360 : Nat := 353895431351281452563725

theorem tailTrace_775360 : CollatzResearch.WordTrace tailWord_775360 prefixEnd_775360 353895431351281452563725 := by
  unfold tailWord_775360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14139851235505307895269767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18853134980673743860359689 14139851235505307895269767)
  ·
    refine ⟨21209776853257961842904651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14139851235505307895269767 21209776853257961842904651)
    ·
      refine ⟨31814665279886942764356977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21209776853257961842904651 31814665279886942764356977)
      ·
        refine ⟨23860998959915207073267733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31814665279886942764356977 23860998959915207073267733)
        ·
          refine ⟨1118484326246025331559425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23860998959915207073267733 1118484326246025331559425)
          ·
            refine ⟨838863244684518998669569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118484326246025331559425 838863244684518998669569)
            ·
              refine ⟨629147433513389249002177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838863244684518998669569 629147433513389249002177)
              ·
                refine ⟨471860575135041936751633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629147433513389249002177 471860575135041936751633)
                ·
                  refine ⟨353895431351281452563725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471860575135041936751633 353895431351281452563725)
                  ·
                    rfl

theorem cell20_775360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_775360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775360 prefixEnd_775360 := by exact prefixLift 775360
  have htrace : WordTrace (prefixWord ++ tailWord_775360) baseStart_775360 baseEnd_775360 := by
    simpa [prefixWord, tailWord_775360, baseEnd_775360] using wordTrace_append hprefix tailTrace_775360
  have hstable : (prefixWord ++ tailWord_775360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775360).length < 2 ^ (prefixWord ++ tailWord_775360).sum := by decide
  have hdescent : baseEnd_775360 < baseStart_775360 := by decide
  rcases family_descends (prefixWord ++ tailWord_775360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775375 : List Nat := [1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_775375 : Nat := 118140960795 + 775375 * 2 ^ 59
def prefixEnd_775375 : Nat := 4983230072969 + 3 ^ 40 * 775375 * 2
def baseEnd_775375 : Nat := 117967425920002689021221

theorem tailTrace_775375 : CollatzResearch.WordTrace tailWord_775375 prefixEnd_775375 117967425920002689021221 := by
  unfold tailWord_775375
  simp only [CollatzResearch.WordTrace]
  refine ⟨28280249565956273352335579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18853499710637515568223719 28280249565956273352335579)
  ·
    refine ⟨42420374348934410028503369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28280249565956273352335579 42420374348934410028503369)
    ·
      refine ⟨31815280761700807521377527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42420374348934410028503369 31815280761700807521377527)
      ·
        refine ⟨47722921142551211282066291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31815280761700807521377527 47722921142551211282066291)
        ·
          refine ⟨71584381713826816923099437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47722921142551211282066291 71584381713826816923099437)
          ·
            refine ⟨26844143142685056346162289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71584381713826816923099437 26844143142685056346162289)
            ·
              refine ⟨20133107357013792259621717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26844143142685056346162289 20133107357013792259621717)
              ·
                refine ⟨117967425920002689021221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20133107357013792259621717 117967425920002689021221)
                ·
                  rfl

theorem cell20_775375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_775375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775375 prefixEnd_775375 := by exact prefixLift 775375
  have htrace : WordTrace (prefixWord ++ tailWord_775375) baseStart_775375 baseEnd_775375 := by
    simpa [prefixWord, tailWord_775375, baseEnd_775375] using wordTrace_append hprefix tailTrace_775375
  have hstable : (prefixWord ++ tailWord_775375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775375).length < 2 ^ (prefixWord ++ tailWord_775375).sum := by decide
  have hdescent : baseEnd_775375 < baseStart_775375 := by decide
  rcases family_descends (prefixWord ++ tailWord_775375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775378 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_775378 : Nat := 118140960795 + 775378 * 2 ^ 59
def prefixEnd_775378 : Nat := 4983230072969 + 3 ^ 40 * 775378 * 2
def baseEnd_775378 : Nat := 353903647041753389963651

theorem tailTrace_775378 : CollatzResearch.WordTrace tailWord_775378 prefixEnd_775378 353903647041753389963651 := by
  unfold tailWord_775378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070089746236351216173697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18853572656630269909796525 7070089746236351216173697)
  ·
    refine ⟨5302567309677263412130273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7070089746236351216173697 5302567309677263412130273)
    ·
      refine ⟨3976925482257947559097705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5302567309677263412130273 3976925482257947559097705)
      ·
        refine ⟨2982694111693460669323279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3976925482257947559097705 2982694111693460669323279)
        ·
          refine ⟨4474041167540191003984919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982694111693460669323279 4474041167540191003984919)
          ·
            refine ⟨6711061751310286505977379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474041167540191003984919 6711061751310286505977379)
            ·
              refine ⟨10066592626965429758966069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6711061751310286505977379 10066592626965429758966069)
              ·
                refine ⟨943743058778009039903069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10066592626965429758966069 943743058778009039903069)
                ·
                  refine ⟨353903647041753389963651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943743058778009039903069 353903647041753389963651)
                  ·
                    rfl

theorem cell20_775378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_775378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775378 prefixEnd_775378 := by exact prefixLift 775378
  have htrace : WordTrace (prefixWord ++ tailWord_775378) baseStart_775378 baseEnd_775378 := by
    simpa [prefixWord, tailWord_775378, baseEnd_775378] using wordTrace_append hprefix tailTrace_775378
  have hstable : (prefixWord ++ tailWord_775378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775378).length < 2 ^ (prefixWord ++ tailWord_775378).sum := by decide
  have hdescent : baseEnd_775378 < baseStart_775378 := by decide
  rcases family_descends (prefixWord ++ tailWord_775378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775402 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_775402 : Nat := 118140960795 + 775402 * 2 ^ 59
def prefixEnd_775402 : Nat := 4983230072969 + 3 ^ 40 * 775402 * 2
def baseEnd_775402 : Nat := 353914601295715973163553

theorem tailTrace_775402 : CollatzResearch.WordTrace tailWord_775402 prefixEnd_775402 353914601295715973163553 := by
  unfold tailWord_775402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070308584214614240892115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18854156224572304642378973 7070308584214614240892115)
  ·
    refine ⟨10605462876321921361338173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070308584214614240892115 10605462876321921361338173)
    ·
      refine ⟨3977048578620720510501815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10605462876321921361338173 3977048578620720510501815)
      ·
        refine ⟨5965572867931080765752723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977048578620720510501815 5965572867931080765752723)
        ·
          refine ⟨8948359301896621148629085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965572867931080765752723 8948359301896621148629085)
          ·
            refine ⟨3355634738211232930735907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8948359301896621148629085 3355634738211232930735907)
            ·
              refine ⟨5033452107316849396103861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355634738211232930735907 5033452107316849396103861)
              ·
                refine ⟨471886135060954630884737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5033452107316849396103861 471886135060954630884737)
                ·
                  refine ⟨353914601295715973163553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471886135060954630884737 353914601295715973163553)
                  ·
                    rfl

theorem cell20_775402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_775402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775402 prefixEnd_775402 := by exact prefixLift 775402
  have htrace : WordTrace (prefixWord ++ tailWord_775402) baseStart_775402 baseEnd_775402 := by
    simpa [prefixWord, tailWord_775402, baseEnd_775402] using wordTrace_append hprefix tailTrace_775402
  have hstable : (prefixWord ++ tailWord_775402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775402).length < 2 ^ (prefixWord ++ tailWord_775402).sum := by decide
  have hdescent : baseEnd_775402 < baseStart_775402 := by decide
  rcases family_descends (prefixWord ++ tailWord_775402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775423 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_775423 : Nat := 118140960795 + 775423 * 2 ^ 59
def prefixEnd_775423 : Nat := 4983230072969 + 3 ^ 40 * 775423 * 2
def baseEnd_775423 : Nat := 353924186267933233463467

theorem tailTrace_775423 : CollatzResearch.WordTrace tailWord_775423 prefixEnd_775423 353924186267933233463467 := by
  unfold tailWord_775423
  simp only [CollatzResearch.WordTrace]
  refine ⟨28282000269782377550082923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18854666846521585033388615 28282000269782377550082923)
  ·
    refine ⟨42423000404673566325124385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28282000269782377550082923 42423000404673566325124385)
    ·
      refine ⟨31817250303505174743843289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42423000404673566325124385 31817250303505174743843289)
      ·
        refine ⟨23862937727628881057882467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31817250303505174743843289 23862937727628881057882467)
        ·
          refine ⟨35794406591443321586823701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23862937727628881057882467 35794406591443321586823701)
          ·
            refine ⟨1677862808973905699382361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35794406591443321586823701 1677862808973905699382361)
            ·
              refine ⟨1258397106730429274536771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677862808973905699382361 1258397106730429274536771)
              ·
                refine ⟨1887595660095643911805157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258397106730429274536771 1887595660095643911805157)
                ·
                  refine ⟨353924186267933233463467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887595660095643911805157 353924186267933233463467)
                  ·
                    rfl

theorem cell20_775423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_775423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775423 prefixEnd_775423 := by exact prefixLift 775423
  have htrace : WordTrace (prefixWord ++ tailWord_775423) baseStart_775423 baseEnd_775423 := by
    simpa [prefixWord, tailWord_775423, baseEnd_775423] using wordTrace_append hprefix tailTrace_775423
  have hstable : (prefixWord ++ tailWord_775423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775423).length < 2 ^ (prefixWord ++ tailWord_775423).sum := by decide
  have hdescent : baseEnd_775423 < baseStart_775423 := by decide
  rcases family_descends (prefixWord ++ tailWord_775423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775475 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_775475 : Nat := 118140960795 + 775475 * 2 ^ 59
def prefixEnd_775475 : Nat := 4983230072969 + 3 ^ 40 * 775475 * 2
def baseEnd_775475 : Nat := 353947920484852163729921

theorem tailTrace_775475 : CollatzResearch.WordTrace tailWord_775475 prefixEnd_775475 353947920484852163729921 := by
  unfold tailWord_775475
  simp only [CollatzResearch.WordTrace]
  refine ⟨28283896865593990430975879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18855931243729326953983919 28283896865593990430975879)
  ·
    refine ⟨42425845298390985646463819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28283896865593990430975879 42425845298390985646463819)
    ·
      refine ⟨63638767947586478469695729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42425845298390985646463819 63638767947586478469695729)
      ·
        refine ⟨47729075960689858852271797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63638767947586478469695729 47729075960689858852271797)
        ·
          refine ⟨4474600871314674267400481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47729075960689858852271797 4474600871314674267400481)
          ·
            refine ⟨3355950653486005700550361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474600871314674267400481 3355950653486005700550361)
            ·
              refine ⟨2516962990114504275412771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355950653486005700550361 2516962990114504275412771)
              ·
                refine ⟨3775444485171756413119157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516962990114504275412771 3775444485171756413119157)
                ·
                  refine ⟨353947920484852163729921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3775444485171756413119157 353947920484852163729921)
                  ·
                    rfl

theorem cell20_775475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_775475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775475 prefixEnd_775475 := by exact prefixLift 775475
  have htrace : WordTrace (prefixWord ++ tailWord_775475) baseStart_775475 baseEnd_775475 := by
    simpa [prefixWord, tailWord_775475, baseEnd_775475] using wordTrace_append hprefix tailTrace_775475
  have hstable : (prefixWord ++ tailWord_775475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775475).length < 2 ^ (prefixWord ++ tailWord_775475).sum := by decide
  have hdescent : baseEnd_775475 < baseStart_775475 := by decide
  rcases family_descends (prefixWord ++ tailWord_775475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775527 : List Nat := [1, 1, 5, 1, 12]
def baseStart_775527 : Nat := 118140960795 + 775527 * 2 ^ 59
def prefixEnd_775527 : Nat := 4983230072969 + 3 ^ 40 * 775527 * 2
def baseEnd_775527 : Nat := 4370020428416927086375

theorem tailTrace_775527 : CollatzResearch.WordTrace tailWord_775527 prefixEnd_775527 4370020428416927086375 := by
  unfold tailWord_775527
  simp only [CollatzResearch.WordTrace]
  refine ⟨28285793461405603311868835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18857195640937068874579223 28285793461405603311868835)
  ·
    refine ⟨42428690192108404967803253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28285793461405603311868835 42428690192108404967803253)
    ·
      refine ⟨3977689705510162965731555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42428690192108404967803253 3977689705510162965731555)
      ·
        refine ⟨5966534558265244448597333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977689705510162965731555 5966534558265244448597333)
        ·
          refine ⟨4370020428416927086375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5966534558265244448597333 4370020428416927086375)
          ·
            rfl

theorem cell20_775527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 12].length) (baseStart_775527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775527 prefixEnd_775527 := by exact prefixLift 775527
  have htrace : WordTrace (prefixWord ++ tailWord_775527) baseStart_775527 baseEnd_775527 := by
    simpa [prefixWord, tailWord_775527, baseEnd_775527] using wordTrace_append hprefix tailTrace_775527
  have hstable : (prefixWord ++ tailWord_775527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775527).length < 2 ^ (prefixWord ++ tailWord_775527).sum := by decide
  have hdescent : baseEnd_775527 < baseStart_775527 := by decide
  rcases family_descends (prefixWord ++ tailWord_775527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775533 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 2]
def baseStart_775533 : Nat := 118140960795 + 775533 * 2 ^ 59
def prefixEnd_775533 : Nat := 4983230072969 + 3 ^ 40 * 775533 * 2
def baseEnd_775533 : Nat := 353974393265261739796351

theorem tailTrace_775533 : CollatzResearch.WordTrace tailWord_775533 prefixEnd_775533 353974393265261739796351 := by
  unfold tailWord_775533
  simp only [CollatzResearch.WordTrace]
  refine ⟨28286012299383866336587253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18857341532922577557724835 28286012299383866336587253)
  ·
    refine ⟨2651813653067237469055055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28286012299383866336587253 2651813653067237469055055)
    ·
      refine ⟨3977720479600856203582583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651813653067237469055055 3977720479600856203582583)
      ·
        refine ⟨5966580719401284305373875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977720479600856203582583 5966580719401284305373875)
        ·
          refine ⟨8949871079101926458060813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966580719401284305373875 8949871079101926458060813)
          ·
            refine ⟨3356201654663222421772805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8949871079101926458060813 3356201654663222421772805)
            ·
              refine ⟨629287810249354204082401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3356201654663222421772805 629287810249354204082401)
              ·
                refine ⟨471965857687015653061801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629287810249354204082401 471965857687015653061801)
                ·
                  refine ⟨353974393265261739796351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471965857687015653061801 353974393265261739796351)
                  ·
                    rfl

theorem cell20_775533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_775533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775533 prefixEnd_775533 := by exact prefixLift 775533
  have htrace : WordTrace (prefixWord ++ tailWord_775533) baseStart_775533 baseEnd_775533 := by
    simpa [prefixWord, tailWord_775533, baseEnd_775533] using wordTrace_append hprefix tailTrace_775533
  have hstable : (prefixWord ++ tailWord_775533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775533).length < 2 ^ (prefixWord ++ tailWord_775533).sum := by decide
  have hdescent : baseEnd_775533 < baseStart_775533 := by decide
  rcases family_descends (prefixWord ++ tailWord_775533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775554 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_775554 : Nat := 118140960795 + 775554 * 2 ^ 59
def prefixEnd_775554 : Nat := 4983230072969 + 3 ^ 40 * 775554 * 2
def baseEnd_775554 : Nat := 353983978237479000096265

theorem tailTrace_775554 : CollatzResearch.WordTrace tailWord_775554 prefixEnd_775554 353983978237479000096265 := by
  unfold tailWord_775554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7071694558076946730775429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18857852154871857948734477 7071694558076946730775429)
  ·
    refine ⟨1325942729639427512020393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7071694558076946730775429 1325942729639427512020393)
    ·
      refine ⟨994457047229570634015295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1325942729639427512020393 994457047229570634015295)
      ·
        refine ⟨1491685570844355951022943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994457047229570634015295 1491685570844355951022943)
        ·
          refine ⟨2237528356266533926534415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491685570844355951022943 2237528356266533926534415)
          ·
            refine ⟨3356292534399800889801623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237528356266533926534415 3356292534399800889801623)
            ·
              refine ⟨5034438801599701334702435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356292534399800889801623 5034438801599701334702435)
              ·
                refine ⟨7551658202399552002053653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034438801599701334702435 7551658202399552002053653)
                ·
                  refine ⟨353983978237479000096265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7551658202399552002053653 353983978237479000096265)
                  ·
                    rfl

theorem cell20_775554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_775554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775554 prefixEnd_775554 := by exact prefixLift 775554
  have htrace : WordTrace (prefixWord ++ tailWord_775554) baseStart_775554 baseEnd_775554 := by
    simpa [prefixWord, tailWord_775554, baseEnd_775554] using wordTrace_append hprefix tailTrace_775554
  have hstable : (prefixWord ++ tailWord_775554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775554).length < 2 ^ (prefixWord ++ tailWord_775554).sum := by decide
  have hdescent : baseEnd_775554 < baseStart_775554 := by decide
  rcases family_descends (prefixWord ++ tailWord_775554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775561 : List Nat := [1, 2, 1, 1, 7, 1, 3, 4]
def baseStart_775561 : Nat := 118140960795 + 775561 * 2 ^ 59
def prefixEnd_775561 : Nat := 4983230072969 + 3 ^ 40 * 775561 * 2
def baseEnd_775561 : Nat := 117995724409406028954301

theorem tailTrace_775561 : CollatzResearch.WordTrace tailWord_775561 prefixEnd_775561 117995724409406028954301 := by
  unfold tailWord_775561
  simp only [CollatzResearch.WordTrace]
  refine ⟨28287033543282427118606537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18858022362188284745737691 28287033543282427118606537)
  ·
    refine ⟨21215275157461820338954903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28287033543282427118606537 21215275157461820338954903)
    ·
      refine ⟨31822912736192730508432355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21215275157461820338954903 31822912736192730508432355)
      ·
        refine ⟨47734369104289095762648533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31822912736192730508432355 47734369104289095762648533)
        ·
          refine ⟨1118774275881775681937075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47734369104289095762648533 1118774275881775681937075)
          ·
            refine ⟨1678161413822663522905613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118774275881775681937075 1678161413822663522905613)
            ·
              refine ⟨629310530183498821089605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1678161413822663522905613 629310530183498821089605)
              ·
                refine ⟨117995724409406028954301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629310530183498821089605 117995724409406028954301)
                ·
                  rfl

theorem cell20_775561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_775561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775561 prefixEnd_775561 := by exact prefixLift 775561
  have htrace : WordTrace (prefixWord ++ tailWord_775561) baseStart_775561 baseEnd_775561 := by
    simpa [prefixWord, tailWord_775561, baseEnd_775561] using wordTrace_append hprefix tailTrace_775561
  have hstable : (prefixWord ++ tailWord_775561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775561).length < 2 ^ (prefixWord ++ tailWord_775561).sum := by decide
  have hdescent : baseEnd_775561 < baseStart_775561 := by decide
  rcases family_descends (prefixWord ++ tailWord_775561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775589 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_775589 : Nat := 118140960795 + 775589 * 2 ^ 59
def prefixEnd_775589 : Nat := 4983230072969 + 3 ^ 40 * 775589 * 2
def baseEnd_775589 : Nat := 353999953191174433929455

theorem tailTrace_775589 : CollatzResearch.WordTrace tailWord_775589 prefixEnd_775589 353999953191174433929455 := by
  unfold tailWord_775589
  simp only [CollatzResearch.WordTrace]
  refine ⟨28288054787180987900625821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18858703191453991933750547 28288054787180987900625821)
  ·
    refine ⟨10608020545192870462734683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28288054787180987900625821 10608020545192870462734683)
    ·
      refine ⟨15912030817789305694102025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10608020545192870462734683 15912030817789305694102025)
      ·
        refine ⟨11934023113341979270576519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15912030817789305694102025 11934023113341979270576519)
        ·
          refine ⟨17901034670012968905864779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11934023113341979270576519 17901034670012968905864779)
          ·
            refine ⟨26851552005019453358797169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17901034670012968905864779 26851552005019453358797169)
            ·
              refine ⟨20138664003764590019097877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26851552005019453358797169 20138664003764590019097877)
              ·
                refine ⟨943999875176465157145213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20138664003764590019097877 943999875176465157145213)
                ·
                  refine ⟨353999953191174433929455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 943999875176465157145213 353999953191174433929455)
                  ·
                    rfl

theorem cell20_775589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_775589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775589 prefixEnd_775589 := by exact prefixLift 775589
  have htrace : WordTrace (prefixWord ++ tailWord_775589) baseStart_775589 baseEnd_775589 := by
    simpa [prefixWord, tailWord_775589, baseEnd_775589] using wordTrace_append hprefix tailTrace_775589
  have hstable : (prefixWord ++ tailWord_775589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775589).length < 2 ^ (prefixWord ++ tailWord_775589).sum := by decide
  have hdescent : baseEnd_775589 < baseStart_775589 := by decide
  rcases family_descends (prefixWord ++ tailWord_775589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775596 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_775596 : Nat := 118140960795 + 775596 * 2 ^ 59
def prefixEnd_775596 : Nat := 4983230072969 + 3 ^ 40 * 775596 * 2
def baseEnd_775596 : Nat := 354003148181913520696093

theorem tailTrace_775596 : CollatzResearch.WordTrace tailWord_775596 prefixEnd_775596 354003148181913520696093 := by
  unfold tailWord_775596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14144155049077814048065321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18858873398770418730753761 14144155049077814048065321)
  ·
    refine ⟨10608116286808360536048991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14144155049077814048065321 10608116286808360536048991)
    ·
      refine ⟨15912174430212540804073487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10608116286808360536048991 15912174430212540804073487)
      ·
        refine ⟨23868261645318811206110231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15912174430212540804073487 23868261645318811206110231)
        ·
          refine ⟨35802392467978216809165347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23868261645318811206110231 35802392467978216809165347)
          ·
            refine ⟨53703588701967325213748021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35802392467978216809165347 53703588701967325213748021)
            ·
              refine ⟨5034711440809436738788877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53703588701967325213748021 5034711440809436738788877)
              ·
                refine ⟨1888016790303538777045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5034711440809436738788877 1888016790303538777045829)
                ·
                  refine ⟨354003148181913520696093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888016790303538777045829 354003148181913520696093)
                  ·
                    rfl

theorem cell20_775596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_775596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775596 prefixEnd_775596 := by exact prefixLift 775596
  have htrace : WordTrace (prefixWord ++ tailWord_775596) baseStart_775596 baseEnd_775596 := by
    simpa [prefixWord, tailWord_775596, baseEnd_775596] using wordTrace_append hprefix tailTrace_775596
  have hstable : (prefixWord ++ tailWord_775596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775596).length < 2 ^ (prefixWord ++ tailWord_775596).sum := by decide
  have hdescent : baseEnd_775596 < baseStart_775596 := by decide
  rcases family_descends (prefixWord ++ tailWord_775596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775630 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_775630 : Nat := 118140960795 + 775630 * 2 ^ 59
def prefixEnd_775630 : Nat := 4983230072969 + 3 ^ 40 * 775630 * 2
def baseEnd_775630 : Nat := 354018666708360513562621

theorem tailTrace_775630 : CollatzResearch.WordTrace tailWord_775630 prefixEnd_775630 354018666708360513562621 := by
  unfold tailWord_775630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536193772504056487858543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18859700120021634601912229 3536193772504056487858543)
  ·
    refine ⟨5304290658756084731787815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3536193772504056487858543 5304290658756084731787815)
    ·
      refine ⟨7956435988134127097681723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5304290658756084731787815 7956435988134127097681723)
      ·
        refine ⟨11934653982201190646522585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7956435988134127097681723 11934653982201190646522585)
        ·
          refine ⟨8950990486650892984891939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11934653982201190646522585 8950990486650892984891939)
          ·
            refine ⟨13426485729976339477337909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8950990486650892984891939 13426485729976339477337909)
            ·
              refine ⟨1258733037185281826000429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13426485729976339477337909 1258733037185281826000429)
              ·
                refine ⟨472024888944480684750161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258733037185281826000429 472024888944480684750161)
                ·
                  refine ⟨354018666708360513562621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472024888944480684750161 354018666708360513562621)
                  ·
                    rfl

theorem cell20_775630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_775630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775630 prefixEnd_775630 := by exact prefixLift 775630
  have htrace : WordTrace (prefixWord ++ tailWord_775630) baseStart_775630 baseEnd_775630 := by
    simpa [prefixWord, tailWord_775630, baseEnd_775630] using wordTrace_append hprefix tailTrace_775630
  have hstable : (prefixWord ++ tailWord_775630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775630).length < 2 ^ (prefixWord ++ tailWord_775630).sum := by decide
  have hdescent : baseEnd_775630 < baseStart_775630 := by decide
  rcases family_descends (prefixWord ++ tailWord_775630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775641 : List Nat := [1, 2, 1, 2, 4, 2, 8]
def baseStart_775641 : Nat := 118140960795 + 775641 * 2 ^ 59
def prefixEnd_775641 : Nat := 4983230072969 + 3 ^ 40 * 775641 * 2
def baseEnd_775641 : Nat := 39335965267565929355101

theorem tailTrace_775641 : CollatzResearch.WordTrace tailWord_775641 prefixEnd_775641 39335965267565929355101 := by
  unfold tailWord_775641
  simp only [CollatzResearch.WordTrace]
  refine ⟨28289951382992600781518777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18859967588661733854345851 28289951382992600781518777)
  ·
    refine ⟨21217463537244450586139083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28289951382992600781518777 21217463537244450586139083)
    ·
      refine ⟨31826195305866675879208625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21217463537244450586139083 31826195305866675879208625)
      ·
        refine ⟨23869646479400006909406469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31826195305866675879208625 23869646479400006909406469)
        ·
          refine ⟨4475558714887501295513713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23869646479400006909406469 4475558714887501295513713)
          ·
            refine ⟨3356669036165625971635285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475558714887501295513713 3356669036165625971635285)
            ·
              refine ⟨39335965267565929355101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3356669036165625971635285 39335965267565929355101)
              ·
                rfl

theorem cell20_775641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_775641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775641 prefixEnd_775641 := by exact prefixLift 775641
  have htrace : WordTrace (prefixWord ++ tailWord_775641) baseStart_775641 baseEnd_775641 := by
    simpa [prefixWord, tailWord_775641, baseEnd_775641] using wordTrace_append hprefix tailTrace_775641
  have hstable : (prefixWord ++ tailWord_775641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775641).length < 2 ^ (prefixWord ++ tailWord_775641).sum := by decide
  have hdescent : baseEnd_775641 < baseStart_775641 := by decide
  rcases family_descends (prefixWord ++ tailWord_775641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775651 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_775651 : Nat := 118140960795 + 775651 * 2 ^ 59
def prefixEnd_775651 : Nat := 4983230072969 + 3 ^ 40 * 775651 * 2
def baseEnd_775651 : Nat := 354028251680577773862535

theorem tailTrace_775651 : CollatzResearch.WordTrace tailWord_775651 prefixEnd_775651 354028251680577773862535 := by
  unfold tailWord_775651
  simp only [CollatzResearch.WordTrace]
  refine ⟨28290316112956372489382807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18860210741970914992921871 28290316112956372489382807)
  ·
    refine ⟨42435474169434558734074211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28290316112956372489382807 42435474169434558734074211)
    ·
      refine ⟨63653211254151838101111317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42435474169434558734074211 63653211254151838101111317)
      ·
        refine ⟨2983744277538367410989593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63653211254151838101111317 2983744277538367410989593)
        ·
          refine ⟨2237808208153775558242195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2983744277538367410989593 2237808208153775558242195)
          ·
            refine ⟨3356712312230663337363293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237808208153775558242195 3356712312230663337363293)
            ·
              refine ⟨1258767117086498751511235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3356712312230663337363293 1258767117086498751511235)
              ·
                refine ⟨1888150675629748127266853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258767117086498751511235 1888150675629748127266853)
                ·
                  refine ⟨354028251680577773862535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888150675629748127266853 354028251680577773862535)
                  ·
                    rfl

theorem cell20_775651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_775651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775651 prefixEnd_775651 := by exact prefixLift 775651
  have htrace : WordTrace (prefixWord ++ tailWord_775651) baseStart_775651 baseEnd_775651 := by
    simpa [prefixWord, tailWord_775651, baseEnd_775651] using wordTrace_append hprefix tailTrace_775651
  have hstable : (prefixWord ++ tailWord_775651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775651).length < 2 ^ (prefixWord ++ tailWord_775651).sum := by decide
  have hdescent : baseEnd_775651 < baseStart_775651 := by decide
  rcases family_descends (prefixWord ++ tailWord_775651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775661 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_775661 : Nat := 118140960795 + 775661 * 2 ^ 59
def prefixEnd_775661 : Nat := 4983230072969 + 3 ^ 40 * 775661 * 2
def baseEnd_775661 : Nat := 354032815953062183529161

theorem tailTrace_775661 : CollatzResearch.WordTrace tailWord_775661 prefixEnd_775661 354032815953062183529161 := by
  unfold tailWord_775661
  simp only [CollatzResearch.WordTrace]
  refine ⟨28290680842920144197246837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18860453895280096131497891 28290680842920144197246837)
  ·
    refine ⟨2652251329023763518491891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28290680842920144197246837 2652251329023763518491891)
    ·
      refine ⟨3978376993535645277737837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652251329023763518491891 3978376993535645277737837)
      ·
        refine ⟨1491891372575866979151689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3978376993535645277737837 1491891372575866979151689)
        ·
          refine ⟨1118918529431900234363767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1491891372575866979151689 1118918529431900234363767)
          ·
            refine ⟨1678377794147850351545651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118918529431900234363767 1678377794147850351545651)
            ·
              refine ⟨2517566691221775527318477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678377794147850351545651 2517566691221775527318477)
              ·
                refine ⟨944087509208165822744429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2517566691221775527318477 944087509208165822744429)
                ·
                  refine ⟨354032815953062183529161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944087509208165822744429 354032815953062183529161)
                  ·
                    rfl

theorem cell20_775661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_775661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775661 prefixEnd_775661 := by exact prefixLift 775661
  have htrace : WordTrace (prefixWord ++ tailWord_775661) baseStart_775661 baseEnd_775661 := by
    simpa [prefixWord, tailWord_775661, baseEnd_775661] using wordTrace_append hprefix tailTrace_775661
  have hstable : (prefixWord ++ tailWord_775661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775661).length < 2 ^ (prefixWord ++ tailWord_775661).sum := by decide
  have hdescent : baseEnd_775661 < baseStart_775661 := by decide
  rcases family_descends (prefixWord ++ tailWord_775661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775689 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 2]
def baseStart_775689 : Nat := 118140960795 + 775689 * 2 ^ 59
def prefixEnd_775689 : Nat := 4983230072969 + 3 ^ 40 * 775689 * 2
def baseEnd_775689 : Nat := 354045595916018530595713

theorem tailTrace_775689 : CollatzResearch.WordTrace tailWord_775689 prefixEnd_775689 354045595916018530595713 := by
  unfold tailWord_775689
  simp only [CollatzResearch.WordTrace]
  refine ⟨28291702086818704979266121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18861134724545803319510747 28291702086818704979266121)
  ·
    refine ⟨21218776565114028734449591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28291702086818704979266121 21218776565114028734449591)
    ·
      refine ⟨31828164847671043101674387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21218776565114028734449591 31828164847671043101674387)
      ·
        refine ⟨47742247271506564652511581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31828164847671043101674387 47742247271506564652511581)
        ·
          refine ⟨17903342726814961744691843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47742247271506564652511581 17903342726814961744691843)
          ·
            refine ⟨26855014090222442617037765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17903342726814961744691843 26855014090222442617037765)
            ·
              refine ⟨5035315141916707990694581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26855014090222442617037765 5035315141916707990694581)
              ·
                refine ⟨472060794554691374127617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5035315141916707990694581 472060794554691374127617)
                ·
                  refine ⟨354045595916018530595713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472060794554691374127617 354045595916018530595713)
                  ·
                    rfl

theorem cell20_775689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_775689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775689 prefixEnd_775689 := by exact prefixLift 775689
  have htrace : WordTrace (prefixWord ++ tailWord_775689) baseStart_775689 baseEnd_775689 := by
    simpa [prefixWord, tailWord_775689, baseEnd_775689] using wordTrace_append hprefix tailTrace_775689
  have hstable : (prefixWord ++ tailWord_775689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775689).length < 2 ^ (prefixWord ++ tailWord_775689).sum := by decide
  have hdescent : baseEnd_775689 < baseStart_775689 := by decide
  rcases family_descends (prefixWord ++ tailWord_775689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775724 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_775724 : Nat := 118140960795 + 775724 * 2 ^ 59
def prefixEnd_775724 : Nat := 4983230072969 + 3 ^ 40 * 775724 * 2
def baseEnd_775724 : Nat := 354061570869713964428903

theorem tailTrace_775724 : CollatzResearch.WordTrace tailWord_775724 prefixEnd_775724 354061570869713964428903 := by
  unfold tailWord_775724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146489320845952978395113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18861985761127937304526817 14146489320845952978395113)
  ·
    refine ⟨10609866990634464733796335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14146489320845952978395113 10609866990634464733796335)
    ·
      refine ⟨15914800485951697100694503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609866990634464733796335 15914800485951697100694503)
      ·
        refine ⟨23872200728927545651041755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15914800485951697100694503 23872200728927545651041755)
        ·
          refine ⟨35808301093391318476562633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23872200728927545651041755 35808301093391318476562633)
          ·
            refine ⟨26856225820043488857421975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35808301093391318476562633 26856225820043488857421975)
            ·
              refine ⟨40284338730065233286132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26856225820043488857421975 40284338730065233286132963)
              ·
                refine ⟨60426508095097849929199445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40284338730065233286132963 60426508095097849929199445)
                ·
                  refine ⟨354061570869713964428903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60426508095097849929199445 354061570869713964428903)
                  ·
                    rfl

theorem cell20_775724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_775724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775724 prefixEnd_775724 := by exact prefixLift 775724
  have htrace : WordTrace (prefixWord ++ tailWord_775724) baseStart_775724 baseEnd_775724 := by
    simpa [prefixWord, tailWord_775724, baseEnd_775724] using wordTrace_append hprefix tailTrace_775724
  have hstable : (prefixWord ++ tailWord_775724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775724).length < 2 ^ (prefixWord ++ tailWord_775724).sum := by decide
  have hdescent : baseEnd_775724 < baseStart_775724 := by decide
  rcases family_descends (prefixWord ++ tailWord_775724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775816 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 2]
def baseStart_775816 : Nat := 118140960795 + 775816 * 2 ^ 59
def prefixEnd_775816 : Nat := 4983230072969 + 3 ^ 40 * 775816 * 2
def baseEnd_775816 : Nat := 354103562176570533361861

theorem tailTrace_775816 : CollatzResearch.WordTrace tailWord_775816 prefixEnd_775816 354103562176570533361861 := by
  unfold tailWord_775816
  simp only [CollatzResearch.WordTrace]
  refine ⟨14148167078679302834569651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18864222771572403779426201 14148167078679302834569651)
  ·
    refine ⟨21222250618018954251854477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14148167078679302834569651 21222250618018954251854477)
    ·
      refine ⟨7958343981757107844445429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21222250618018954251854477 7958343981757107844445429)
      ·
        refine ⟨746094748289728860416759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7958343981757107844445429 746094748289728860416759)
        ·
          refine ⟨1119142122434593290625139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746094748289728860416759 1119142122434593290625139)
          ·
            refine ⟨1678713183651889935937709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119142122434593290625139 1678713183651889935937709)
            ·
              refine ⟨629517443869458725976641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1678713183651889935937709 629517443869458725976641)
              ·
                refine ⟨472138082902094044482481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629517443869458725976641 472138082902094044482481)
                ·
                  refine ⟨354103562176570533361861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472138082902094044482481 354103562176570533361861)
                  ·
                    rfl

theorem cell20_775816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_775816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775816 prefixEnd_775816 := by exact prefixLift 775816
  have htrace : WordTrace (prefixWord ++ tailWord_775816) baseStart_775816 baseEnd_775816 := by
    simpa [prefixWord, tailWord_775816, baseEnd_775816] using wordTrace_append hprefix tailTrace_775816
  have hstable : (prefixWord ++ tailWord_775816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775816).length < 2 ^ (prefixWord ++ tailWord_775816).sum := by decide
  have hdescent : baseEnd_775816 < baseStart_775816 := by decide
  rcases family_descends (prefixWord ++ tailWord_775816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775820 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 2]
def baseStart_775820 : Nat := 118140960795 + 775820 * 2 ^ 59
def prefixEnd_775820 : Nat := 4983230072969 + 3 ^ 40 * 775820 * 2
def baseEnd_775820 : Nat := 354105387885564297228511

theorem tailTrace_775820 : CollatzResearch.WordTrace tailWord_775820 prefixEnd_775820 354105387885564297228511 := by
  unfold tailWord_775820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14148240024672057176142457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18864320032896076234856609 14148240024672057176142457)
  ·
    refine ⟨10611180018504042882106843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14148240024672057176142457 10611180018504042882106843)
    ·
      refine ⟨15916770027756064323160265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10611180018504042882106843 15916770027756064323160265)
      ·
        refine ⟨11937577520817048242370199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15916770027756064323160265 11937577520817048242370199)
        ·
          refine ⟨17906366281225572363555299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11937577520817048242370199 17906366281225572363555299)
          ·
            refine ⟨26859549421838358545332949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17906366281225572363555299 26859549421838358545332949)
            ·
              refine ⟨629520689574336528406241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26859549421838358545332949 629520689574336528406241)
              ·
                refine ⟨472140517180752396304681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629520689574336528406241 472140517180752396304681)
                ·
                  refine ⟨354105387885564297228511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472140517180752396304681 354105387885564297228511)
                  ·
                    rfl

theorem cell20_775820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_775820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775820 prefixEnd_775820 := by exact prefixLift 775820
  have htrace : WordTrace (prefixWord ++ tailWord_775820) baseStart_775820 baseEnd_775820 := by
    simpa [prefixWord, tailWord_775820, baseEnd_775820] using wordTrace_append hprefix tailTrace_775820
  have hstable : (prefixWord ++ tailWord_775820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775820).length < 2 ^ (prefixWord ++ tailWord_775820).sum := by decide
  have hdescent : baseEnd_775820 < baseStart_775820 := by decide
  rcases family_descends (prefixWord ++ tailWord_775820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775831 : List Nat := [1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_775831 : Nat := 118140960795 + 775831 * 2 ^ 59
def prefixEnd_775831 : Nat := 4983230072969 + 3 ^ 40 * 775831 * 2
def baseEnd_775831 : Nat := 118036802861765715953933

theorem tailTrace_775831 : CollatzResearch.WordTrace tailWord_775831 prefixEnd_775831 118036802861765715953933 := by
  unfold tailWord_775831
  simp only [CollatzResearch.WordTrace]
  refine ⟨28296881252304263230935347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18864587501536175487290231 28296881252304263230935347)
  ·
    refine ⟨42445321878456394846403021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28296881252304263230935347 42445321878456394846403021)
    ·
      refine ⟨15916995704421148067401133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42445321878456394846403021 15916995704421148067401133)
      ·
        refine ⟨5968873389157930525275425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15916995704421148067401133 5968873389157930525275425)
        ·
          refine ⟨4476655041868447893956569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5968873389157930525275425 4476655041868447893956569)
          ·
            refine ⟨3357491281401335920467427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476655041868447893956569 3357491281401335920467427)
            ·
              refine ⟨5036236922102003880701141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357491281401335920467427 5036236922102003880701141)
              ·
                refine ⟨118036802861765715953933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5036236922102003880701141 118036802861765715953933)
                ·
                  rfl

theorem cell20_775831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_775831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775831 prefixEnd_775831 := by exact prefixLift 775831
  have htrace : WordTrace (prefixWord ++ tailWord_775831) baseStart_775831 baseEnd_775831 := by
    simpa [prefixWord, tailWord_775831, baseEnd_775831] using wordTrace_append hprefix tailTrace_775831
  have hstable : (prefixWord ++ tailWord_775831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775831).length < 2 ^ (prefixWord ++ tailWord_775831).sum := by decide
  have hdescent : baseEnd_775831 < baseStart_775831 := by decide
  rcases family_descends (prefixWord ++ tailWord_775831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775879 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 2]
def baseStart_775879 : Nat := 118140960795 + 775879 * 2 ^ 59
def prefixEnd_775879 : Nat := 4983230072969 + 3 ^ 40 * 775879 * 2
def baseEnd_775879 : Nat := 354132317093222314261603

theorem tailTrace_775879 : CollatzResearch.WordTrace tailWord_775879 prefixEnd_775879 354132317093222314261603 := by
  unfold tailWord_775879
  simp only [CollatzResearch.WordTrace]
  refine ⟨28298631956130367428682691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18865754637420244952455127 28298631956130367428682691)
  ·
    refine ⟨42447947934195551143024037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28298631956130367428682691 42447947934195551143024037)
    ·
      refine ⟨7958990237661665839317007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42447947934195551143024037 7958990237661665839317007)
      ·
        refine ⟨11938485356492498758975511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7958990237661665839317007 11938485356492498758975511)
        ·
          refine ⟨17907728034738748138463267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11938485356492498758975511 17907728034738748138463267)
          ·
            refine ⟨26861592052108122207694901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17907728034738748138463267 26861592052108122207694901)
            ·
              refine ⟨2518274254885136456971397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26861592052108122207694901 2518274254885136456971397)
              ·
                refine ⟨472176422790963085682137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2518274254885136456971397 472176422790963085682137)
                ·
                  refine ⟨354132317093222314261603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472176422790963085682137 354132317093222314261603)
                  ·
                    rfl

theorem cell20_775879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 2].length) (baseStart_775879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775879 prefixEnd_775879 := by exact prefixLift 775879
  have htrace : WordTrace (prefixWord ++ tailWord_775879) baseStart_775879 baseEnd_775879 := by
    simpa [prefixWord, tailWord_775879, baseEnd_775879] using wordTrace_append hprefix tailTrace_775879
  have hstable : (prefixWord ++ tailWord_775879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775879).length < 2 ^ (prefixWord ++ tailWord_775879).sum := by decide
  have hdescent : baseEnd_775879 < baseStart_775879 := by decide
  rcases family_descends (prefixWord ++ tailWord_775879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775883 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_775883 : Nat := 118140960795 + 775883 * 2 ^ 59
def prefixEnd_775883 : Nat := 4983230072969 + 3 ^ 40 * 775883 * 2
def baseEnd_775883 : Nat := 354134142802216078128253

theorem tailTrace_775883 : CollatzResearch.WordTrace tailWord_775883 prefixEnd_775883 354134142802216078128253 := by
  unfold tailWord_775883
  simp only [CollatzResearch.WordTrace]
  refine ⟨28298777848115876111828303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18865851898743917407885535 28298777848115876111828303)
  ·
    refine ⟨42448166772173814167742455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28298777848115876111828303 42448166772173814167742455)
    ·
      refine ⟨63672250158260721251613683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42448166772173814167742455 63672250158260721251613683)
      ·
        refine ⟨95508375237391081877420525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63672250158260721251613683 95508375237391081877420525)
        ·
          refine ⟨35815640714021655704032697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95508375237391081877420525 35815640714021655704032697)
          ·
            refine ⟨26861730535516241778024523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35815640714021655704032697 26861730535516241778024523)
            ·
              refine ⟨40292595803274362667036785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26861730535516241778024523 40292595803274362667036785)
              ·
                refine ⟨30219446852455772000277589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40292595803274362667036785 30219446852455772000277589)
                ·
                  refine ⟨354134142802216078128253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30219446852455772000277589 354134142802216078128253)
                  ·
                    rfl

theorem cell20_775883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_775883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775883 prefixEnd_775883 := by exact prefixLift 775883
  have htrace : WordTrace (prefixWord ++ tailWord_775883) baseStart_775883 baseEnd_775883 := by
    simpa [prefixWord, tailWord_775883, baseEnd_775883] using wordTrace_append hprefix tailTrace_775883
  have hstable : (prefixWord ++ tailWord_775883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775883).length < 2 ^ (prefixWord ++ tailWord_775883).sum := by decide
  have hdescent : baseEnd_775883 < baseStart_775883 := by decide
  rcases family_descends (prefixWord ++ tailWord_775883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775934 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_775934 : Nat := 118140960795 + 775934 * 2 ^ 59
def prefixEnd_775934 : Nat := 4983230072969 + 3 ^ 40 * 775934 * 2
def baseEnd_775934 : Nat := 354157420591886567428045

theorem tailTrace_775934 : CollatzResearch.WordTrace tailWord_775934 prefixEnd_775934 354157420591886567428045 := by
  unfold tailWord_775934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537579746366388977741857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18867091980620741214623237 3537579746366388977741857)
  ·
    refine ⟨2653184809774791733306393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3537579746366388977741857 2653184809774791733306393)
    ·
      refine ⟨1989888607331093799979795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2653184809774791733306393 1989888607331093799979795)
      ·
        refine ⟨2984832910996640699969693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989888607331093799979795 2984832910996640699969693)
        ·
          refine ⟨1119312341623740262488635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2984832910996640699969693 1119312341623740262488635)
          ·
            refine ⟨1678968512435610393732953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119312341623740262488635 1678968512435610393732953)
            ·
              refine ⟨1259226384326707795299715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1678968512435610393732953 1259226384326707795299715)
              ·
                refine ⟨1888839576490061692949573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259226384326707795299715 1888839576490061692949573)
                ·
                  refine ⟨354157420591886567428045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888839576490061692949573 354157420591886567428045)
                  ·
                    rfl

theorem cell20_775934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_775934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775934 prefixEnd_775934 := by exact prefixLift 775934
  have htrace : WordTrace (prefixWord ++ tailWord_775934) baseStart_775934 baseEnd_775934 := by
    simpa [prefixWord, tailWord_775934, baseEnd_775934] using wordTrace_append hprefix tailTrace_775934
  have hstable : (prefixWord ++ tailWord_775934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775934).length < 2 ^ (prefixWord ++ tailWord_775934).sum := by decide
  have hdescent : baseEnd_775934 < baseStart_775934 := by decide
  rcases family_descends (prefixWord ++ tailWord_775934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775962 : List Nat := [3, 1, 1, 3, 2, 2, 4, 4]
def baseStart_775962 : Nat := 118140960795 + 775962 * 2 ^ 59
def prefixEnd_775962 : Nat := 4983230072969 + 3 ^ 40 * 775962 * 2
def baseEnd_775962 : Nat := 118056733518280971498199

theorem tailTrace_775962 : CollatzResearch.WordTrace tailWord_775962 prefixEnd_775962 118056733518280971498199 := by
  unfold tailWord_775962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075414803707418150988535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18867772809886448402636093 7075414803707418150988535)
  ·
    refine ⟨10613122205561127226482803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7075414803707418150988535 10613122205561127226482803)
    ·
      refine ⟨15919683308341690839724205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10613122205561127226482803 15919683308341690839724205)
      ·
        refine ⟨5969881240628134064896577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15919683308341690839724205 5969881240628134064896577)
        ·
          refine ⟨4477410930471100548672433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5969881240628134064896577 4477410930471100548672433)
          ·
            refine ⟨3358058197853325411504325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4477410930471100548672433 3358058197853325411504325)
            ·
              refine ⟨629635912097498514657061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3358058197853325411504325 629635912097498514657061)
              ·
                refine ⟨118056733518280971498199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629635912097498514657061 118056733518280971498199)
                ·
                  rfl

theorem cell20_775962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_775962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775962 prefixEnd_775962 := by exact prefixLift 775962
  have htrace : WordTrace (prefixWord ++ tailWord_775962) baseStart_775962 baseEnd_775962 := by
    simpa [prefixWord, tailWord_775962, baseEnd_775962] using wordTrace_append hprefix tailTrace_775962
  have hstable : (prefixWord ++ tailWord_775962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775962).length < 2 ^ (prefixWord ++ tailWord_775962).sum := by decide
  have hdescent : baseEnd_775962 < baseStart_775962 := by decide
  rcases family_descends (prefixWord ++ tailWord_775962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775972 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 2]
def baseStart_775972 : Nat := 118140960795 + 775972 * 2 ^ 59
def prefixEnd_775972 : Nat := 4983230072969 + 3 ^ 40 * 775972 * 2
def baseEnd_775972 : Nat := 354174764827327324161223

theorem tailTrace_775972 : CollatzResearch.WordTrace tailWord_775972 prefixEnd_775972 354174764827327324161223 := by
  unfold tailWord_775972
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151011972396722155909085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18868015963195629541212113 14151011972396722155909085)
  ·
    refine ⟨5306629489648770808465907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14151011972396722155909085 5306629489648770808465907)
    ·
      refine ⟨7959944234473156212698861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5306629489648770808465907 7959944234473156212698861)
      ·
        refine ⟨2984979087927433579762073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7959944234473156212698861 2984979087927433579762073)
        ·
          refine ⟨2238734315945575184821555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984979087927433579762073 2238734315945575184821555)
          ·
            refine ⟨3358101473918362777232333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238734315945575184821555 3358101473918362777232333)
            ·
              refine ⟨1259288052719386041462125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3358101473918362777232333 1259288052719386041462125)
              ·
                refine ⟨472233019769769765548297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1259288052719386041462125 472233019769769765548297)
                ·
                  refine ⟨354174764827327324161223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472233019769769765548297 354174764827327324161223)
                  ·
                    rfl

theorem cell20_775972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_775972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775972 prefixEnd_775972 := by exact prefixLift 775972
  have htrace : WordTrace (prefixWord ++ tailWord_775972) baseStart_775972 baseEnd_775972 := by
    simpa [prefixWord, tailWord_775972, baseEnd_775972] using wordTrace_append hprefix tailTrace_775972
  have hstable : (prefixWord ++ tailWord_775972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775972).length < 2 ^ (prefixWord ++ tailWord_775972).sum := by decide
  have hdescent : baseEnd_775972 < baseStart_775972 := by decide
  rcases family_descends (prefixWord ++ tailWord_775972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775989 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 2]
def baseStart_775989 : Nat := 118140960795 + 775989 * 2 ^ 59
def prefixEnd_775989 : Nat := 4983230072969 + 3 ^ 40 * 775989 * 2
def baseEnd_775989 : Nat := 354182524090550820594487

theorem tailTrace_775989 : CollatzResearch.WordTrace tailWord_775989 prefixEnd_775989 354182524090550820594487 := by
  unfold tailWord_775989
  simp only [CollatzResearch.WordTrace]
  refine ⟨28302643985731856215187021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18868429323821237476791347 28302643985731856215187021)
  ·
    refine ⟨10613491494649446080695133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28302643985731856215187021 10613491494649446080695133)
    ·
      refine ⟨3980059310493542280260675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10613491494649446080695133 3980059310493542280260675)
      ·
        refine ⟨5970088965740313420391013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980059310493542280260675 5970088965740313420391013)
        ·
          refine ⟨1119391681076308766323315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5970088965740313420391013 1119391681076308766323315)
          ·
            refine ⟨1679087521614463149484973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119391681076308766323315 1679087521614463149484973)
            ·
              refine ⟨629657820605423681056865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1679087521614463149484973 629657820605423681056865)
              ·
                refine ⟨472243365454067760792649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629657820605423681056865 472243365454067760792649)
                ·
                  refine ⟨354182524090550820594487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472243365454067760792649 354182524090550820594487)
                  ·
                    rfl

theorem cell20_775989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_775989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_775989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_775989 prefixEnd_775989 := by exact prefixLift 775989
  have htrace : WordTrace (prefixWord ++ tailWord_775989) baseStart_775989 baseEnd_775989 := by
    simpa [prefixWord, tailWord_775989, baseEnd_775989] using wordTrace_append hprefix tailTrace_775989
  have hstable : (prefixWord ++ tailWord_775989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775989).length < 2 ^ (prefixWord ++ tailWord_775989).sum := by decide
  have hdescent : baseEnd_775989 < baseStart_775989 := by decide
  rcases family_descends (prefixWord ++ tailWord_775989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776021 : List Nat := [1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_776021 : Nat := 118140960795 + 776021 * 2 ^ 59
def prefixEnd_776021 : Nat := 4983230072969 + 3 ^ 40 * 776021 * 2
def baseEnd_776021 : Nat := 118065709920833643842563

theorem tailTrace_776021 : CollatzResearch.WordTrace tailWord_776021 prefixEnd_776021 118065709920833643842563 := by
  unfold tailWord_776021
  simp only [CollatzResearch.WordTrace]
  refine ⟨28303811121615925680351917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18869207414410617120234611 28303811121615925680351917)
  ·
    refine ⟨10613929170605972130131969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28303811121615925680351917 10613929170605972130131969)
    ·
      refine ⟨7960446877954479097598977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10613929170605972130131969 7960446877954479097598977)
      ·
        refine ⟨5970335158465859323199233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7960446877954479097598977 5970335158465859323199233)
        ·
          refine ⟨4477751368849394492399425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970335158465859323199233 4477751368849394492399425)
          ·
            refine ⟨3358313526637045869299569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4477751368849394492399425 3358313526637045869299569)
            ·
              refine ⟨2518735144977784401974677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358313526637045869299569 2518735144977784401974677)
              ·
                refine ⟨118065709920833643842563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2518735144977784401974677 118065709920833643842563)
                ·
                  rfl

theorem cell20_776021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_776021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776021 prefixEnd_776021 := by exact prefixLift 776021
  have htrace : WordTrace (prefixWord ++ tailWord_776021) baseStart_776021 baseEnd_776021 := by
    simpa [prefixWord, tailWord_776021, baseEnd_776021] using wordTrace_append hprefix tailTrace_776021
  have hstable : (prefixWord ++ tailWord_776021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776021).length < 2 ^ (prefixWord ++ tailWord_776021).sum := by decide
  have hdescent : baseEnd_776021 < baseStart_776021 := by decide
  rcases family_descends (prefixWord ++ tailWord_776021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776045 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_776045 : Nat := 118140960795 + 776045 * 2 ^ 59
def prefixEnd_776045 : Nat := 4983230072969 + 3 ^ 40 * 776045 * 2
def baseEnd_776045 : Nat := 354208084016463514727591

theorem tailTrace_776045 : CollatzResearch.WordTrace tailWord_776045 prefixEnd_776045 354208084016463514727591 := by
  unfold tailWord_776045
  simp only [CollatzResearch.WordTrace]
  refine ⟨28304686473528977779225589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18869790982352651852817059 28304686473528977779225589)
  ·
    refine ⟨2653564356893341666802399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28304686473528977779225589 2653564356893341666802399)
    ·
      refine ⟨3980346535340012500203599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653564356893341666802399 3980346535340012500203599)
      ·
        refine ⟨5970519803010018750305399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980346535340012500203599 5970519803010018750305399)
        ·
          refine ⟨8955779704515028125458099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970519803010018750305399 8955779704515028125458099)
          ·
            refine ⟨13433669556772542188187149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8955779704515028125458099 13433669556772542188187149)
            ·
              refine ⟨5037626083789703320570181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13433669556772542188187149 5037626083789703320570181)
              ·
                refine ⟨944554890710569372606909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5037626083789703320570181 944554890710569372606909)
                ·
                  refine ⟨354208084016463514727591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944554890710569372606909 354208084016463514727591)
                  ·
                    rfl

theorem cell20_776045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_776045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776045 prefixEnd_776045 := by exact prefixLift 776045
  have htrace : WordTrace (prefixWord ++ tailWord_776045) baseStart_776045 baseEnd_776045 := by
    simpa [prefixWord, tailWord_776045, baseEnd_776045] using wordTrace_append hprefix tailTrace_776045
  have hstable : (prefixWord ++ tailWord_776045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776045).length < 2 ^ (prefixWord ++ tailWord_776045).sum := by decide
  have hdescent : baseEnd_776045 < baseStart_776045 := by decide
  rcases family_descends (prefixWord ++ tailWord_776045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776100 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_776100 : Nat := 118140960795 + 776100 * 2 ^ 59
def prefixEnd_776100 : Nat := 4983230072969 + 3 ^ 40 * 776100 * 2
def baseEnd_776100 : Nat := 354233187515127767894033

theorem tailTrace_776100 : CollatzResearch.WordTrace tailWord_776100 prefixEnd_776100 354233187515127767894033 := by
  unfold tailWord_776100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153346244164861086238877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18871128325553148114985169 14153346244164861086238877)
  ·
    refine ⟨5307504841561822907339579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14153346244164861086238877 5307504841561822907339579)
    ·
      refine ⟨7961257262342734361009369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5307504841561822907339579 7961257262342734361009369)
      ·
        refine ⟨5970942946757050770757027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7961257262342734361009369 5970942946757050770757027)
        ·
          refine ⟨8956414420135576156135541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970942946757050770757027 8956414420135576156135541)
          ·
            refine ⟨839663851887710264637707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8956414420135576156135541 839663851887710264637707)
            ·
              refine ⟨1259495777831565396956561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839663851887710264637707 1259495777831565396956561)
              ·
                refine ⟨944621833373674047717421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259495777831565396956561 944621833373674047717421)
                ·
                  refine ⟨354233187515127767894033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944621833373674047717421 354233187515127767894033)
                  ·
                    rfl

theorem cell20_776100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_776100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776100 prefixEnd_776100 := by exact prefixLift 776100
  have htrace : WordTrace (prefixWord ++ tailWord_776100) baseStart_776100 baseEnd_776100 := by
    simpa [prefixWord, tailWord_776100, baseEnd_776100] using wordTrace_append hprefix tailTrace_776100
  have hstable : (prefixWord ++ tailWord_776100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776100).length < 2 ^ (prefixWord ++ tailWord_776100).sum := by decide
  have hdescent : baseEnd_776100 < baseStart_776100 := by decide
  rcases family_descends (prefixWord ++ tailWord_776100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776142 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_776142 : Nat := 118140960795 + 776142 * 2 ^ 59
def prefixEnd_776142 : Nat := 4983230072969 + 3 ^ 40 * 776142 * 2
def baseEnd_776142 : Nat := 354252357459562288493861

theorem tailTrace_776142 : CollatzResearch.WordTrace tailWord_776142 prefixEnd_776142 354252357459562288493861 := by
  unfold tailWord_776142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538528044272195418188335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18872149569451708897004453 3538528044272195418188335)
  ·
    refine ⟨5307792066408293127282503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538528044272195418188335 5307792066408293127282503)
    ·
      refine ⟨7961688099612439690923755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5307792066408293127282503 7961688099612439690923755)
      ·
        refine ⟨11942532149418659536385633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961688099612439690923755 11942532149418659536385633)
        ·
          refine ⟨8956899112063994652289225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11942532149418659536385633 8956899112063994652289225)
          ·
            refine ⟨6717674334047995989216919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8956899112063994652289225 6717674334047995989216919)
            ·
              refine ⟨10076511501071993983825379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717674334047995989216919 10076511501071993983825379)
              ·
                refine ⟨15114767251607990975738069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10076511501071993983825379 15114767251607990975738069)
                ·
                  refine ⟨354252357459562288493861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15114767251607990975738069 354252357459562288493861)
                  ·
                    rfl

theorem cell20_776142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_776142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776142 prefixEnd_776142 := by exact prefixLift 776142
  have htrace : WordTrace (prefixWord ++ tailWord_776142) baseStart_776142 baseEnd_776142 := by
    simpa [prefixWord, tailWord_776142, baseEnd_776142] using wordTrace_append hprefix tailTrace_776142
  have hstable : (prefixWord ++ tailWord_776142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776142).length < 2 ^ (prefixWord ++ tailWord_776142).sum := by decide
  have hdescent : baseEnd_776142 < baseStart_776142 := by decide
  rcases family_descends (prefixWord ++ tailWord_776142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776187 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_776187 : Nat := 118140960795 + 776187 * 2 ^ 59
def prefixEnd_776187 : Nat := 4983230072969 + 3 ^ 40 * 776187 * 2
def baseEnd_776187 : Nat := 354272896685742131993677

theorem tailTrace_776187 : CollatzResearch.WordTrace tailWord_776187 prefixEnd_776187 354272896685742131993677 := by
  unfold tailWord_776187
  simp only [CollatzResearch.WordTrace]
  refine ⟨28309865639014536030894815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18873243759343024020596543 28309865639014536030894815)
  ·
    refine ⟨42464798458521804046342223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28309865639014536030894815 42464798458521804046342223)
    ·
      refine ⟨63697197687782706069513335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42464798458521804046342223 63697197687782706069513335)
      ·
        refine ⟨95545796531674059104270003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63697197687782706069513335 95545796531674059104270003)
        ·
          refine ⟨143318694797511088656405005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95545796531674059104270003 143318694797511088656405005)
          ·
            refine ⟨53744510549066658246151877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143318694797511088656405005 53744510549066658246151877)
            ·
              refine ⟨10077095727949998421153477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53744510549066658246151877 10077095727949998421153477)
              ·
                refine ⟨1889455448990624703966277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10077095727949998421153477 1889455448990624703966277)
                ·
                  refine ⟨354272896685742131993677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889455448990624703966277 354272896685742131993677)
                  ·
                    rfl

theorem cell20_776187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_776187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776187 prefixEnd_776187 := by exact prefixLift 776187
  have htrace : WordTrace (prefixWord ++ tailWord_776187) baseStart_776187 baseEnd_776187 := by
    simpa [prefixWord, tailWord_776187, baseEnd_776187] using wordTrace_append hprefix tailTrace_776187
  have hstable : (prefixWord ++ tailWord_776187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776187).length < 2 ^ (prefixWord ++ tailWord_776187).sum := by decide
  have hdescent : baseEnd_776187 < baseStart_776187 := by decide
  rcases family_descends (prefixWord ++ tailWord_776187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776190 : List Nat := [4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_776190 : Nat := 118140960795 + 776190 * 2 ^ 59
def prefixEnd_776190 : Nat := 4983230072969 + 3 ^ 40 * 776190 * 2
def baseEnd_776190 : Nat := 118091421989162484964555

theorem tailTrace_776190 : CollatzResearch.WordTrace tailWord_776190 prefixEnd_776190 118091421989162484964555 := by
  unfold tailWord_776190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538746882250458442906753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18873316705335778362169349 3538746882250458442906753)
  ·
    refine ⟨2654060161687843832180065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3538746882250458442906753 2654060161687843832180065)
    ·
      refine ⟨1990545121265882874135049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2654060161687843832180065 1990545121265882874135049)
      ·
        refine ⟨1492908840949412155601287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1990545121265882874135049 1492908840949412155601287)
        ·
          refine ⟨2239363261424118233401931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492908840949412155601287 2239363261424118233401931)
          ·
            refine ⟨3359044892136177350102897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239363261424118233401931 3359044892136177350102897)
            ·
              refine ⟨2519283669102133012577173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3359044892136177350102897 2519283669102133012577173)
              ·
                refine ⟨118091421989162484964555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2519283669102133012577173 118091421989162484964555)
                ·
                  rfl

theorem cell20_776190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_776190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776190 prefixEnd_776190 := by exact prefixLift 776190
  have htrace : WordTrace (prefixWord ++ tailWord_776190) baseStart_776190 baseEnd_776190 := by
    simpa [prefixWord, tailWord_776190, baseEnd_776190] using wordTrace_append hprefix tailTrace_776190
  have hstable : (prefixWord ++ tailWord_776190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776190).length < 2 ^ (prefixWord ++ tailWord_776190).sum := by decide
  have hdescent : baseEnd_776190 < baseStart_776190 := by decide
  rcases family_descends (prefixWord ++ tailWord_776190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776242 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_776242 : Nat := 118140960795 + 776242 * 2 ^ 59
def prefixEnd_776242 : Nat := 4983230072969 + 3 ^ 40 * 776242 * 2
def baseEnd_776242 : Nat := 354298000184406385160119

theorem tailTrace_776242 : CollatzResearch.WordTrace tailWord_776242 prefixEnd_776242 354298000184406385160119 := by
  unfold tailWord_776242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077967913453820106036745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18874581102543520282764653 7077967913453820106036745)
  ·
    refine ⟨5308475935090365079527559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7077967913453820106036745 5308475935090365079527559)
    ·
      refine ⟨7962713902635547619291339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308475935090365079527559 7962713902635547619291339)
      ·
        refine ⟨11944070853953321428937009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7962713902635547619291339 11944070853953321428937009)
        ·
          refine ⟨8958053140464991071702757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11944070853953321428937009 8958053140464991071702757)
          ·
            refine ⟨1679634963837185825944267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8958053140464991071702757 1679634963837185825944267)
            ·
              refine ⟨2519452445755778738916401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679634963837185825944267 2519452445755778738916401)
              ·
                refine ⟨1889589334316834054187301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519452445755778738916401 1889589334316834054187301)
                ·
                  refine ⟨354298000184406385160119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889589334316834054187301 354298000184406385160119)
                  ·
                    rfl

theorem cell20_776242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_776242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776242 prefixEnd_776242 := by exact prefixLift 776242
  have htrace : WordTrace (prefixWord ++ tailWord_776242) baseStart_776242 baseEnd_776242 := by
    simpa [prefixWord, tailWord_776242, baseEnd_776242] using wordTrace_append hprefix tailTrace_776242
  have hstable : (prefixWord ++ tailWord_776242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776242).length < 2 ^ (prefixWord ++ tailWord_776242).sum := by decide
  have hdescent : baseEnd_776242 < baseStart_776242 := by decide
  rcases family_descends (prefixWord ++ tailWord_776242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776263 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_776263 : Nat := 118140960795 + 776263 * 2 ^ 59
def prefixEnd_776263 : Nat := 4983230072969 + 3 ^ 40 * 776263 * 2
def baseEnd_776263 : Nat := 354307585156623645460033

theorem tailTrace_776263 : CollatzResearch.WordTrace tailWord_776263 prefixEnd_776263 354307585156623645460033 := by
  unfold tailWord_776263
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312637586739201010661443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18875091724492800673774295 28312637586739201010661443)
  ·
    refine ⟨42468956380108801515992165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28312637586739201010661443 42468956380108801515992165)
    ·
      refine ⟨7962929321270400284248531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42468956380108801515992165 7962929321270400284248531)
      ·
        refine ⟨11944393981905600426372797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7962929321270400284248531 11944393981905600426372797)
        ·
          refine ⟨4479147743214600159889799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11944393981905600426372797 4479147743214600159889799)
          ·
            refine ⟨6718721614821900239834699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479147743214600159889799 6718721614821900239834699)
            ·
              refine ⟨10078082422232850359752049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718721614821900239834699 10078082422232850359752049)
              ·
                refine ⟨7558561816674637769814037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10078082422232850359752049 7558561816674637769814037)
                ·
                  refine ⟨354307585156623645460033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7558561816674637769814037 354307585156623645460033)
                  ·
                    rfl

theorem cell20_776263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_776263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776263 prefixEnd_776263 := by exact prefixLift 776263
  have htrace : WordTrace (prefixWord ++ tailWord_776263) baseStart_776263 baseEnd_776263 := by
    simpa [prefixWord, tailWord_776263, baseEnd_776263] using wordTrace_append hprefix tailTrace_776263
  have hstable : (prefixWord ++ tailWord_776263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776263).length < 2 ^ (prefixWord ++ tailWord_776263).sum := by decide
  have hdescent : baseEnd_776263 < baseStart_776263 := by decide
  rcases family_descends (prefixWord ++ tailWord_776263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776280 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_776280 : Nat := 118140960795 + 776280 * 2 ^ 59
def prefixEnd_776280 : Nat := 4983230072969 + 3 ^ 40 * 776280 * 2
def baseEnd_776280 : Nat := 354315344419847141893297

theorem tailTrace_776280 : CollatzResearch.WordTrace tailWord_776280 prefixEnd_776280 354315344419847141893297 := by
  unfold tailWord_776280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14156628813838806457015147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18875505085118408609353529 14156628813838806457015147)
  ·
    refine ⟨21234943220758209685522721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14156628813838806457015147 21234943220758209685522721)
    ·
      refine ⟨15926207415568657264142041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21234943220758209685522721 15926207415568657264142041)
      ·
        refine ⟨11944655561676492948106531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15926207415568657264142041 11944655561676492948106531)
        ·
          refine ⟨17916983342514739422159797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11944655561676492948106531 17916983342514739422159797)
          ·
            refine ⟨1679717188360756820827481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17916983342514739422159797 1679717188360756820827481)
            ·
              refine ⟨1259787891270567615620611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679717188360756820827481 1259787891270567615620611)
              ·
                refine ⟨1889681836905851423430917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259787891270567615620611 1889681836905851423430917)
                ·
                  refine ⟨354315344419847141893297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889681836905851423430917 354315344419847141893297)
                  ·
                    rfl

theorem cell20_776280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_776280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776280 prefixEnd_776280 := by exact prefixLift 776280
  have htrace : WordTrace (prefixWord ++ tailWord_776280) baseStart_776280 baseEnd_776280 := by
    simpa [prefixWord, tailWord_776280, baseEnd_776280] using wordTrace_append hprefix tailTrace_776280
  have hstable : (prefixWord ++ tailWord_776280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776280).length < 2 ^ (prefixWord ++ tailWord_776280).sum := by decide
  have hdescent : baseEnd_776280 < baseStart_776280 := by decide
  rcases family_descends (prefixWord ++ tailWord_776280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776304 : List Nat := [2, 1, 1, 1, 5, 4, 2, 4]
def baseStart_776304 : Nat := 118140960795 + 776304 * 2 ^ 59
def prefixEnd_776304 : Nat := 4983230072969 + 3 ^ 40 * 776304 * 2
def baseEnd_776304 : Nat := 118108766224603241697733

theorem tailTrace_776304 : CollatzResearch.WordTrace tailWord_776304 prefixEnd_776304 118108766224603241697733 := by
  unfold tailWord_776304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157066489795332506451983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18876088653060443341935977 14157066489795332506451983)
  ·
    refine ⟨21235599734692998759677975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14157066489795332506451983 21235599734692998759677975)
    ·
      refine ⟨31853399602039498139516963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21235599734692998759677975 31853399602039498139516963)
      ·
        refine ⟨47780099403059247209275445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31853399602039498139516963 47780099403059247209275445)
        ·
          refine ⟨4479384319036804425869573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47780099403059247209275445 4479384319036804425869573)
          ·
            refine ⟨839884559819400829850545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4479384319036804425869573 839884559819400829850545)
            ·
              refine ⟨629913419864550622387909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839884559819400829850545 629913419864550622387909)
              ·
                refine ⟨118108766224603241697733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629913419864550622387909 118108766224603241697733)
                ·
                  rfl

theorem cell20_776304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_776304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776304 prefixEnd_776304 := by exact prefixLift 776304
  have htrace : WordTrace (prefixWord ++ tailWord_776304) baseStart_776304 baseEnd_776304 := by
    simpa [prefixWord, tailWord_776304, baseEnd_776304] using wordTrace_append hprefix tailTrace_776304
  have hstable : (prefixWord ++ tailWord_776304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776304).length < 2 ^ (prefixWord ++ tailWord_776304).sum := by decide
  have hdescent : baseEnd_776304 < baseStart_776304 := by decide
  rcases family_descends (prefixWord ++ tailWord_776304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776325 : List Nat := [1, 3, 1, 1, 5, 3, 6]
def baseStart_776325 : Nat := 118140960795 + 776325 * 2 ^ 59
def prefixEnd_776325 : Nat := 4983230072969 + 3 ^ 40 * 776325 * 2
def baseEnd_776325 : Nat := 39370653738447442821457

theorem tailTrace_776325 : CollatzResearch.WordTrace tailWord_776325 prefixEnd_776325 39370653738447442821457 := by
  unfold tailWord_776325
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314898912514585599418429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18876599275009723732945619 28314898912514585599418429)
  ·
    refine ⟨10618087092192969599781911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28314898912514585599418429 10618087092192969599781911)
    ·
      refine ⟨15927130638289454399672867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10618087092192969599781911 15927130638289454399672867)
      ·
        refine ⟨23890695957434181599509301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15927130638289454399672867 23890695957434181599509301)
        ·
          refine ⟨2239752746009454524953997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23890695957434181599509301 2239752746009454524953997)
          ·
            refine ⟨839907279753545446857749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2239752746009454524953997 839907279753545446857749)
            ·
              refine ⟨39370653738447442821457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 839907279753545446857749 39370653738447442821457)
              ·
                rfl

theorem cell20_776325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_776325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776325 prefixEnd_776325 := by exact prefixLift 776325
  have htrace : WordTrace (prefixWord ++ tailWord_776325) baseStart_776325 baseEnd_776325 := by
    simpa [prefixWord, tailWord_776325, baseEnd_776325] using wordTrace_append hprefix tailTrace_776325
  have hstable : (prefixWord ++ tailWord_776325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776325).length < 2 ^ (prefixWord ++ tailWord_776325).sum := by decide
  have hdescent : baseEnd_776325 < baseStart_776325 := by decide
  rcases family_descends (prefixWord ++ tailWord_776325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776349 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_776349 : Nat := 118140960795 + 776349 * 2 ^ 59
def prefixEnd_776349 : Nat := 4983230072969 + 3 ^ 40 * 776349 * 2
def baseEnd_776349 : Nat := 354346837899989568593015

theorem tailTrace_776349 : CollatzResearch.WordTrace tailWord_776349 prefixEnd_776349 354346837899989568593015 := by
  unfold tailWord_776349
  simp only [CollatzResearch.WordTrace]
  refine ⟨28315774264427637698292101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18877182842951758465528067 28315774264427637698292101)
  ·
    refine ⟨5309207674580182068429769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28315774264427637698292101 5309207674580182068429769)
    ·
      refine ⟨3981905755935136551322327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5309207674580182068429769 3981905755935136551322327)
      ·
        refine ⟨5972858633902704826983491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981905755935136551322327 5972858633902704826983491)
        ·
          refine ⟨8959287950854057240475237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972858633902704826983491 8959287950854057240475237)
          ·
            refine ⟨1679866490785135732589107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8959287950854057240475237 1679866490785135732589107)
            ·
              refine ⟨2519799736177703598883661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679866490785135732589107 2519799736177703598883661)
              ·
                refine ⟨944924901066638849581373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2519799736177703598883661 944924901066638849581373)
                ·
                  refine ⟨354346837899989568593015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944924901066638849581373 354346837899989568593015)
                  ·
                    rfl

theorem cell20_776349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_776349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776349 prefixEnd_776349 := by exact prefixLift 776349
  have htrace : WordTrace (prefixWord ++ tailWord_776349) baseStart_776349 baseEnd_776349 := by
    simpa [prefixWord, tailWord_776349, baseEnd_776349] using wordTrace_append hprefix tailTrace_776349
  have hstable : (prefixWord ++ tailWord_776349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776349).length < 2 ^ (prefixWord ++ tailWord_776349).sum := by decide
  have hdescent : baseEnd_776349 < baseStart_776349 := by decide
  rcases family_descends (prefixWord ++ tailWord_776349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776384 : List Nat := [2, 1, 1, 2, 5, 9]
def baseStart_776384 : Nat := 118140960795 + 776384 * 2 ^ 59
def prefixEnd_776384 : Nat := 4983230072969 + 3 ^ 40 * 776384 * 2
def baseEnd_776384 : Nat := 13124548624210555645415

theorem tailTrace_776384 : CollatzResearch.WordTrace tailWord_776384 prefixEnd_776384 13124548624210555645415 := by
  unfold tailWord_776384
  simp only [CollatzResearch.WordTrace]
  refine ⟨14158525409650419337908103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18878033879533892450544137 14158525409650419337908103)
  ·
    refine ⟨21237788114475629006862155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14158525409650419337908103 21237788114475629006862155)
    ·
      refine ⟨31856682171713443510293233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21237788114475629006862155 31856682171713443510293233)
      ·
        refine ⟨23892511628785082632719925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31856682171713443510293233 23892511628785082632719925)
        ·
          refine ⟨2239922965198601496817493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23892511628785082632719925 2239922965198601496817493)
          ·
            refine ⟨13124548624210555645415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2239922965198601496817493 13124548624210555645415)
            ·
              rfl

theorem cell20_776384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 9].length) (baseStart_776384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776384 prefixEnd_776384 := by exact prefixLift 776384
  have htrace : WordTrace (prefixWord ++ tailWord_776384) baseStart_776384 baseEnd_776384 := by
    simpa [prefixWord, tailWord_776384, baseEnd_776384] using wordTrace_append hprefix tailTrace_776384
  have hstable : (prefixWord ++ tailWord_776384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776384).length < 2 ^ (prefixWord ++ tailWord_776384).sum := by decide
  have hdescent : baseEnd_776384 < baseStart_776384 := by decide
  rcases family_descends (prefixWord ++ tailWord_776384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776386 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_776386 : Nat := 118140960795 + 776386 * 2 ^ 59
def prefixEnd_776386 : Nat := 4983230072969 + 3 ^ 40 * 776386 * 2
def baseEnd_776386 : Nat := 354363725708181884359531

theorem tailTrace_776386 : CollatzResearch.WordTrace tailWord_776386 prefixEnd_776386 354363725708181884359531 := by
  unfold tailWord_776386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079280941323398254347253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18878082510195728678259341 7079280941323398254347253)
  ·
    refine ⟨663682588249068586345055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7079280941323398254347253 663682588249068586345055)
    ·
      refine ⟨995523882373602879517583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663682588249068586345055 995523882373602879517583)
      ·
        refine ⟨1493285823560404319276375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995523882373602879517583 1493285823560404319276375)
        ·
          refine ⟨2239928735340606478914563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493285823560404319276375 2239928735340606478914563)
          ·
            refine ⟨3359893103010909718371845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239928735340606478914563 3359893103010909718371845)
            ·
              refine ⟨629979956814545572194721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3359893103010909718371845 629979956814545572194721)
              ·
                refine ⟨472484967610909179146041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629979956814545572194721 472484967610909179146041)
                ·
                  refine ⟨354363725708181884359531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472484967610909179146041 354363725708181884359531)
                  ·
                    rfl

theorem cell20_776386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_776386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776386 prefixEnd_776386 := by exact prefixLift 776386
  have htrace : WordTrace (prefixWord ++ tailWord_776386) baseStart_776386 baseEnd_776386 := by
    simpa [prefixWord, tailWord_776386, baseEnd_776386] using wordTrace_append hprefix tailTrace_776386
  have hstable : (prefixWord ++ tailWord_776386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776386).length < 2 ^ (prefixWord ++ tailWord_776386).sum := by decide
  have hdescent : baseEnd_776386 < baseStart_776386 := by decide
  rcases family_descends (prefixWord ++ tailWord_776386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776460 : List Nat := [2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_776460 : Nat := 118140960795 + 776460 * 2 ^ 59
def prefixEnd_776460 : Nat := 4983230072969 + 3 ^ 40 * 776460 * 2
def baseEnd_776460 : Nat := 118132500441522171964187

theorem tailTrace_776460 : CollatzResearch.WordTrace tailWord_776460 prefixEnd_776460 118132500441522171964187 := by
  unfold tailWord_776460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159911383512751827791417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18879881844683669103721889 14159911383512751827791417)
  ·
    refine ⟨10619933537634563870843563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14159911383512751827791417 10619933537634563870843563)
    ·
      refine ⟨15929900306451845806265345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619933537634563870843563 15929900306451845806265345)
      ·
        refine ⟨11947425229838884354699009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15929900306451845806265345 11947425229838884354699009)
        ·
          refine ⟨8960568922379163266024257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11947425229838884354699009 8960568922379163266024257)
          ·
            refine ⟨6720426691784372449518193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8960568922379163266024257 6720426691784372449518193)
            ·
              refine ⟨5040320018838279337138645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720426691784372449518193 5040320018838279337138645)
              ·
                refine ⟨118132500441522171964187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5040320018838279337138645 118132500441522171964187)
                ·
                  rfl

theorem cell20_776460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_776460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776460 prefixEnd_776460 := by exact prefixLift 776460
  have htrace : WordTrace (prefixWord ++ tailWord_776460) baseStart_776460 baseEnd_776460 := by
    simpa [prefixWord, tailWord_776460, baseEnd_776460] using wordTrace_append hprefix tailTrace_776460
  have hstable : (prefixWord ++ tailWord_776460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776460).length < 2 ^ (prefixWord ++ tailWord_776460).sum := by decide
  have hdescent : baseEnd_776460 < baseStart_776460 := by decide
  rcases family_descends (prefixWord ++ tailWord_776460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776484 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_776484 : Nat := 118140960795 + 776484 * 2 ^ 59
def prefixEnd_776484 : Nat := 4983230072969 + 3 ^ 40 * 776484 * 2
def baseEnd_776484 : Nat := 354408455578529099092463

theorem tailTrace_776484 : CollatzResearch.WordTrace tailWord_776484 prefixEnd_776484 354408455578529099092463 := by
  unfold tailWord_776484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14160349059469277877228253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18880465412625703836304337 14160349059469277877228253)
  ·
    refine ⟨5310130897300979203960595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14160349059469277877228253 5310130897300979203960595)
    ·
      refine ⟨7965196345951468805940893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310130897300979203960595 7965196345951468805940893)
      ·
        refine ⟨2986948629731800802227835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7965196345951468805940893 2986948629731800802227835)
        ·
          refine ⟨4480422944597701203341753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986948629731800802227835 4480422944597701203341753)
          ·
            refine ⟨3360317208448275902506315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4480422944597701203341753 3360317208448275902506315)
            ·
              refine ⟨5040475812672413853759473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360317208448275902506315 5040475812672413853759473)
              ·
                refine ⟨3780356859504310390319605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040475812672413853759473 3780356859504310390319605)
                ·
                  refine ⟨354408455578529099092463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780356859504310390319605 354408455578529099092463)
                  ·
                    rfl

theorem cell20_776484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_776484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776484 prefixEnd_776484 := by exact prefixLift 776484
  have htrace : WordTrace (prefixWord ++ tailWord_776484) baseStart_776484 baseEnd_776484 := by
    simpa [prefixWord, tailWord_776484, baseEnd_776484] using wordTrace_append hprefix tailTrace_776484
  have hstable : (prefixWord ++ tailWord_776484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776484).length < 2 ^ (prefixWord ++ tailWord_776484).sum := by decide
  have hdescent : baseEnd_776484 < baseStart_776484 := by decide
  rcases family_descends (prefixWord ++ tailWord_776484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776543 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_776543 : Nat := 118140960795 + 776543 * 2 ^ 59
def prefixEnd_776543 : Nat := 4983230072969 + 3 ^ 40 * 776543 * 2
def baseEnd_776543 : Nat := 354435384786187116125555

theorem tailTrace_776543 : CollatzResearch.WordTrace tailWord_776543 prefixEnd_776543 354435384786187116125555 := by
  unfold tailWord_776543
  simp only [CollatzResearch.WordTrace]
  refine ⟨28322850025724808830854283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18881900017149872553902855 28322850025724808830854283)
  ·
    refine ⟨42484275038587213246281425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28322850025724808830854283 42484275038587213246281425)
    ·
      refine ⟨31863206278940409934711069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42484275038587213246281425 31863206278940409934711069)
      ·
        refine ⟨11948702354602653725516651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31863206278940409934711069 11948702354602653725516651)
        ·
          refine ⟨17923053531903980588274977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11948702354602653725516651 17923053531903980588274977)
          ·
            refine ⟨13442290148927985441206233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17923053531903980588274977 13442290148927985441206233)
            ·
              refine ⟨10081717611695989080904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13442290148927985441206233 10081717611695989080904675)
              ·
                refine ⟨15122576417543983621357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10081717611695989080904675 15122576417543983621357013)
                ·
                  refine ⟨354435384786187116125555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15122576417543983621357013 354435384786187116125555)
                  ·
                    rfl

theorem cell20_776543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_776543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776543 prefixEnd_776543 := by exact prefixLift 776543
  have htrace : WordTrace (prefixWord ++ tailWord_776543) baseStart_776543 baseEnd_776543 := by
    simpa [prefixWord, tailWord_776543, baseEnd_776543] using wordTrace_append hprefix tailTrace_776543
  have hstable : (prefixWord ++ tailWord_776543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776543).length < 2 ^ (prefixWord ++ tailWord_776543).sum := by decide
  have hdescent : baseEnd_776543 < baseStart_776543 := by decide
  rcases family_descends (prefixWord ++ tailWord_776543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776560 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_776560 : Nat := 118140960795 + 776560 * 2 ^ 59
def prefixEnd_776560 : Nat := 4983230072969 + 3 ^ 40 * 776560 * 2
def baseEnd_776560 : Nat := 354443144049410612558819

theorem tailTrace_776560 : CollatzResearch.WordTrace tailWord_776560 prefixEnd_776560 354443144049410612558819 := by
  unfold tailWord_776560
  simp only [CollatzResearch.WordTrace]
  refine ⟨14161735033331610367111567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18882313377775480489482089 14161735033331610367111567)
  ·
    refine ⟨21242602549997415550667351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14161735033331610367111567 21242602549997415550667351)
    ·
      refine ⟨31863903824996123326001027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21242602549997415550667351 31863903824996123326001027)
      ·
        refine ⟨47795855737494184989001541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31863903824996123326001027 47795855737494184989001541)
        ·
          refine ⟨8961722950780159685437789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47795855737494184989001541 8961722950780159685437789)
          ·
            refine ⟨3360646106542559882039171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8961722950780159685437789 3360646106542559882039171)
            ·
              refine ⟨5040969159813839823058757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360646106542559882039171 5040969159813839823058757)
              ·
                refine ⟨945181717465094966823517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5040969159813839823058757 945181717465094966823517)
                ·
                  refine ⟨354443144049410612558819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945181717465094966823517 354443144049410612558819)
                  ·
                    rfl

theorem cell20_776560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_776560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776560 prefixEnd_776560 := by exact prefixLift 776560
  have htrace : WordTrace (prefixWord ++ tailWord_776560) baseStart_776560 baseEnd_776560 := by
    simpa [prefixWord, tailWord_776560, baseEnd_776560] using wordTrace_append hprefix tailTrace_776560
  have hstable : (prefixWord ++ tailWord_776560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776560).length < 2 ^ (prefixWord ++ tailWord_776560).sum := by decide
  have hdescent : baseEnd_776560 < baseStart_776560 := by decide
  rcases family_descends (prefixWord ++ tailWord_776560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776566 : List Nat := [5, 1, 1, 4, 2, 1, 1, 5]
def baseStart_776566 : Nat := 118140960795 + 776566 * 2 ^ 59
def prefixEnd_776566 : Nat := 4983230072969 + 3 ^ 40 * 776566 * 2
def baseEnd_776566 : Nat := 118148627537633752786265

theorem tailTrace_776566 : CollatzResearch.WordTrace tailWord_776566 prefixEnd_776566 118148627537633752786265 := by
  unfold tailWord_776566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770230556540092734933847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18882459269760989172627701 1770230556540092734933847)
  ·
    refine ⟨2655345834810139102400771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1770230556540092734933847 2655345834810139102400771)
    ·
      refine ⟨3983018752215208653601157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2655345834810139102400771 3983018752215208653601157)
      ·
        refine ⟨746816016040351622550217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3983018752215208653601157 746816016040351622550217)
        ·
          refine ⟨560112012030263716912663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746816016040351622550217 560112012030263716912663)
          ·
            refine ⟨840168018045395575368995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560112012030263716912663 840168018045395575368995)
            ·
              refine ⟨1260252027068093363053493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840168018045395575368995 1260252027068093363053493)
              ·
                refine ⟨118148627537633752786265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1260252027068093363053493 118148627537633752786265)
                ·
                  rfl

theorem cell20_776566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_776566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776566 prefixEnd_776566 := by exact prefixLift 776566
  have htrace : WordTrace (prefixWord ++ tailWord_776566) baseStart_776566 baseEnd_776566 := by
    simpa [prefixWord, tailWord_776566, baseEnd_776566] using wordTrace_append hprefix tailTrace_776566
  have hstable : (prefixWord ++ tailWord_776566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776566).length < 2 ^ (prefixWord ++ tailWord_776566).sum := by decide
  have hdescent : baseEnd_776566 < baseStart_776566 := by decide
  rcases family_descends (prefixWord ++ tailWord_776566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776577 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_776577 : Nat := 118140960795 + 776577 * 2 ^ 59
def prefixEnd_776577 : Nat := 4983230072969 + 3 ^ 40 * 776577 * 2
def baseEnd_776577 : Nat := 354450903312634108992083

theorem tailTrace_776577 : CollatzResearch.WordTrace tailWord_776577 prefixEnd_776577 354450903312634108992083 := by
  unfold tailWord_776577
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324090107601632637591985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18882726738401088425061323 28324090107601632637591985)
  ·
    refine ⟨21243067580701224478193989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28324090107601632637591985 21243067580701224478193989)
    ·
      refine ⟨3983075171381479589661373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21243067580701224478193989 3983075171381479589661373)
      ·
        refine ⟨1493653189268054846123015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3983075171381479589661373 1493653189268054846123015)
        ·
          refine ⟨2240479783902082269184523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493653189268054846123015 2240479783902082269184523)
          ·
            refine ⟨3360719675853123403776785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240479783902082269184523 3360719675853123403776785)
            ·
              refine ⟨2520539756889842552832589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360719675853123403776785 2520539756889842552832589)
              ·
                refine ⟨945202408833690957312221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2520539756889842552832589 945202408833690957312221)
                ·
                  refine ⟨354450903312634108992083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945202408833690957312221 354450903312634108992083)
                  ·
                    rfl

theorem cell20_776577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_776577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776577 prefixEnd_776577 := by exact prefixLift 776577
  have htrace : WordTrace (prefixWord ++ tailWord_776577) baseStart_776577 baseEnd_776577 := by
    simpa [prefixWord, tailWord_776577, baseEnd_776577] using wordTrace_append hprefix tailTrace_776577
  have hstable : (prefixWord ++ tailWord_776577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776577).length < 2 ^ (prefixWord ++ tailWord_776577).sum := by decide
  have hdescent : baseEnd_776577 < baseStart_776577 := by decide
  rcases family_descends (prefixWord ++ tailWord_776577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776581 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_776581 : Nat := 118140960795 + 776581 * 2 ^ 59
def prefixEnd_776581 : Nat := 4983230072969 + 3 ^ 40 * 776581 * 2
def baseEnd_776581 : Nat := 354452729021627872858733

theorem tailTrace_776581 : CollatzResearch.WordTrace tailWord_776581 prefixEnd_776581 354452729021627872858733 := by
  unfold tailWord_776581
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324235999587141320737597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18882823999724760880491731 28324235999587141320737597)
  ·
    refine ⟨10621588499845177995276599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28324235999587141320737597 10621588499845177995276599)
    ·
      refine ⟨15932382749767766992914899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10621588499845177995276599 15932382749767766992914899)
      ·
        refine ⟨23898574124651650489372349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15932382749767766992914899 23898574124651650489372349)
        ·
          refine ⟨8961965296744368933514631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23898574124651650489372349 8961965296744368933514631)
          ·
            refine ⟨13442947945116553400271947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961965296744368933514631 13442947945116553400271947)
            ·
              refine ⟨20164421917674830100407921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13442947945116553400271947 20164421917674830100407921)
              ·
                refine ⟨15123316438256122575305941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20164421917674830100407921 15123316438256122575305941)
                ·
                  refine ⟨354452729021627872858733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15123316438256122575305941 354452729021627872858733)
                  ·
                    rfl

theorem cell20_776581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_776581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776581 prefixEnd_776581 := by exact prefixLift 776581
  have htrace : WordTrace (prefixWord ++ tailWord_776581) baseStart_776581 baseEnd_776581 := by
    simpa [prefixWord, tailWord_776581, baseEnd_776581] using wordTrace_append hprefix tailTrace_776581
  have hstable : (prefixWord ++ tailWord_776581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776581).length < 2 ^ (prefixWord ++ tailWord_776581).sum := by decide
  have hdescent : baseEnd_776581 < baseStart_776581 := by decide
  rcases family_descends (prefixWord ++ tailWord_776581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776615 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_776615 : Nat := 118140960795 + 776615 * 2 ^ 59
def prefixEnd_776615 : Nat := 4983230072969 + 3 ^ 40 * 776615 * 2
def baseEnd_776615 : Nat := 354468247548074865725261

theorem tailTrace_776615 : CollatzResearch.WordTrace tailWord_776615 prefixEnd_776615 354468247548074865725261 := by
  unfold tailWord_776615
  simp only [CollatzResearch.WordTrace]
  refine ⟨28325476081463965127475299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18883650720975976751650199 28325476081463965127475299)
  ·
    refine ⟨42488214122195947691212949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28325476081463965127475299 42488214122195947691212949)
    ·
      refine ⟨1991635036977935048025607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42488214122195947691212949 1991635036977935048025607)
      ·
        refine ⟨2987452555466902572038411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991635036977935048025607 2987452555466902572038411)
        ·
          refine ⟨4481178833200353858057617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987452555466902572038411 4481178833200353858057617)
          ·
            refine ⟨3360884124900265393543213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481178833200353858057617 3360884124900265393543213)
            ·
              refine ⟨1260331546837599522578705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3360884124900265393543213 1260331546837599522578705)
              ·
                refine ⟨945248660128199641934029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260331546837599522578705 945248660128199641934029)
                ·
                  refine ⟨354468247548074865725261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945248660128199641934029 354468247548074865725261)
                  ·
                    rfl

theorem cell20_776615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_776615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776615 prefixEnd_776615 := by exact prefixLift 776615
  have htrace : WordTrace (prefixWord ++ tailWord_776615) baseStart_776615 baseEnd_776615 := by
    simpa [prefixWord, tailWord_776615, baseEnd_776615] using wordTrace_append hprefix tailTrace_776615
  have hstable : (prefixWord ++ tailWord_776615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776615).length < 2 ^ (prefixWord ++ tailWord_776615).sum := by decide
  have hdescent : baseEnd_776615 < baseStart_776615 := by decide
  rcases family_descends (prefixWord ++ tailWord_776615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776628 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_776628 : Nat := 118140960795 + 776628 * 2 ^ 59
def prefixEnd_776628 : Nat := 4983230072969 + 3 ^ 40 * 776628 * 2
def baseEnd_776628 : Nat := 354474181102304598291875

theorem tailTrace_776628 : CollatzResearch.WordTrace tailWord_776628 prefixEnd_776628 354474181102304598291875 := by
  unfold tailWord_776628
  simp only [CollatzResearch.WordTrace]
  refine ⟨14162975115208434173849269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18883966820277912231799025 14162975115208434173849269)
  ·
    refine ⟨1327778917050790703798369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14162975115208434173849269 1327778917050790703798369)
    ·
      refine ⟨995834187788093027848777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1327778917050790703798369 995834187788093027848777)
      ·
        refine ⟨746875640841069770886583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995834187788093027848777 746875640841069770886583)
        ·
          refine ⟨1120313461261604656329875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746875640841069770886583 1120313461261604656329875)
          ·
            refine ⟨1680470191892406984494813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120313461261604656329875 1680470191892406984494813)
            ·
              refine ⟨630176321959652619185555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1680470191892406984494813 630176321959652619185555)
              ·
                refine ⟨945264482939478928778333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630176321959652619185555 945264482939478928778333)
                ·
                  refine ⟨354474181102304598291875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945264482939478928778333 354474181102304598291875)
                  ·
                    rfl

theorem cell20_776628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_776628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776628 prefixEnd_776628 := by exact prefixLift 776628
  have htrace : WordTrace (prefixWord ++ tailWord_776628) baseStart_776628 baseEnd_776628 := by
    simpa [prefixWord, tailWord_776628, baseEnd_776628] using wordTrace_append hprefix tailTrace_776628
  have hstable : (prefixWord ++ tailWord_776628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776628).length < 2 ^ (prefixWord ++ tailWord_776628).sum := by decide
  have hdescent : baseEnd_776628 < baseStart_776628 := by decide
  rcases family_descends (prefixWord ++ tailWord_776628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776650 : List Nat := [3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_776650 : Nat := 118140960795 + 776650 * 2 ^ 59
def prefixEnd_776650 : Nat := 4983230072969 + 3 ^ 40 * 776650 * 2
def baseEnd_776650 : Nat := 118161407500590099852817

theorem tailTrace_776650 : CollatzResearch.WordTrace tailWord_776650 prefixEnd_776650 118161407500590099852817 := by
  unfold tailWord_776650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081688159084291526249851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18884501757558110736666269 7081688159084291526249851)
  ·
    refine ⟨10622532238626437289374777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7081688159084291526249851 10622532238626437289374777)
    ·
      refine ⟨7966899178969827967031083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10622532238626437289374777 7966899178969827967031083)
      ·
        refine ⟨11950348768454741950546625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7966899178969827967031083 11950348768454741950546625)
        ·
          refine ⟨8962761576341056462909969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11950348768454741950546625 8962761576341056462909969)
          ·
            refine ⟨6722071182255792347182477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8962761576341056462909969 6722071182255792347182477)
            ·
              refine ⟨2520776693345922130193429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6722071182255792347182477 2520776693345922130193429)
              ·
                refine ⟨118161407500590099852817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2520776693345922130193429 118161407500590099852817)
                ·
                  rfl

theorem cell20_776650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_776650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776650 prefixEnd_776650 := by exact prefixLift 776650
  have htrace : WordTrace (prefixWord ++ tailWord_776650) baseStart_776650 baseEnd_776650 := by
    simpa [prefixWord, tailWord_776650, baseEnd_776650] using wordTrace_append hprefix tailTrace_776650
  have hstable : (prefixWord ++ tailWord_776650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776650).length < 2 ^ (prefixWord ++ tailWord_776650).sum := by decide
  have hdescent : baseEnd_776650 < baseStart_776650 := by decide
  rcases family_descends (prefixWord ++ tailWord_776650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776677 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 4]
def baseStart_776677 : Nat := 118140960795 + 776677 * 2 ^ 59
def prefixEnd_776677 : Nat := 4983230072969 + 3 ^ 40 * 776677 * 2
def baseEnd_776677 : Nat := 354496546037478205658341

theorem tailTrace_776677 : CollatzResearch.WordTrace tailWord_776677 prefixEnd_776677 354496546037478205658341 := by
  unfold tailWord_776677
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327737407239349716232285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18885158271492899810821523 28327737407239349716232285)
  ·
    refine ⟨10622901527714756143587107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28327737407239349716232285 10622901527714756143587107)
    ·
      refine ⟨15934352291572134215380661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10622901527714756143587107 15934352291572134215380661)
      ·
        refine ⟨1493845527334887582691937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15934352291572134215380661 1493845527334887582691937)
        ·
          refine ⟨1120384145501165687018953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493845527334887582691937 1120384145501165687018953)
          ·
            refine ⟨840288109125874265264215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120384145501165687018953 840288109125874265264215)
            ·
              refine ⟨1260432163688811397896323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840288109125874265264215 1260432163688811397896323)
              ·
                refine ⟨1890648245533217096844485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260432163688811397896323 1890648245533217096844485)
                ·
                  refine ⟨354496546037478205658341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890648245533217096844485 354496546037478205658341)
                  ·
                    rfl

theorem cell20_776677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_776677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776677 prefixEnd_776677 := by exact prefixLift 776677
  have htrace : WordTrace (prefixWord ++ tailWord_776677) baseStart_776677 baseEnd_776677 := by
    simpa [prefixWord, tailWord_776677, baseEnd_776677] using wordTrace_append hprefix tailTrace_776677
  have hstable : (prefixWord ++ tailWord_776677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776677).length < 2 ^ (prefixWord ++ tailWord_776677).sum := by decide
  have hdescent : baseEnd_776677 < baseStart_776677 := by decide
  rcases family_descends (prefixWord ++ tailWord_776677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776688 : List Nat := [2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_776688 : Nat := 118140960795 + 776688 * 2 ^ 59
def prefixEnd_776688 : Nat := 4983230072969 + 3 ^ 40 * 776688 * 2
def baseEnd_776688 : Nat := 118167188912403685430543

theorem tailTrace_776688 : CollatzResearch.WordTrace tailWord_776688 prefixEnd_776688 118167188912403685430543 := by
  unfold tailWord_776688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164069305099749297441359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18885425740132999063255145 14164069305099749297441359)
  ·
    refine ⟨21246103957649623946162039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14164069305099749297441359 21246103957649623946162039)
    ·
      refine ⟨31869155936474435919243059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21246103957649623946162039 31869155936474435919243059)
      ·
        refine ⟨47803733904711653878864589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31869155936474435919243059 47803733904711653878864589)
        ·
          refine ⟨17926400214266870204574221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47803733904711653878864589 17926400214266870204574221)
          ·
            refine ⟨6722400080350076326715333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17926400214266870204574221 6722400080350076326715333)
            ·
              refine ⟨1260450015065639311259125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6722400080350076326715333 1260450015065639311259125)
              ·
                refine ⟨118167188912403685430543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1260450015065639311259125 118167188912403685430543)
                ·
                  rfl

theorem cell20_776688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_776688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776688 prefixEnd_776688 := by exact prefixLift 776688
  have htrace : WordTrace (prefixWord ++ tailWord_776688) baseStart_776688 baseEnd_776688 := by
    simpa [prefixWord, tailWord_776688, baseEnd_776688] using wordTrace_append hprefix tailTrace_776688
  have hstable : (prefixWord ++ tailWord_776688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776688).length < 2 ^ (prefixWord ++ tailWord_776688).sum := by decide
  have hdescent : baseEnd_776688 < baseStart_776688 := by decide
  rcases family_descends (prefixWord ++ tailWord_776688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776732 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 2]
def baseStart_776732 : Nat := 118140960795 + 776732 * 2 ^ 59
def prefixEnd_776732 : Nat := 4983230072969 + 3 ^ 40 * 776732 * 2
def baseEnd_776732 : Nat := 354521649536142458824783

theorem tailTrace_776732 : CollatzResearch.WordTrace tailWord_776732 prefixEnd_776732 354521649536142458824783 := by
  unfold tailWord_776732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164871711020047054742225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18886495614693396072989633 14164871711020047054742225)
  ·
    refine ⟨10623653783265035291056669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14164871711020047054742225 10623653783265035291056669)
    ·
      refine ⟨3983870168724388234146251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10623653783265035291056669 3983870168724388234146251)
      ·
        refine ⟨5975805253086582351219377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983870168724388234146251 5975805253086582351219377)
        ·
          refine ⟨4481853939814936763414533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5975805253086582351219377 4481853939814936763414533)
          ·
            refine ⟨840347613715300643140225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4481853939814936763414533 840347613715300643140225)
            ·
              refine ⟨630260710286475482355169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840347613715300643140225 630260710286475482355169)
              ·
                refine ⟨472695532714856611766377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630260710286475482355169 472695532714856611766377)
                ·
                  refine ⟨354521649536142458824783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472695532714856611766377 354521649536142458824783)
                  ·
                    rfl

theorem cell20_776732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_776732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776732 prefixEnd_776732 := by exact prefixLift 776732
  have htrace : WordTrace (prefixWord ++ tailWord_776732) baseStart_776732 baseEnd_776732 := by
    simpa [prefixWord, tailWord_776732, baseEnd_776732] using wordTrace_append hprefix tailTrace_776732
  have hstable : (prefixWord ++ tailWord_776732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776732).length < 2 ^ (prefixWord ++ tailWord_776732).sum := by decide
  have hdescent : baseEnd_776732 < baseStart_776732 := by decide
  rcases family_descends (prefixWord ++ tailWord_776732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776757 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_776757 : Nat := 118140960795 + 776757 * 2 ^ 59
def prefixEnd_776757 : Nat := 4983230072969 + 3 ^ 40 * 776757 * 2
def baseEnd_776757 : Nat := 354533060217353482991347

theorem tailTrace_776757 : CollatzResearch.WordTrace tailWord_776757 prefixEnd_776757 354533060217353482991347 := by
  unfold tailWord_776757
  simp only [CollatzResearch.WordTrace]
  refine ⟨28330655246949523379144525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18887103497966348919429683 28330655246949523379144525)
  ·
    refine ⟨10623995717606071267179197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28330655246949523379144525 10623995717606071267179197)
    ·
      refine ⟨3983998394102276725192199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10623995717606071267179197 3983998394102276725192199)
      ·
        refine ⟨5975997591153415087788299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983998394102276725192199 5975997591153415087788299)
        ·
          refine ⟨8963996386730122631682449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975997591153415087788299 8963996386730122631682449)
          ·
            refine ⟨6722997290047591973761837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8963996386730122631682449 6722997290047591973761837)
            ·
              refine ⟨2521123983767846990160689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6722997290047591973761837 2521123983767846990160689)
              ·
                refine ⟨1890842987825885242620517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521123983767846990160689 1890842987825885242620517)
                ·
                  refine ⟨354533060217353482991347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1890842987825885242620517 354533060217353482991347)
                  ·
                    rfl

theorem cell20_776757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_776757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776757 prefixEnd_776757 := by exact prefixLift 776757
  have htrace : WordTrace (prefixWord ++ tailWord_776757) baseStart_776757 baseEnd_776757 := by
    simpa [prefixWord, tailWord_776757, baseEnd_776757] using wordTrace_append hprefix tailTrace_776757
  have hstable : (prefixWord ++ tailWord_776757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776757).length < 2 ^ (prefixWord ++ tailWord_776757).sum := by decide
  have hdescent : baseEnd_776757 < baseStart_776757 := by decide
  rcases family_descends (prefixWord ++ tailWord_776757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776781 : List Nat := [1, 6, 1, 1, 2, 2, 7]
def baseStart_776781 : Nat := 118140960795 + 776781 * 2 ^ 59
def prefixEnd_776781 : Nat := 4983230072969 + 3 ^ 40 * 776781 * 2
def baseEnd_776781 : Nat := 39393779385701785132361

theorem tailTrace_776781 : CollatzResearch.WordTrace tailWord_776781 prefixEnd_776781 39393779385701785132361 := by
  unfold tailWord_776781
  simp only [CollatzResearch.WordTrace]
  refine ⟨28331530598862575478018197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18887687065908383652012131 28331530598862575478018197)
  ·
    refine ⟨1328040496821683225532103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28331530598862575478018197 1328040496821683225532103)
    ·
      refine ⟨1992060745232524838298155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328040496821683225532103 1992060745232524838298155)
      ·
        refine ⟨2988091117848787257447233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992060745232524838298155 2988091117848787257447233)
        ·
          refine ⟨2241068338386590443085425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988091117848787257447233 2241068338386590443085425)
          ·
            refine ⟨1680801253789942832314069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241068338386590443085425 1680801253789942832314069)
            ·
              refine ⟨39393779385701785132361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1680801253789942832314069 39393779385701785132361)
              ·
                rfl

theorem cell20_776781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_776781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776781 prefixEnd_776781 := by exact prefixLift 776781
  have htrace : WordTrace (prefixWord ++ tailWord_776781) baseStart_776781 baseEnd_776781 := by
    simpa [prefixWord, tailWord_776781, baseEnd_776781] using wordTrace_append hprefix tailTrace_776781
  have hstable : (prefixWord ++ tailWord_776781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776781).length < 2 ^ (prefixWord ++ tailWord_776781).sum := by decide
  have hdescent : baseEnd_776781 < baseStart_776781 := by decide
  rcases family_descends (prefixWord ++ tailWord_776781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776788 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_776788 : Nat := 118140960795 + 776788 * 2 ^ 59
def prefixEnd_776788 : Nat := 4983230072969 + 3 ^ 40 * 776788 * 2
def baseEnd_776788 : Nat := 354547209462055152957887

theorem tailTrace_776788 : CollatzResearch.WordTrace tailWord_776788 prefixEnd_776788 354547209462055152957887 := by
  unfold tailWord_776788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14165892954918607836761509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18887857273224810449015345 14165892954918607836761509)
  ·
    refine ⟨2656104929047238969392783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14165892954918607836761509 2656104929047238969392783)
    ·
      refine ⟨3984157393570858454089175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656104929047238969392783 3984157393570858454089175)
      ·
        refine ⟨5976236090356287681133763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984157393570858454089175 5976236090356287681133763)
        ·
          refine ⟨8964354135534431521700645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5976236090356287681133763 8964354135534431521700645)
          ·
            refine ⟨1680816400412705910318871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8964354135534431521700645 1680816400412705910318871)
            ·
              refine ⟨2521224600619058865478307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680816400412705910318871 2521224600619058865478307)
              ·
                refine ⟨3781836900928588298217461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521224600619058865478307 3781836900928588298217461)
                ·
                  refine ⟨354547209462055152957887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781836900928588298217461 354547209462055152957887)
                  ·
                    rfl

theorem cell20_776788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_776788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776788 prefixEnd_776788 := by exact prefixLift 776788
  have htrace : WordTrace (prefixWord ++ tailWord_776788) baseStart_776788 baseEnd_776788 := by
    simpa [prefixWord, tailWord_776788, baseEnd_776788] using wordTrace_append hprefix tailTrace_776788
  have hstable : (prefixWord ++ tailWord_776788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776788).length < 2 ^ (prefixWord ++ tailWord_776788).sum := by decide
  have hdescent : baseEnd_776788 < baseStart_776788 := by decide
  rcases family_descends (prefixWord ++ tailWord_776788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776850 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_776850 : Nat := 118140960795 + 776850 * 2 ^ 59
def prefixEnd_776850 : Nat := 4983230072969 + 3 ^ 40 * 776850 * 2
def baseEnd_776850 : Nat := 354575507951458492890967

theorem tailTrace_776850 : CollatzResearch.WordTrace tailWord_776850 prefixEnd_776850 354575507951458492890967 := by
  unfold tailWord_776850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083511808903150065570001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18889364823741733508186669 7083511808903150065570001)
  ·
    refine ⟨5312633856677362549177501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7083511808903150065570001 5312633856677362549177501)
    ·
      refine ⟨1992237696254010955941563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5312633856677362549177501 1992237696254010955941563)
      ·
        refine ⟨2988356544381016433912345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992237696254010955941563 2988356544381016433912345)
        ·
          refine ⟨2241267408285762325434259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988356544381016433912345 2241267408285762325434259)
          ·
            refine ⟨3361901112428643488151389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241267408285762325434259 3361901112428643488151389)
            ·
              refine ⟨1260712917160741308056771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3361901112428643488151389 1260712917160741308056771)
              ·
                refine ⟨1891069375741111962085157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260712917160741308056771 1891069375741111962085157)
                ·
                  refine ⟨354575507951458492890967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891069375741111962085157 354575507951458492890967)
                  ·
                    rfl

theorem cell20_776850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_776850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776850 prefixEnd_776850 := by exact prefixLift 776850
  have htrace : WordTrace (prefixWord ++ tailWord_776850) baseStart_776850 baseEnd_776850 := by
    simpa [prefixWord, tailWord_776850, baseEnd_776850] using wordTrace_append hprefix tailTrace_776850
  have hstable : (prefixWord ++ tailWord_776850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776850).length < 2 ^ (prefixWord ++ tailWord_776850).sum := by decide
  have hdescent : baseEnd_776850 < baseStart_776850 := by decide
  rcases family_descends (prefixWord ++ tailWord_776850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776860 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_776860 : Nat := 118140960795 + 776860 * 2 ^ 59
def prefixEnd_776860 : Nat := 4983230072969 + 3 ^ 40 * 776860 * 2
def baseEnd_776860 : Nat := 354580072223942902557593

theorem tailTrace_776860 : CollatzResearch.WordTrace tailWord_776860 prefixEnd_776860 354580072223942902557593 := by
  unfold tailWord_776860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14167205982788185985072017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18889607977050914646762689 14167205982788185985072017)
  ·
    refine ⟨10625404487091139488804013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14167205982788185985072017 10625404487091139488804013)
    ·
      refine ⟨3984526682659177308301505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10625404487091139488804013 3984526682659177308301505)
      ·
        refine ⟨2988395011994382981226129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3984526682659177308301505 2988395011994382981226129)
        ·
          refine ⟨2241296258995787235919597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988395011994382981226129 2241296258995787235919597)
          ·
            refine ⟨840486097123420213469849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2241296258995787235919597 840486097123420213469849)
            ·
              refine ⟨630364572842565160102387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840486097123420213469849 630364572842565160102387)
              ·
                refine ⟨945546859263847740153581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630364572842565160102387 945546859263847740153581)
                ·
                  refine ⟨354580072223942902557593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945546859263847740153581 354580072223942902557593)
                  ·
                    rfl

theorem cell20_776860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_776860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776860 prefixEnd_776860 := by exact prefixLift 776860
  have htrace : WordTrace (prefixWord ++ tailWord_776860) baseStart_776860 baseEnd_776860 := by
    simpa [prefixWord, tailWord_776860, baseEnd_776860] using wordTrace_append hprefix tailTrace_776860
  have hstable : (prefixWord ++ tailWord_776860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776860).length < 2 ^ (prefixWord ++ tailWord_776860).sum := by decide
  have hdescent : baseEnd_776860 < baseStart_776860 := by decide
  rcases family_descends (prefixWord ++ tailWord_776860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776933 : List Nat := [1, 3, 1, 4, 1, 3, 3, 4]
def baseStart_776933 : Nat := 118140960795 + 776933 * 2 ^ 59
def prefixEnd_776933 : Nat := 4983230072969 + 3 ^ 40 * 776933 * 2
def baseEnd_776933 : Nat := 118204463804359697707987

theorem tailTrace_776933 : CollatzResearch.WordTrace tailWord_776933 prefixEnd_776933 118204463804359697707987 := by
  unfold tailWord_776933
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337074494311905437551453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18891382996207936958367635 28337074494311905437551453)
  ·
    refine ⟨10626402935366964539081795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28337074494311905437551453 10626402935366964539081795)
    ·
      refine ⟨15939604403050446808622693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10626402935366964539081795 15939604403050446808622693)
      ·
        refine ⟨2988675825571958776616755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15939604403050446808622693 2988675825571958776616755)
        ·
          refine ⟨4483013738357938164925133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988675825571958776616755 4483013738357938164925133)
          ·
            refine ⟨1681130151884226811846925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4483013738357938164925133 1681130151884226811846925)
            ·
              refine ⟨630423806956585054442597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1681130151884226811846925 630423806956585054442597)
              ·
                refine ⟨118204463804359697707987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630423806956585054442597 118204463804359697707987)
                ·
                  rfl

theorem cell20_776933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_776933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776933 prefixEnd_776933 := by exact prefixLift 776933
  have htrace : WordTrace (prefixWord ++ tailWord_776933) baseStart_776933 baseEnd_776933 := by
    simpa [prefixWord, tailWord_776933, baseEnd_776933] using wordTrace_append hprefix tailTrace_776933
  have hstable : (prefixWord ++ tailWord_776933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776933).length < 2 ^ (prefixWord ++ tailWord_776933).sum := by decide
  have hdescent : baseEnd_776933 < baseStart_776933 := by decide
  rcases family_descends (prefixWord ++ tailWord_776933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776937 : List Nat := [1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_776937 : Nat := 118140960795 + 776937 * 2 ^ 59
def prefixEnd_776937 : Nat := 4983230072969 + 3 ^ 40 * 776937 * 2
def baseEnd_776937 : Nat := 118205072374024285663537

theorem tailTrace_776937 : CollatzResearch.WordTrace tailWord_776937 prefixEnd_776937 118205072374024285663537 := by
  unfold tailWord_776937
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337220386297414120697065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18891480257531609413798043 28337220386297414120697065)
  ·
    refine ⟨21252915289723060590522799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28337220386297414120697065 21252915289723060590522799)
    ·
      refine ⟨31879372934584590885784199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21252915289723060590522799 31879372934584590885784199)
      ·
        refine ⟨47819059401876886328676299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31879372934584590885784199 47819059401876886328676299)
        ·
          refine ⟨71728589102815329493014449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47819059401876886328676299 71728589102815329493014449)
          ·
            refine ⟨53796441827111497119760837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71728589102815329493014449 53796441827111497119760837)
            ·
              refine ⟨10086832842583405709955157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53796441827111497119760837 10086832842583405709955157)
              ·
                refine ⟨118205072374024285663537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10086832842583405709955157 118205072374024285663537)
                ·
                  rfl

theorem cell20_776937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_776937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776937 prefixEnd_776937 := by exact prefixLift 776937
  have htrace : WordTrace (prefixWord ++ tailWord_776937) baseStart_776937 baseEnd_776937 := by
    simpa [prefixWord, tailWord_776937, baseEnd_776937] using wordTrace_append hprefix tailTrace_776937
  have hstable : (prefixWord ++ tailWord_776937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776937).length < 2 ^ (prefixWord ++ tailWord_776937).sum := by decide
  have hdescent : baseEnd_776937 < baseStart_776937 := by decide
  rcases family_descends (prefixWord ++ tailWord_776937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776964 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 2]
def baseStart_776964 : Nat := 118140960795 + 776964 * 2 ^ 59
def prefixEnd_776964 : Nat := 4983230072969 + 3 ^ 40 * 776964 * 2
def baseEnd_776964 : Nat := 354627540657780763090501

theorem tailTrace_776964 : CollatzResearch.WordTrace tailWord_776964 prefixEnd_776964 354627540657780763090501 := by
  unfold tailWord_776964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169102578599798865964973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18892136771466398487953297 14169102578599798865964973)
  ·
    refine ⟨5313413466974924574736865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14169102578599798865964973 5313413466974924574736865)
    ·
      refine ⟨3985060100231193431052649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5313413466974924574736865 3985060100231193431052649)
      ·
        refine ⟨2988795075173395073289487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3985060100231193431052649 2988795075173395073289487)
        ·
          refine ⟨4483192612760092609934231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988795075173395073289487 4483192612760092609934231)
          ·
            refine ⟨6724788919140138914901347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483192612760092609934231 6724788919140138914901347)
            ·
              refine ⟨10087183378710208372352021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724788919140138914901347 10087183378710208372352021)
              ·
                refine ⟨472836720877041017454001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10087183378710208372352021 472836720877041017454001)
                ·
                  refine ⟨354627540657780763090501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472836720877041017454001 354627540657780763090501)
                  ·
                    rfl

theorem cell20_776964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_776964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776964 prefixEnd_776964 := by exact prefixLift 776964
  have htrace : WordTrace (prefixWord ++ tailWord_776964) baseStart_776964 baseEnd_776964 := by
    simpa [prefixWord, tailWord_776964, baseEnd_776964] using wordTrace_append hprefix tailTrace_776964
  have hstable : (prefixWord ++ tailWord_776964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776964).length < 2 ^ (prefixWord ++ tailWord_776964).sum := by decide
  have hdescent : baseEnd_776964 < baseStart_776964 := by decide
  rcases family_descends (prefixWord ++ tailWord_776964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776975 : List Nat := [1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_776975 : Nat := 118140960795 + 776975 * 2 ^ 59
def prefixEnd_776975 : Nat := 4983230072969 + 3 ^ 40 * 776975 * 2
def baseEnd_776975 : Nat := 118210853785837871241263

theorem tailTrace_776975 : CollatzResearch.WordTrace tailWord_776975 prefixEnd_776975 118210853785837871241263 := by
  unfold tailWord_776975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28338606360159746610580379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18892404240106497740386919 28338606360159746610580379)
  ·
    refine ⟨42507909540239619915870569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28338606360159746610580379 42507909540239619915870569)
    ·
      refine ⟨31880932155179714936902927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42507909540239619915870569 31880932155179714936902927)
      ·
        refine ⟨47821398232769572405354391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31880932155179714936902927 47821398232769572405354391)
        ·
          refine ⟨71732097349154358608031587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47821398232769572405354391 71732097349154358608031587)
          ·
            refine ⟨107598146023731537912047381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71732097349154358608031587 107598146023731537912047381)
            ·
              refine ⟨5043663094862415839627221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107598146023731537912047381 5043663094862415839627221)
              ·
                refine ⟨118210853785837871241263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5043663094862415839627221 118210853785837871241263)
                ·
                  rfl

theorem cell20_776975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_776975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776975 prefixEnd_776975 := by exact prefixLift 776975
  have htrace : WordTrace (prefixWord ++ tailWord_776975) baseStart_776975 baseEnd_776975 := by
    simpa [prefixWord, tailWord_776975, baseEnd_776975] using wordTrace_append hprefix tailTrace_776975
  have hstable : (prefixWord ++ tailWord_776975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776975).length < 2 ^ (prefixWord ++ tailWord_776975).sum := by decide
  have hdescent : baseEnd_776975 < baseStart_776975 := by decide
  rcases family_descends (prefixWord ++ tailWord_776975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776992 : List Nat := [2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_776992 : Nat := 118140960795 + 776992 * 2 ^ 59
def prefixEnd_776992 : Nat := 4983230072969 + 3 ^ 40 * 776992 * 2
def baseEnd_776992 : Nat := 118213440206912370052351

theorem tailTrace_776992 : CollatzResearch.WordTrace tailWord_776992 prefixEnd_776992 118213440206912370052351 := by
  unfold tailWord_776992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169613200549079256974615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18892817600732105675966153 14169613200549079256974615)
  ·
    refine ⟨21254419800823618885461923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14169613200549079256974615 21254419800823618885461923)
    ·
      refine ⟨31881629701235428328192885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21254419800823618885461923 31881629701235428328192885)
      ·
        refine ⟨2988902784490821405768083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31881629701235428328192885 2988902784490821405768083)
        ·
          refine ⟨4483354176736232108652125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988902784490821405768083 4483354176736232108652125)
          ·
            refine ⟨1681257816276087040744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4483354176736232108652125 1681257816276087040744547)
            ·
              refine ⟨2521886724414130561116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681257816276087040744547 2521886724414130561116821)
              ·
                refine ⟨118213440206912370052351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2521886724414130561116821 118213440206912370052351)
                ·
                  rfl

theorem cell20_776992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_776992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_776992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_776992 prefixEnd_776992 := by exact prefixLift 776992
  have htrace : WordTrace (prefixWord ++ tailWord_776992) baseStart_776992 baseEnd_776992 := by
    simpa [prefixWord, tailWord_776992, baseEnd_776992] using wordTrace_append hprefix tailTrace_776992
  have hstable : (prefixWord ++ tailWord_776992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776992).length < 2 ^ (prefixWord ++ tailWord_776992).sum := by decide
  have hdescent : baseEnd_776992 < baseStart_776992 := by decide
  rcases family_descends (prefixWord ++ tailWord_776992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777005 : List Nat := [1, 5, 3, 2, 2, 1, 6]
def baseStart_777005 : Nat := 118140960795 + 777005 * 2 ^ 59
def prefixEnd_777005 : Nat := 4983230072969 + 3 ^ 40 * 777005 * 2
def baseEnd_777005 : Nat := 39405139352774093635963

theorem tailTrace_777005 : CollatzResearch.WordTrace tailWord_777005 prefixEnd_777005 39405139352774093635963 := by
  unfold tailWord_777005
  simp only [CollatzResearch.WordTrace]
  refine ⟨28339700550051061734172469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18893133700034041156114979 28339700550051061734172469)
  ·
    refine ⟨2656846926567287037578669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28339700550051061734172469 2656846926567287037578669)
    ·
      refine ⟨996317597462732639092001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2656846926567287037578669 996317597462732639092001)
      ·
        refine ⟨747238198097049479319001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 996317597462732639092001 747238198097049479319001)
        ·
          refine ⟨560428648572787109489251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747238198097049479319001 560428648572787109489251)
          ·
            refine ⟨840642972859180664233877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560428648572787109489251 840642972859180664233877)
            ·
              refine ⟨39405139352774093635963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 840642972859180664233877 39405139352774093635963)
              ·
                rfl

theorem cell20_777005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 6].length) (baseStart_777005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777005 prefixEnd_777005 := by exact prefixLift 777005
  have htrace : WordTrace (prefixWord ++ tailWord_777005) baseStart_777005 baseEnd_777005 := by
    simpa [prefixWord, tailWord_777005, baseEnd_777005] using wordTrace_append hprefix tailTrace_777005
  have hstable : (prefixWord ++ tailWord_777005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777005).length < 2 ^ (prefixWord ++ tailWord_777005).sum := by decide
  have hdescent : baseEnd_777005 < baseStart_777005 := by decide
  rcases family_descends (prefixWord ++ tailWord_777005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777023 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_777023 : Nat := 118140960795 + 777023 * 2 ^ 59
def prefixEnd_777023 : Nat := 4983230072969 + 3 ^ 40 * 777023 * 2
def baseEnd_777023 : Nat := 354654469865438780123593

theorem tailTrace_777023 : CollatzResearch.WordTrace tailWord_777023 prefixEnd_777023 354654469865438780123593 := by
  unfold tailWord_777023
  simp only [CollatzResearch.WordTrace]
  refine ⟨28340357063985850808327723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18893571375990567205551815 28340357063985850808327723)
  ·
    refine ⟨42510535595978776212491585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28340357063985850808327723 42510535595978776212491585)
    ·
      refine ⟨31882901696984082159368689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42510535595978776212491585 31882901696984082159368689)
      ·
        refine ⟨23912176272738061619526517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31882901696984082159368689 23912176272738061619526517)
        ·
          refine ⟨2241766525569193276830611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23912176272738061619526517 2241766525569193276830611)
          ·
            refine ⟨3362649788353789915245917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241766525569193276830611 3362649788353789915245917)
            ·
              refine ⟨1260993670632671218217219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3362649788353789915245917 1260993670632671218217219)
              ·
                refine ⟨1891490505949006827325829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260993670632671218217219 1891490505949006827325829)
                ·
                  refine ⟨354654469865438780123593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891490505949006827325829 354654469865438780123593)
                  ·
                    rfl

theorem cell20_777023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_777023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777023 prefixEnd_777023 := by exact prefixLift 777023
  have htrace : WordTrace (prefixWord ++ tailWord_777023) baseStart_777023 baseEnd_777023 := by
    simpa [prefixWord, tailWord_777023, baseEnd_777023] using wordTrace_append hprefix tailTrace_777023
  have hstable : (prefixWord ++ tailWord_777023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777023).length < 2 ^ (prefixWord ++ tailWord_777023).sum := by decide
  have hdescent : baseEnd_777023 < baseStart_777023 := by decide
  rcases family_descends (prefixWord ++ tailWord_777023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777033 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 3]
def baseStart_777033 : Nat := 118140960795 + 777033 * 2 ^ 59
def prefixEnd_777033 : Nat := 4983230072969 + 3 ^ 40 * 777033 * 2
def baseEnd_777033 : Nat := 354659034137923189790219

theorem tailTrace_777033 : CollatzResearch.WordTrace tailWord_777033 prefixEnd_777033 354659034137923189790219 := by
  unfold tailWord_777033
  simp only [CollatzResearch.WordTrace]
  refine ⟨28340721793949622516191753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18893814529299748344127835 28340721793949622516191753)
  ·
    refine ⟨21255541345462216887143815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28340721793949622516191753 21255541345462216887143815)
    ·
      refine ⟨31883312018193325330715723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21255541345462216887143815 31883312018193325330715723)
      ·
        refine ⟨47824968027289987996073585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31883312018193325330715723 47824968027289987996073585)
        ·
          refine ⟨35868726020467490997055189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47824968027289987996073585 35868726020467490997055189)
          ·
            refine ⟨840673266104706820243481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35868726020467490997055189 840673266104706820243481)
            ·
              refine ⟨630504949578530115182611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840673266104706820243481 630504949578530115182611)
              ·
                refine ⟨945757424367795172773917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630504949578530115182611 945757424367795172773917)
                ·
                  refine ⟨354659034137923189790219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945757424367795172773917 354659034137923189790219)
                  ·
                    rfl

theorem cell20_777033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_777033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777033 prefixEnd_777033 := by exact prefixLift 777033
  have htrace : WordTrace (prefixWord ++ tailWord_777033) baseStart_777033 baseEnd_777033 := by
    simpa [prefixWord, tailWord_777033, baseEnd_777033] using wordTrace_append hprefix tailTrace_777033
  have hstable : (prefixWord ++ tailWord_777033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777033).length < 2 ^ (prefixWord ++ tailWord_777033).sum := by decide
  have hdescent : baseEnd_777033 < baseStart_777033 := by decide
  rcases family_descends (prefixWord ++ tailWord_777033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777075 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_777075 : Nat := 118140960795 + 777075 * 2 ^ 59
def prefixEnd_777075 : Nat := 4983230072969 + 3 ^ 40 * 777075 * 2
def baseEnd_777075 : Nat := 354678204082357710390047

theorem tailTrace_777075 : CollatzResearch.WordTrace tailWord_777075 prefixEnd_777075 354678204082357710390047 := by
  unfold tailWord_777075
  simp only [CollatzResearch.WordTrace]
  refine ⟨28342253659797463689220679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18894835773198309126147119 28342253659797463689220679)
  ·
    refine ⟨42513380489696195533831019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28342253659797463689220679 42513380489696195533831019)
    ·
      refine ⟨63770070734544293300746529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42513380489696195533831019 63770070734544293300746529)
      ·
        refine ⟨47827553050908219975559897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63770070734544293300746529 47827553050908219975559897)
        ·
          refine ⟨35870664788181164981669923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47827553050908219975559897 35870664788181164981669923)
          ·
            refine ⟨53805997182271747472504885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35870664788181164981669923 53805997182271747472504885)
            ·
              refine ⟨5044312235837976325547333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53805997182271747472504885 5044312235837976325547333)
              ·
                refine ⟨945808544219620561040125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5044312235837976325547333 945808544219620561040125)
                ·
                  refine ⟨354678204082357710390047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945808544219620561040125 354678204082357710390047)
                  ·
                    rfl

theorem cell20_777075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_777075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777075 prefixEnd_777075 := by exact prefixLift 777075
  have htrace : WordTrace (prefixWord ++ tailWord_777075) baseStart_777075 baseEnd_777075 := by
    simpa [prefixWord, tailWord_777075, baseEnd_777075] using wordTrace_append hprefix tailTrace_777075
  have hstable : (prefixWord ++ tailWord_777075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777075).length < 2 ^ (prefixWord ++ tailWord_777075).sum := by decide
  have hdescent : baseEnd_777075 < baseStart_777075 := by decide
  rcases family_descends (prefixWord ++ tailWord_777075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777082 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_777082 : Nat := 118140960795 + 777082 * 2 ^ 59
def prefixEnd_777082 : Nat := 4983230072969 + 3 ^ 40 * 777082 * 2
def baseEnd_777082 : Nat := 354681399073096797156685

theorem tailTrace_777082 : CollatzResearch.WordTrace tailWord_777082 prefixEnd_777082 354681399073096797156685 := by
  unfold tailWord_777082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7085627242693025971181375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18895005980514735923150333 7085627242693025971181375)
  ·
    refine ⟨10628440864039538956772063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7085627242693025971181375 10628440864039538956772063)
    ·
      refine ⟨15942661296059308435158095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10628440864039538956772063 15942661296059308435158095)
      ·
        refine ⟨23913991944088962652737143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15942661296059308435158095 23913991944088962652737143)
        ·
          refine ⟨35870987916133443979105715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23913991944088962652737143 35870987916133443979105715)
          ·
            refine ⟨53806481874200165968658573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35870987916133443979105715 53806481874200165968658573)
            ·
              refine ⟨20177430702825062238246965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53806481874200165968658573 20177430702825062238246965)
              ·
                refine ⟨1891634128389849584835653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20177430702825062238246965 1891634128389849584835653)
                ·
                  refine ⟨354681399073096797156685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891634128389849584835653 354681399073096797156685)
                  ·
                    rfl

theorem cell20_777082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_777082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777082 prefixEnd_777082 := by exact prefixLift 777082
  have htrace : WordTrace (prefixWord ++ tailWord_777082) baseStart_777082 baseEnd_777082 := by
    simpa [prefixWord, tailWord_777082, baseEnd_777082] using wordTrace_append hprefix tailTrace_777082
  have hstable : (prefixWord ++ tailWord_777082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777082).length < 2 ^ (prefixWord ++ tailWord_777082).sum := by decide
  have hdescent : baseEnd_777082 < baseStart_777082 := by decide
  rcases family_descends (prefixWord ++ tailWord_777082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777133 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 4]
def baseStart_777133 : Nat := 118140960795 + 777133 * 2 ^ 59
def prefixEnd_777133 : Nat := 4983230072969 + 3 ^ 40 * 777133 * 2
def baseEnd_777133 : Nat := 354704676862767286456477

theorem tailTrace_777133 : CollatzResearch.WordTrace tailWord_777133 prefixEnd_777133 354704676862767286456477 := by
  unfold tailWord_777133
  simp only [CollatzResearch.WordTrace]
  refine ⟨28344369093587339594832053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18896246062391559729888035 28344369093587339594832053)
  ·
    refine ⟨2657284602523813087015505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28344369093587339594832053 2657284602523813087015505)
    ·
      refine ⟨1992963451892859815261629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657284602523813087015505 1992963451892859815261629)
      ·
        refine ⟨747361294459822430723111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1992963451892859815261629 747361294459822430723111)
        ·
          refine ⟨1121041941689733646084667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747361294459822430723111 1121041941689733646084667)
          ·
            refine ⟨1681562912534600469127001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121041941689733646084667 1681562912534600469127001)
            ·
              refine ⟨1261172184400950351845251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681562912534600469127001 1261172184400950351845251)
              ·
                refine ⟨1891758276601425527767877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261172184400950351845251 1891758276601425527767877)
                ·
                  refine ⟨354704676862767286456477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1891758276601425527767877 354704676862767286456477)
                  ·
                    rfl

theorem cell20_777133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_777133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777133 prefixEnd_777133 := by exact prefixLift 777133
  have htrace : WordTrace (prefixWord ++ tailWord_777133) baseStart_777133 baseEnd_777133 := by
    simpa [prefixWord, tailWord_777133, baseEnd_777133] using wordTrace_append hprefix tailTrace_777133
  have hstable : (prefixWord ++ tailWord_777133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777133).length < 2 ^ (prefixWord ++ tailWord_777133).sum := by decide
  have hdescent : baseEnd_777133 < baseStart_777133 := by decide
  rcases family_descends (prefixWord ++ tailWord_777133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777175 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 2]
def baseStart_777175 : Nat := 118140960795 + 777175 * 2 ^ 59
def prefixEnd_777175 : Nat := 4983230072969 + 3 ^ 40 * 777175 * 2
def baseEnd_777175 : Nat := 354723846807201807056305

theorem tailTrace_777175 : CollatzResearch.WordTrace tailWord_777175 prefixEnd_777175 354723846807201807056305 := by
  unfold tailWord_777175
  simp only [CollatzResearch.WordTrace]
  refine ⟨28345900959435180767860979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18897267306290120511907319 28345900959435180767860979)
  ·
    refine ⟨42518851439152771151791469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28345900959435180767860979 42518851439152771151791469)
    ·
      refine ⟨15944569289682289181921801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42518851439152771151791469 15944569289682289181921801)
      ·
        refine ⟨11958426967261716886441351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15944569289682289181921801 11958426967261716886441351)
        ·
          refine ⟨17937640450892575329662027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11958426967261716886441351 17937640450892575329662027)
          ·
            refine ⟨26906460676338862994493041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17937640450892575329662027 26906460676338862994493041)
            ·
              refine ⟨20179845507254147245869781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26906460676338862994493041 20179845507254147245869781)
              ·
                refine ⟨472965129076269076075073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20179845507254147245869781 472965129076269076075073)
                ·
                  refine ⟨354723846807201807056305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472965129076269076075073 354723846807201807056305)
                  ·
                    rfl

theorem cell20_777175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 2].length) (baseStart_777175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777175 prefixEnd_777175 := by exact prefixLift 777175
  have htrace : WordTrace (prefixWord ++ tailWord_777175) baseStart_777175 baseEnd_777175 := by
    simpa [prefixWord, tailWord_777175, baseEnd_777175] using wordTrace_append hprefix tailTrace_777175
  have hstable : (prefixWord ++ tailWord_777175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777175).length < 2 ^ (prefixWord ++ tailWord_777175).sum := by decide
  have hdescent : baseEnd_777175 < baseStart_777175 := by decide
  rcases family_descends (prefixWord ++ tailWord_777175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777247 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 2]
def baseStart_777247 : Nat := 118140960795 + 777247 * 2 ^ 59
def prefixEnd_777247 : Nat := 4983230072969 + 3 ^ 40 * 777247 * 2
def baseEnd_777247 : Nat := 354756709569089556656011

theorem tailTrace_777247 : CollatzResearch.WordTrace tailWord_777247 prefixEnd_777247 354756709569089556656011 := by
  unfold tailWord_777247
  simp only [CollatzResearch.WordTrace]
  refine ⟨28348527015174337064481995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18899018010116224709654663 28348527015174337064481995)
  ·
    refine ⟨42522790522761505596722993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28348527015174337064481995 42522790522761505596722993)
    ·
      refine ⟨31892092892071129197542245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42522790522761505596722993 31892092892071129197542245)
      ·
        refine ⟨5979767417263336724539171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31892092892071129197542245 5979767417263336724539171)
        ·
          refine ⟨8969651125895005086808757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979767417263336724539171 8969651125895005086808757)
          ·
            refine ⟨840904793052656726888321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8969651125895005086808757 840904793052656726888321)
            ·
              refine ⟨630678594789492545166241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840904793052656726888321 630678594789492545166241)
              ·
                refine ⟨473008946092119408874681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630678594789492545166241 473008946092119408874681)
                ·
                  refine ⟨354756709569089556656011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473008946092119408874681 354756709569089556656011)
                  ·
                    rfl

theorem cell20_777247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 2].length) (baseStart_777247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777247 prefixEnd_777247 := by exact prefixLift 777247
  have htrace : WordTrace (prefixWord ++ tailWord_777247) baseStart_777247 baseEnd_777247 := by
    simpa [prefixWord, tailWord_777247, baseEnd_777247] using wordTrace_append hprefix tailTrace_777247
  have hstable : (prefixWord ++ tailWord_777247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777247).length < 2 ^ (prefixWord ++ tailWord_777247).sum := by decide
  have hdescent : baseEnd_777247 < baseStart_777247 := by decide
  rcases family_descends (prefixWord ++ tailWord_777247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777265 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_777265 : Nat := 118140960795 + 777265 * 2 ^ 59
def prefixEnd_777265 : Nat := 4983230072969 + 3 ^ 40 * 777265 * 2
def baseEnd_777265 : Nat := 354764925259561494055937

theorem tailTrace_777265 : CollatzResearch.WordTrace tailWord_777265 prefixEnd_777265 354764925259561494055937 := by
  unfold tailWord_777265
  simp only [CollatzResearch.WordTrace]
  refine ⟨28349183529109126138637249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18899455686072750759091499 28349183529109126138637249)
  ·
    refine ⟨21261887646831844603977937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28349183529109126138637249 21261887646831844603977937)
    ·
      refine ⟨15946415735123883452983453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21261887646831844603977937 15946415735123883452983453)
      ·
        refine ⟨5979905900671456294868795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15946415735123883452983453 5979905900671456294868795)
        ·
          refine ⟨8969858851007184442303193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979905900671456294868795 8969858851007184442303193)
          ·
            refine ⟨6727394138255388331727395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969858851007184442303193 6727394138255388331727395)
            ·
              refine ⟨10091091207383082497591093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727394138255388331727395 10091091207383082497591093)
              ·
                refine ⟨946039800692163984149165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10091091207383082497591093 946039800692163984149165)
                ·
                  refine ⟨354764925259561494055937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 946039800692163984149165 354764925259561494055937)
                  ·
                    rfl

theorem cell20_777265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_777265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777265 prefixEnd_777265 := by exact prefixLift 777265
  have htrace : WordTrace (prefixWord ++ tailWord_777265) baseStart_777265 baseEnd_777265 := by
    simpa [prefixWord, tailWord_777265, baseEnd_777265] using wordTrace_append hprefix tailTrace_777265
  have hstable : (prefixWord ++ tailWord_777265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777265).length < 2 ^ (prefixWord ++ tailWord_777265).sum := by decide
  have hdescent : baseEnd_777265 < baseStart_777265 := by decide
  rcases family_descends (prefixWord ++ tailWord_777265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777268 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_777268 : Nat := 118140960795 + 777268 * 2 ^ 59
def prefixEnd_777268 : Nat := 4983230072969 + 3 ^ 40 * 777268 * 2
def baseEnd_777268 : Nat := 354766294541306816955925

theorem tailTrace_777268 : CollatzResearch.WordTrace tailWord_777268 prefixEnd_777268 354766294541306816955925 := by
  unfold tailWord_777268
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174646474049128825498229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18899528632065505100664305 14174646474049128825498229)
  ·
    refine ⟨1328873106942105827390459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14174646474049128825498229 1328873106942105827390459)
    ·
      refine ⟨1993309660413158741085689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328873106942105827390459 1993309660413158741085689)
      ·
        refine ⟨1494982245309869055814267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1993309660413158741085689 1494982245309869055814267)
        ·
          refine ⟨2242473367964803583721401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494982245309869055814267 2242473367964803583721401)
          ·
            refine ⟨1681855025973602687791051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242473367964803583721401 1681855025973602687791051)
            ·
              refine ⟨2522782538960404031686577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681855025973602687791051 2522782538960404031686577)
              ·
                refine ⟨1892086904220303023764933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522782538960404031686577 1892086904220303023764933)
                ·
                  refine ⟨354766294541306816955925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892086904220303023764933 354766294541306816955925)
                  ·
                    rfl

theorem cell20_777268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_777268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777268 prefixEnd_777268 := by exact prefixLift 777268
  have htrace : WordTrace (prefixWord ++ tailWord_777268) baseStart_777268 baseEnd_777268 := by
    simpa [prefixWord, tailWord_777268, baseEnd_777268] using wordTrace_append hprefix tailTrace_777268
  have hstable : (prefixWord ++ tailWord_777268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777268).length < 2 ^ (prefixWord ++ tailWord_777268).sum := by decide
  have hdescent : baseEnd_777268 < baseStart_777268 := by decide
  rcases family_descends (prefixWord ++ tailWord_777268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777272 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_777272 : Nat := 118140960795 + 777272 * 2 ^ 59
def prefixEnd_777272 : Nat := 4983230072969 + 3 ^ 40 * 777272 * 2
def baseEnd_777272 : Nat := 354768120250300580822575

theorem tailTrace_777272 : CollatzResearch.WordTrace tailWord_777272 prefixEnd_777272 354768120250300580822575 := by
  unfold tailWord_777272
  simp only [CollatzResearch.WordTrace]
  refine ⟨14174719420041883167071035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18899625893389177556094713 14174719420041883167071035)
  ·
    refine ⟨21262079130062824750606553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14174719420041883167071035 21262079130062824750606553)
    ·
      refine ⟨15946559347547118562954915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21262079130062824750606553 15946559347547118562954915)
      ·
        refine ⟨23919839021320677844432373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15946559347547118562954915 23919839021320677844432373)
        ·
          refine ⟨2242484908248813547915535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23919839021320677844432373 2242484908248813547915535)
          ·
            refine ⟨3363727362373220321873303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242484908248813547915535 3363727362373220321873303)
            ·
              refine ⟨5045591043559830482809955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363727362373220321873303 5045591043559830482809955)
              ·
                refine ⟨7568386565339745724214933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5045591043559830482809955 7568386565339745724214933)
                ·
                  refine ⟨354768120250300580822575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7568386565339745724214933 354768120250300580822575)
                  ·
                    rfl

theorem cell20_777272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_777272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777272 prefixEnd_777272 := by exact prefixLift 777272
  have htrace : WordTrace (prefixWord ++ tailWord_777272) baseStart_777272 baseEnd_777272 := by
    simpa [prefixWord, tailWord_777272, baseEnd_777272] using wordTrace_append hprefix tailTrace_777272
  have hstable : (prefixWord ++ tailWord_777272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777272).length < 2 ^ (prefixWord ++ tailWord_777272).sum := by decide
  have hdescent : baseEnd_777272 < baseStart_777272 := by decide
  rcases family_descends (prefixWord ++ tailWord_777272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777317 : List Nat := [1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_777317 : Nat := 118140960795 + 777317 * 2 ^ 59
def prefixEnd_777317 : Nat := 4983230072969 + 3 ^ 40 * 777317 * 2
def baseEnd_777317 : Nat := 118262886492160141440797

theorem tailTrace_777317 : CollatzResearch.WordTrace tailWord_777317 prefixEnd_777317 118262886492160141440797 := by
  unfold tailWord_777317
  simp only [CollatzResearch.WordTrace]
  refine ⟨28351080124920739019530205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18900720083280492679686803 28351080124920739019530205)
  ·
    refine ⟨10631655046845277132323827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28351080124920739019530205 10631655046845277132323827)
    ·
      refine ⟨15947482570267915698485741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10631655046845277132323827 15947482570267915698485741)
      ·
        refine ⟨5980305963850468386932153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15947482570267915698485741 5980305963850468386932153)
        ·
          refine ⟨4485229472887851290199115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5980305963850468386932153 4485229472887851290199115)
          ·
            refine ⟨6727844209331776935298673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485229472887851290199115 6727844209331776935298673)
            ·
              refine ⟨5045883156998832701474005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727844209331776935298673 5045883156998832701474005)
              ·
                refine ⟨118262886492160141440797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5045883156998832701474005 118262886492160141440797)
                ·
                  rfl

theorem cell20_777317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_777317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777317 prefixEnd_777317 := by exact prefixLift 777317
  have htrace : WordTrace (prefixWord ++ tailWord_777317) baseStart_777317 baseEnd_777317 := by
    simpa [prefixWord, tailWord_777317, baseEnd_777317] using wordTrace_append hprefix tailTrace_777317
  have hstable : (prefixWord ++ tailWord_777317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777317).length < 2 ^ (prefixWord ++ tailWord_777317).sum := by decide
  have hdescent : baseEnd_777317 < baseStart_777317 := by decide
  rcases family_descends (prefixWord ++ tailWord_777317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777334 : List Nat := [5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_777334 : Nat := 118140960795 + 777334 * 2 ^ 59
def prefixEnd_777334 : Nat := 4983230072969 + 3 ^ 40 * 777334 * 2
def baseEnd_777334 : Nat := 118265472913234640251885

theorem tailTrace_777334 : CollatzResearch.WordTrace tailWord_777334 prefixEnd_777334 118265472913234640251885 := by
  unfold tailWord_777334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771981260366196932681191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18901133443906100615266037 1771981260366196932681191)
  ·
    refine ⟨2657971890549295399021787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771981260366196932681191 2657971890549295399021787)
    ·
      refine ⟨3986957835823943098532681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2657971890549295399021787 3986957835823943098532681)
      ·
        refine ⟨2990218376867957323899511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3986957835823943098532681 2990218376867957323899511)
        ·
          refine ⟨4485327565301935985849267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990218376867957323899511 4485327565301935985849267)
          ·
            refine ⟨6727991347952903978773901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485327565301935985849267 6727991347952903978773901)
            ·
              refine ⟨2522996755482338992040213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6727991347952903978773901 2522996755482338992040213)
              ·
                refine ⟨118265472913234640251885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2522996755482338992040213 118265472913234640251885)
                ·
                  rfl

theorem cell20_777334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_777334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777334 prefixEnd_777334 := by exact prefixLift 777334
  have htrace : WordTrace (prefixWord ++ tailWord_777334) baseStart_777334 baseEnd_777334 := by
    simpa [prefixWord, tailWord_777334, baseEnd_777334] using wordTrace_append hprefix tailTrace_777334
  have hstable : (prefixWord ++ tailWord_777334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777334).length < 2 ^ (prefixWord ++ tailWord_777334).sum := by decide
  have hdescent : baseEnd_777334 < baseStart_777334 := by decide
  rcases family_descends (prefixWord ++ tailWord_777334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777372 : List Nat := [2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_777372 : Nat := 118140960795 + 777372 * 2 ^ 59
def prefixEnd_777372 : Nat := 4983230072969 + 3 ^ 40 * 777372 * 2
def baseEnd_777372 : Nat := 118271254325048225829611

theorem tailTrace_777372 : CollatzResearch.WordTrace tailWord_777372 prefixEnd_777372 118271254325048225829611 := by
  unfold tailWord_777372
  simp only [CollatzResearch.WordTrace]
  refine ⟨14176543069860741706391185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18902057426480988941854913 14176543069860741706391185)
  ·
    refine ⟨10632407302395556279793389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14176543069860741706391185 10632407302395556279793389)
    ·
      refine ⟨3987152738398333604922521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10632407302395556279793389 3987152738398333604922521)
      ·
        refine ⟨2990364553798750203691891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3987152738398333604922521 2990364553798750203691891)
        ·
          refine ⟨4485546830698125305537837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990364553798750203691891 4485546830698125305537837)
          ·
            refine ⟨1682080061511796989576689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4485546830698125305537837 1682080061511796989576689)
            ·
              refine ⟨1261560046133847742182517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682080061511796989576689 1261560046133847742182517)
              ·
                refine ⟨118271254325048225829611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1261560046133847742182517 118271254325048225829611)
                ·
                  rfl

theorem cell20_777372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_777372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777372 prefixEnd_777372 := by exact prefixLift 777372
  have htrace : WordTrace (prefixWord ++ tailWord_777372) baseStart_777372 baseEnd_777372 := by
    simpa [prefixWord, tailWord_777372, baseEnd_777372] using wordTrace_append hprefix tailTrace_777372
  have hstable : (prefixWord ++ tailWord_777372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777372).length < 2 ^ (prefixWord ++ tailWord_777372).sum := by decide
  have hdescent : baseEnd_777372 < baseStart_777372 := by decide
  rcases family_descends (prefixWord ++ tailWord_777372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777400 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_777400 : Nat := 118140960795 + 777400 * 2 ^ 59
def prefixEnd_777400 : Nat := 4983230072969 + 3 ^ 40 * 777400 * 2
def baseEnd_777400 : Nat := 354826542938101024555385

theorem tailTrace_777400 : CollatzResearch.WordTrace tailWord_777400 prefixEnd_777400 354826542938101024555385 := by
  unfold tailWord_777400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14177053691810022097400827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18902738255746696129867769 14177053691810022097400827)
  ·
    refine ⟨21265580537715033146101241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14177053691810022097400827 21265580537715033146101241)
    ·
      refine ⟨15949185403286274859575931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21265580537715033146101241 15949185403286274859575931)
      ·
        refine ⟨23923778104929412289363897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15949185403286274859575931 23923778104929412289363897)
        ·
          refine ⟨17942833578697059217022923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23923778104929412289363897 17942833578697059217022923)
          ·
            refine ⟨26914250368045588825534385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17942833578697059217022923 26914250368045588825534385)
            ·
              refine ⟨20185687776034191619150789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26914250368045588825534385 20185687776034191619150789)
              ·
                refine ⟨3784816458006410928590773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20185687776034191619150789 3784816458006410928590773)
                ·
                  refine ⟨354826542938101024555385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3784816458006410928590773 354826542938101024555385)
                  ·
                    rfl

theorem cell20_777400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_777400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777400 prefixEnd_777400 := by exact prefixLift 777400
  have htrace : WordTrace (prefixWord ++ tailWord_777400) baseStart_777400 baseEnd_777400 := by
    simpa [prefixWord, tailWord_777400, baseEnd_777400] using wordTrace_append hprefix tailTrace_777400
  have hstable : (prefixWord ++ tailWord_777400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777400).length < 2 ^ (prefixWord ++ tailWord_777400).sum := by decide
  have hdescent : baseEnd_777400 < baseStart_777400 := by decide
  rcases family_descends (prefixWord ++ tailWord_777400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777431 : List Nat := [1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_777431 : Nat := 118140960795 + 777431 * 2 ^ 59
def prefixEnd_777431 : Nat := 4983230072969 + 3 ^ 40 * 777431 * 2
def baseEnd_777431 : Nat := 118280230727600898173975

theorem tailTrace_777431 : CollatzResearch.WordTrace tailWord_777431 prefixEnd_777431 118280230727600898173975 := by
  unfold tailWord_777431
  simp only [CollatzResearch.WordTrace]
  refine ⟨28355238046507736489180147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18903492031005157659453431 28355238046507736489180147)
  ·
    refine ⟨42532857069761604733770221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28355238046507736489180147 42532857069761604733770221)
    ·
      refine ⟨15949821401160601775163833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42532857069761604733770221 15949821401160601775163833)
      ·
        refine ⟨11962366050870451331372875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15949821401160601775163833 11962366050870451331372875)
        ·
          refine ⟨17943549076305676997059313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11962366050870451331372875 17943549076305676997059313)
          ·
            refine ⟨13457661807229257747794485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17943549076305676997059313 13457661807229257747794485)
            ·
              refine ⟨1261655794427742913855733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13457661807229257747794485 1261655794427742913855733)
              ·
                refine ⟨118280230727600898173975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1261655794427742913855733 118280230727600898173975)
                ·
                  rfl

theorem cell20_777431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_777431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777431 prefixEnd_777431 := by exact prefixLift 777431
  have htrace : WordTrace (prefixWord ++ tailWord_777431) baseStart_777431 baseEnd_777431 := by
    simpa [prefixWord, tailWord_777431, baseEnd_777431] using wordTrace_append hprefix tailTrace_777431
  have hstable : (prefixWord ++ tailWord_777431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777431).length < 2 ^ (prefixWord ++ tailWord_777431).sum := by decide
  have hdescent : baseEnd_777431 < baseStart_777431 := by decide
  rcases family_descends (prefixWord ++ tailWord_777431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777448 : List Nat := [2, 1, 4, 1, 2, 1, 5, 4]
def baseStart_777448 : Nat := 118140960795 + 777448 * 2 ^ 59
def prefixEnd_777448 : Nat := 4983230072969 + 3 ^ 40 * 777448 * 2
def baseEnd_777448 : Nat := 118282817148675396985063

theorem tailTrace_777448 : CollatzResearch.WordTrace tailWord_777448 prefixEnd_777448 118282817148675396985063 := by
  unfold tailWord_777448
  simp only [CollatzResearch.WordTrace]
  refine ⟨14177929043723074196274499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18903905391630765595032665 14177929043723074196274499)
  ·
    refine ⟨21266893565584611294411749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14177929043723074196274499 21266893565584611294411749)
    ·
      refine ⟨3987542543547114617702203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21266893565584611294411749 3987542543547114617702203)
      ·
        refine ⟨5981313815320671926553305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987542543547114617702203 5981313815320671926553305)
        ·
          refine ⟨4485985361490503944914979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5981313815320671926553305 4485985361490503944914979)
          ·
            refine ⟨6728978042235755917372469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485985361490503944914979 6728978042235755917372469)
            ·
              refine ⟨630841691459602117253669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6728978042235755917372469 630841691459602117253669)
              ·
                refine ⟨118282817148675396985063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630841691459602117253669 118282817148675396985063)
                ·
                  rfl

theorem cell20_777448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_777448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777448 prefixEnd_777448 := by exact prefixLift 777448
  have htrace : WordTrace (prefixWord ++ tailWord_777448) baseStart_777448 baseEnd_777448 := by
    simpa [prefixWord, tailWord_777448, baseEnd_777448] using wordTrace_append hprefix tailTrace_777448
  have hstable : (prefixWord ++ tailWord_777448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777448).length < 2 ^ (prefixWord ++ tailWord_777448).sum := by decide
  have hdescent : baseEnd_777448 < baseStart_777448 := by decide
  rcases family_descends (prefixWord ++ tailWord_777448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777462 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_777462 : Nat := 118140960795 + 777462 * 2 ^ 59
def prefixEnd_777462 : Nat := 4983230072969 + 3 ^ 40 * 777462 * 2
def baseEnd_777462 : Nat := 354854841427504364488465

theorem tailTrace_777462 : CollatzResearch.WordTrace tailWord_777462 prefixEnd_777462 354854841427504364488465 := by
  unfold tailWord_777462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772273044337214298972415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18904245806263619189039093 1772273044337214298972415)
  ·
    refine ⟨2658409566505821448458623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1772273044337214298972415 2658409566505821448458623)
    ·
      refine ⟨3987614349758732172687935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658409566505821448458623 3987614349758732172687935)
      ·
        refine ⟨5981421524638098259031903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987614349758732172687935 5981421524638098259031903)
        ·
          refine ⟨8972132286957147388547855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981421524638098259031903 8972132286957147388547855)
          ·
            refine ⟨13458198430435721082821783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972132286957147388547855 13458198430435721082821783)
            ·
              refine ⟨20187297645653581624232675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13458198430435721082821783 20187297645653581624232675)
              ·
                refine ⟨30280946468480372436349013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20187297645653581624232675 30280946468480372436349013)
                ·
                  refine ⟨354854841427504364488465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30280946468480372436349013 354854841427504364488465)
                  ·
                    rfl

theorem cell20_777462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_777462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777462 prefixEnd_777462 := by exact prefixLift 777462
  have htrace : WordTrace (prefixWord ++ tailWord_777462) baseStart_777462 baseEnd_777462 := by
    simpa [prefixWord, tailWord_777462, baseEnd_777462] using wordTrace_append hprefix tailTrace_777462
  have hstable : (prefixWord ++ tailWord_777462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777462).length < 2 ^ (prefixWord ++ tailWord_777462).sum := by decide
  have hdescent : baseEnd_777462 < baseStart_777462 := by decide
  rcases family_descends (prefixWord ++ tailWord_777462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777500 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_777500 : Nat := 118140960795 + 777500 * 2 ^ 59
def prefixEnd_777500 : Nat := 4983230072969 + 3 ^ 40 * 777500 * 2
def baseEnd_777500 : Nat := 354872185662945121221643

theorem tailTrace_777500 : CollatzResearch.WordTrace tailWord_777500 prefixEnd_777500 354872185662945121221643 := by
  unfold tailWord_777500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14178877341628880636720977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18905169788838507515627969 14178877341628880636720977)
  ·
    refine ⟨10634158006221660477540733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14178877341628880636720977 10634158006221660477540733)
    ·
      refine ⟨3987809252333122679077775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10634158006221660477540733 3987809252333122679077775)
      ·
        refine ⟨5981713878499684018616663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987809252333122679077775 5981713878499684018616663)
        ·
          refine ⟨8972570817749526027924995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981713878499684018616663 8972570817749526027924995)
          ·
            refine ⟨13458856226624289041887493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972570817749526027924995 13458856226624289041887493)
            ·
              refine ⟨2523535542492054195353905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13458856226624289041887493 2523535542492054195353905)
              ·
                refine ⟨1892651656869040646515429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2523535542492054195353905 1892651656869040646515429)
                ·
                  refine ⟨354872185662945121221643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1892651656869040646515429 354872185662945121221643)
                  ·
                    rfl

theorem cell20_777500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_777500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777500 prefixEnd_777500 := by exact prefixLift 777500
  have htrace : WordTrace (prefixWord ++ tailWord_777500) baseStart_777500 baseEnd_777500 := by
    simpa [prefixWord, tailWord_777500, baseEnd_777500] using wordTrace_append hprefix tailTrace_777500
  have hstable : (prefixWord ++ tailWord_777500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777500).length < 2 ^ (prefixWord ++ tailWord_777500).sum := by decide
  have hdescent : baseEnd_777500 < baseStart_777500 := by decide
  rcases family_descends (prefixWord ++ tailWord_777500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777503 : List Nat := [1, 1, 2, 4, 4, 2, 2, 4]
def baseStart_777503 : Nat := 118140960795 + 777503 * 2 ^ 59
def prefixEnd_777503 : Nat := 4983230072969 + 3 ^ 40 * 777503 * 2
def baseEnd_777503 : Nat := 118291184981563481373877

theorem tailTrace_777503 : CollatzResearch.WordTrace tailWord_777503 prefixEnd_777503 118291184981563481373877 := by
  unfold tailWord_777503
  simp only [CollatzResearch.WordTrace]
  refine ⟨28357864102246892785801163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18905242734831261857200775 28357864102246892785801163)
  ·
    refine ⟨42536796153370339178701745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28357864102246892785801163 42536796153370339178701745)
    ·
      refine ⟨31902597115027754384026309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42536796153370339178701745 31902597115027754384026309)
      ·
        refine ⟨5981736959067703947004933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31902597115027754384026309 5981736959067703947004933)
        ·
          refine ⟨1121575679825194490063425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5981736959067703947004933 1121575679825194490063425)
          ·
            refine ⟨841181759868895867547569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121575679825194490063425 841181759868895867547569)
            ·
              refine ⟨630886319901671900660677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841181759868895867547569 630886319901671900660677)
              ·
                refine ⟨118291184981563481373877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630886319901671900660677 118291184981563481373877)
                ·
                  rfl

theorem cell20_777503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_777503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777503 prefixEnd_777503 := by exact prefixLift 777503
  have htrace : WordTrace (prefixWord ++ tailWord_777503) baseStart_777503 baseEnd_777503 := by
    simpa [prefixWord, tailWord_777503, baseEnd_777503] using wordTrace_append hprefix tailTrace_777503
  have hstable : (prefixWord ++ tailWord_777503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777503).length < 2 ^ (prefixWord ++ tailWord_777503).sum := by decide
  have hdescent : baseEnd_777503 < baseStart_777503 := by decide
  rcases family_descends (prefixWord ++ tailWord_777503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777507 : List Nat := [1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_777507 : Nat := 118140960795 + 777507 * 2 ^ 59
def prefixEnd_777507 : Nat := 4983230072969 + 3 ^ 40 * 777507 * 2
def baseEnd_777507 : Nat := 118291793551228069329427

theorem tailTrace_777507 : CollatzResearch.WordTrace tailWord_777507 prefixEnd_777507 118291793551228069329427 := by
  unfold tailWord_777507
  simp only [CollatzResearch.WordTrace]
  refine ⟨28358009994232401468946775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18905339996154934312631183 28358009994232401468946775)
  ·
    refine ⟨42537014991348602203420163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28358009994232401468946775 42537014991348602203420163)
    ·
      refine ⟨63805522487022903305130245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42537014991348602203420163 63805522487022903305130245)
      ·
        refine ⟨11963535466316794369711921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63805522487022903305130245 11963535466316794369711921)
        ·
          refine ⟨8972651599737595777283941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11963535466316794369711921 8972651599737595777283941)
          ·
            refine ⟨1682372174950799208240739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8972651599737595777283941 1682372174950799208240739)
            ·
              refine ⟨2523558262426198812361109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682372174950799208240739 2523558262426198812361109)
              ·
                refine ⟨118291793551228069329427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2523558262426198812361109 118291793551228069329427)
                ·
                  rfl

theorem cell20_777507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_777507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777507 prefixEnd_777507 := by exact prefixLift 777507
  have htrace : WordTrace (prefixWord ++ tailWord_777507) baseStart_777507 baseEnd_777507 := by
    simpa [prefixWord, tailWord_777507, baseEnd_777507] using wordTrace_append hprefix tailTrace_777507
  have hstable : (prefixWord ++ tailWord_777507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777507).length < 2 ^ (prefixWord ++ tailWord_777507).sum := by decide
  have hdescent : baseEnd_777507 < baseStart_777507 := by decide
  rcases family_descends (prefixWord ++ tailWord_777507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777548 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_777548 : Nat := 118140960795 + 777548 * 2 ^ 59
def prefixEnd_777548 : Nat := 4983230072969 + 3 ^ 40 * 777548 * 2
def baseEnd_777548 : Nat := 354894094170870287621447

theorem tailTrace_777548 : CollatzResearch.WordTrace tailWord_777548 prefixEnd_777548 354894094170870287621447 := by
  unfold tailWord_777548
  simp only [CollatzResearch.WordTrace]
  refine ⟨14179752693541932735594649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18906336924722576980792865 14179752693541932735594649)
  ·
    refine ⟨10634814520156449551695987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14179752693541932735594649 10634814520156449551695987)
    ·
      refine ⟨15952221780234674327543981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10634814520156449551695987 15952221780234674327543981)
      ·
        refine ⟨5982083167588002872828993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15952221780234674327543981 5982083167588002872828993)
        ·
          refine ⟨4486562375691002154621745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5982083167588002872828993 4486562375691002154621745)
          ·
            refine ⟨3364921781768251615966309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4486562375691002154621745 3364921781768251615966309)
            ·
              refine ⟨630922834081547177993683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3364921781768251615966309 630922834081547177993683)
              ·
                refine ⟨946384251122320766990525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630922834081547177993683 946384251122320766990525)
                ·
                  refine ⟨354894094170870287621447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 946384251122320766990525 354894094170870287621447)
                  ·
                    rfl

theorem cell20_777548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_777548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777548 prefixEnd_777548 := by exact prefixLift 777548
  have htrace : WordTrace (prefixWord ++ tailWord_777548) baseStart_777548 baseEnd_777548 := by
    simpa [prefixWord, tailWord_777548, baseEnd_777548] using wordTrace_append hprefix tailTrace_777548
  have hstable : (prefixWord ++ tailWord_777548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777548).length < 2 ^ (prefixWord ++ tailWord_777548).sum := by decide
  have hdescent : baseEnd_777548 < baseStart_777548 := by decide
  rcases family_descends (prefixWord ++ tailWord_777548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777607 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_777607 : Nat := 118140960795 + 777607 * 2 ^ 59
def prefixEnd_777607 : Nat := 4983230072969 + 3 ^ 40 * 777607 * 2
def baseEnd_777607 : Nat := 354921023378528304654539

theorem tailTrace_777607 : CollatzResearch.WordTrace tailWord_777607 prefixEnd_777607 354921023378528304654539 := by
  unfold tailWord_777607
  simp only [CollatzResearch.WordTrace]
  refine ⟨28361657293870118547587075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18907771529246745698391383 28361657293870118547587075)
  ·
    refine ⟨42542485940805177821380613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28361657293870118547587075 42542485940805177821380613)
    ·
      refine ⟨7976716113900970841508865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42542485940805177821380613 7976716113900970841508865)
      ·
        refine ⟨5982537085425728131131649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7976716113900970841508865 5982537085425728131131649)
        ·
          refine ⟨4486902814069296098348737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5982537085425728131131649 4486902814069296098348737)
          ·
            refine ⟨3365177110551972073761553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4486902814069296098348737 3365177110551972073761553)
            ·
              refine ⟨2523882832913979055321165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3365177110551972073761553 2523882832913979055321165)
              ·
                refine ⟨946456062342742145745437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2523882832913979055321165 946456062342742145745437)
                ·
                  refine ⟨354921023378528304654539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 946456062342742145745437 354921023378528304654539)
                  ·
                    rfl

theorem cell20_777607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_777607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777607 prefixEnd_777607 := by exact prefixLift 777607
  have htrace : WordTrace (prefixWord ++ tailWord_777607) baseStart_777607 baseEnd_777607 := by
    simpa [prefixWord, tailWord_777607, baseEnd_777607] using wordTrace_append hprefix tailTrace_777607
  have hstable : (prefixWord ++ tailWord_777607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777607).length < 2 ^ (prefixWord ++ tailWord_777607).sum := by decide
  have hdescent : baseEnd_777607 < baseStart_777607 := by decide
  rcases family_descends (prefixWord ++ tailWord_777607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777631 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 2]
def baseStart_777631 : Nat := 118140960795 + 777631 * 2 ^ 59
def prefixEnd_777631 : Nat := 4983230072969 + 3 ^ 40 * 777631 * 2
def baseEnd_777631 : Nat := 354931977632490887854441

theorem tailTrace_777631 : CollatzResearch.WordTrace tailWord_777631 prefixEnd_777631 354931977632490887854441 := by
  unfold tailWord_777631
  simp only [CollatzResearch.WordTrace]
  refine ⟨28362532645783170646460747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18908355097188780430973831 28362532645783170646460747)
  ·
    refine ⟨42543798968674755969691121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28362532645783170646460747 42543798968674755969691121)
    ·
      refine ⟨31907849226506066977268341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42543798968674755969691121 31907849226506066977268341)
      ·
        refine ⟨2991360864984943779118907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31907849226506066977268341 2991360864984943779118907)
        ·
          refine ⟨4487041297477415668678361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991360864984943779118907 4487041297477415668678361)
          ·
            refine ⟨3365280973108061751508771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487041297477415668678361 3365280973108061751508771)
            ·
              refine ⟨5047921459662092627263157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365280973108061751508771 5047921459662092627263157)
              ·
                refine ⟨473242636843321183805921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5047921459662092627263157 473242636843321183805921)
                ·
                  refine ⟨354931977632490887854441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473242636843321183805921 354931977632490887854441)
                  ·
                    rfl

theorem cell20_777631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 2].length) (baseStart_777631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777631 prefixEnd_777631 := by exact prefixLift 777631
  have htrace : WordTrace (prefixWord ++ tailWord_777631) baseStart_777631 baseEnd_777631 := by
    simpa [prefixWord, tailWord_777631, baseEnd_777631] using wordTrace_append hprefix tailTrace_777631
  have hstable : (prefixWord ++ tailWord_777631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777631).length < 2 ^ (prefixWord ++ tailWord_777631).sum := by decide
  have hdescent : baseEnd_777631 < baseStart_777631 := by decide
  rcases family_descends (prefixWord ++ tailWord_777631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777635 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_777635 : Nat := 118140960795 + 777635 * 2 ^ 59
def prefixEnd_777635 : Nat := 4983230072969 + 3 ^ 40 * 777635 * 2
def baseEnd_777635 : Nat := 354933803341484651721091

theorem tailTrace_777635 : CollatzResearch.WordTrace tailWord_777635 prefixEnd_777635 354933803341484651721091 := by
  unfold tailWord_777635
  simp only [CollatzResearch.WordTrace]
  refine ⟨28362678537768679329606359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18908452358512452886404239 28362678537768679329606359)
  ·
    refine ⟨42544017806653018994409539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28362678537768679329606359 42544017806653018994409539)
    ·
      refine ⟨63816026709979528491614309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42544017806653018994409539 63816026709979528491614309)
      ·
        refine ⟨11965505008121161592177683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63816026709979528491614309 11965505008121161592177683)
        ·
          refine ⟨17948257512181742388266525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11965505008121161592177683 17948257512181742388266525)
          ·
            refine ⟨6730596567068153395599947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17948257512181742388266525 6730596567068153395599947)
            ·
              refine ⟨10095894850602230093399921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730596567068153395599947 10095894850602230093399921)
              ·
                refine ⟨7571921137951672570049941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10095894850602230093399921 7571921137951672570049941)
                ·
                  refine ⟨354933803341484651721091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7571921137951672570049941 354933803341484651721091)
                  ·
                    rfl

theorem cell20_777635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_777635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777635 prefixEnd_777635 := by exact prefixLift 777635
  have htrace : WordTrace (prefixWord ++ tailWord_777635) baseStart_777635 baseEnd_777635 := by
    simpa [prefixWord, tailWord_777635, baseEnd_777635] using wordTrace_append hprefix tailTrace_777635
  have hstable : (prefixWord ++ tailWord_777635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777635).length < 2 ^ (prefixWord ++ tailWord_777635).sum := by decide
  have hdescent : baseEnd_777635 < baseStart_777635 := by decide
  rcases family_descends (prefixWord ++ tailWord_777635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777676 : List Nat := [2, 2, 1, 4, 2, 1, 4, 4]
def baseStart_777676 : Nat := 118140960795 + 777676 * 2 ^ 59
def prefixEnd_777676 : Nat := 4983230072969 + 3 ^ 40 * 777676 * 2
def baseEnd_777676 : Nat := 118317505619556910451419

theorem tailTrace_777676 : CollatzResearch.WordTrace tailWord_777676 prefixEnd_777676 118317505619556910451419 := by
  unfold tailWord_777676
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182086965310071665924441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18909449287080095554565921 14182086965310071665924441)
  ·
    refine ⟨10636565223982553749443331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14182086965310071665924441 10636565223982553749443331)
    ·
      refine ⟨15954847835973830624164997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10636565223982553749443331 15954847835973830624164997)
      ·
        refine ⟨2991533969245093242030937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15954847835973830624164997 2991533969245093242030937)
        ·
          refine ⟨2243650476933819931523203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2991533969245093242030937 2243650476933819931523203)
          ·
            refine ⟨3365475715400729897284805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243650476933819931523203 3365475715400729897284805)
            ·
              refine ⟨631026696637636855740901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3365475715400729897284805 631026696637636855740901)
              ·
                refine ⟨118317505619556910451419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 631026696637636855740901 118317505619556910451419)
                ·
                  rfl

theorem cell20_777676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_777676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777676 prefixEnd_777676 := by exact prefixLift 777676
  have htrace : WordTrace (prefixWord ++ tailWord_777676) baseStart_777676 baseEnd_777676 := by
    simpa [prefixWord, tailWord_777676, baseEnd_777676] using wordTrace_append hprefix tailTrace_777676
  have hstable : (prefixWord ++ tailWord_777676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777676).length < 2 ^ (prefixWord ++ tailWord_777676).sum := by decide
  have hdescent : baseEnd_777676 < baseStart_777676 := by decide
  rcases family_descends (prefixWord ++ tailWord_777676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777680 : List Nat := [2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_777680 : Nat := 118140960795 + 777680 * 2 ^ 59
def prefixEnd_777680 : Nat := 4983230072969 + 3 ^ 40 * 777680 * 2
def baseEnd_777680 : Nat := 118318114189221498406969

theorem tailTrace_777680 : CollatzResearch.WordTrace tailWord_777680 prefixEnd_777680 118318114189221498406969 := by
  unfold tailWord_777680
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182159911302826007497247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18909546548403768009996329 14182159911302826007497247)
  ·
    refine ⟨21273239866954239011245871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14182159911302826007497247 21273239866954239011245871)
    ·
      refine ⟨31909859800431358516868807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21273239866954239011245871 31909859800431358516868807)
      ·
        refine ⟨47864789700647037775303211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31909859800431358516868807 47864789700647037775303211)
        ·
          refine ⟨71797184550970556662954817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47864789700647037775303211 71797184550970556662954817)
          ·
            refine ⟨53847888413227917497216113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71797184550970556662954817 53847888413227917497216113)
            ·
              refine ⟨40385916309920938122912085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53847888413227917497216113 40385916309920938122912085)
              ·
                refine ⟨118318114189221498406969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40385916309920938122912085 118318114189221498406969)
                ·
                  rfl

theorem cell20_777680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_777680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777680 prefixEnd_777680 := by exact prefixLift 777680
  have htrace : WordTrace (prefixWord ++ tailWord_777680) baseStart_777680 baseEnd_777680 := by
    simpa [prefixWord, tailWord_777680, baseEnd_777680] using wordTrace_append hprefix tailTrace_777680
  have hstable : (prefixWord ++ tailWord_777680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777680).length < 2 ^ (prefixWord ++ tailWord_777680).sum := by decide
  have hdescent : baseEnd_777680 < baseStart_777680 := by decide
  rcases family_descends (prefixWord ++ tailWord_777680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777697 : List Nat := [1, 2, 3, 1, 2, 5, 6]
def baseStart_777697 : Nat := 118140960795 + 777697 * 2 ^ 59
def prefixEnd_777697 : Nat := 4983230072969 + 3 ^ 40 * 777697 * 2
def baseEnd_777697 : Nat := 39440233536765332406019

theorem tailTrace_777697 : CollatzResearch.WordTrace tailWord_777697 prefixEnd_777697 39440233536765332406019 := by
  unfold tailWord_777697
  simp only [CollatzResearch.WordTrace]
  refine ⟨28364939863544063918363345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18909959909029375945575563 28364939863544063918363345)
  ·
    refine ⟨21273704897658047938772509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28364939863544063918363345 21273704897658047938772509)
    ·
      refine ⟨7977639336621767977039691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21273704897658047938772509 7977639336621767977039691)
      ·
        refine ⟨11966459004932651965559537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977639336621767977039691 11966459004932651965559537)
        ·
          refine ⟨8974844253699488974169653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11966459004932651965559537 8974844253699488974169653)
          ·
            refine ⟨841391648784327091328405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8974844253699488974169653 841391648784327091328405)
            ·
              refine ⟨39440233536765332406019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 841391648784327091328405 39440233536765332406019)
              ·
                rfl

theorem cell20_777697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_777697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777697 prefixEnd_777697 := by exact prefixLift 777697
  have htrace : WordTrace (prefixWord ++ tailWord_777697) baseStart_777697 baseEnd_777697 := by
    simpa [prefixWord, tailWord_777697, baseEnd_777697] using wordTrace_append hprefix tailTrace_777697
  have hstable : (prefixWord ++ tailWord_777697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777697).length < 2 ^ (prefixWord ++ tailWord_777697).sum := by decide
  have hdescent : baseEnd_777697 < baseStart_777697 := by decide
  rcases family_descends (prefixWord ++ tailWord_777697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777704 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_777704 : Nat := 118140960795 + 777704 * 2 ^ 59
def prefixEnd_777704 : Nat := 4983230072969 + 3 ^ 40 * 777704 * 2
def baseEnd_777704 : Nat := 354965296821627078420809

theorem tailTrace_777704 : CollatzResearch.WordTrace tailWord_777704 prefixEnd_777704 354965296821627078420809 := by
  unfold tailWord_777704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182597587259352056934083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18910130116345802742578777 14182597587259352056934083)
  ·
    refine ⟨21273896380889028085401125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14182597587259352056934083 21273896380889028085401125)
    ·
      refine ⟨3988855571416692766012711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21273896380889028085401125 3988855571416692766012711)
      ·
        refine ⟨5983283357125039149019067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988855571416692766012711 5983283357125039149019067)
        ·
          refine ⟨8974925035687558723528601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983283357125039149019067 8974925035687558723528601)
          ·
            refine ⟨6731193776765669042646451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8974925035687558723528601 6731193776765669042646451)
            ·
              refine ⟨10096790665148503563969677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731193776765669042646451 10096790665148503563969677)
              ·
                refine ⟨3786296499430688836488629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10096790665148503563969677 3786296499430688836488629)
                ·
                  refine ⟨354965296821627078420809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786296499430688836488629 354965296821627078420809)
                  ·
                    rfl

theorem cell20_777704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_777704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777704 prefixEnd_777704 := by exact prefixLift 777704
  have htrace : WordTrace (prefixWord ++ tailWord_777704) baseStart_777704 baseEnd_777704 := by
    simpa [prefixWord, tailWord_777704, baseEnd_777704] using wordTrace_append hprefix tailTrace_777704
  have hstable : (prefixWord ++ tailWord_777704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777704).length < 2 ^ (prefixWord ++ tailWord_777704).sum := by decide
  have hdescent : baseEnd_777704 < baseStart_777704 := by decide
  rcases family_descends (prefixWord ++ tailWord_777704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777714 : List Nat := [3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_777714 : Nat := 118140960795 + 777714 * 2 ^ 59
def prefixEnd_777714 : Nat := 4983230072969 + 3 ^ 40 * 777714 * 2
def baseEnd_777714 : Nat := 118323287031370496029145

theorem tailTrace_777714 : CollatzResearch.WordTrace tailWord_777714 prefixEnd_777714 118323287031370496029145 := by
  unfold tailWord_777714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091389976120618955433049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18910373269654983881154797 7091389976120618955433049)
  ·
    refine ⟨5318542482090464216574787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7091389976120618955433049 5318542482090464216574787)
    ·
      refine ⟨7977813723135696324862181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318542482090464216574787 7977813723135696324862181)
      ·
        refine ⟨1495840073087943060911659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7977813723135696324862181 1495840073087943060911659)
        ·
          refine ⟨2243760109631914591367489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495840073087943060911659 2243760109631914591367489)
          ·
            refine ⟨1682820082223935943525617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2243760109631914591367489 1682820082223935943525617)
            ·
              refine ⟨1262115061667951957644213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682820082223935943525617 1262115061667951957644213)
              ·
                refine ⟨118323287031370496029145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1262115061667951957644213 118323287031370496029145)
                ·
                  rfl

theorem cell20_777714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_777714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777714 prefixEnd_777714 := by exact prefixLift 777714
  have htrace : WordTrace (prefixWord ++ tailWord_777714) baseStart_777714 baseEnd_777714 := by
    simpa [prefixWord, tailWord_777714, baseEnd_777714] using wordTrace_append hprefix tailTrace_777714
  have hstable : (prefixWord ++ tailWord_777714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777714).length < 2 ^ (prefixWord ++ tailWord_777714).sum := by decide
  have hdescent : baseEnd_777714 < baseStart_777714 := by decide
  rcases family_descends (prefixWord ++ tailWord_777714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777717 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 3]
def baseStart_777717 : Nat := 118140960795 + 777717 * 2 ^ 59
def prefixEnd_777717 : Nat := 4983230072969 + 3 ^ 40 * 777717 * 2
def baseEnd_777717 : Nat := 354971230375856810987423

theorem tailTrace_777717 : CollatzResearch.WordTrace tailWord_777717 prefixEnd_777717 354971230375856810987423 := by
  unfold tailWord_777717
  simp only [CollatzResearch.WordTrace]
  refine ⟨28365669323471607334091405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18910446215647738222727603 28365669323471607334091405)
  ·
    refine ⟨10637125996301852750284277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28365669323471607334091405 10637125996301852750284277)
    ·
      refine ⟨997230562153298695339151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10637125996301852750284277 997230562153298695339151)
      ·
        refine ⟨1495845843229948043008727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997230562153298695339151 1495845843229948043008727)
        ·
          refine ⟨2243768764844922064513091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495845843229948043008727 2243768764844922064513091)
          ·
            refine ⟨3365653147267383096769637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243768764844922064513091 3365653147267383096769637)
            ·
              refine ⟨631059965112634330644307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3365653147267383096769637 631059965112634330644307)
              ·
                refine ⟨946589947668951495966461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631059965112634330644307 946589947668951495966461)
                ·
                  refine ⟨354971230375856810987423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 946589947668951495966461 354971230375856810987423)
                  ·
                    rfl

theorem cell20_777717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_777717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777717 prefixEnd_777717 := by exact prefixLift 777717
  have htrace : WordTrace (prefixWord ++ tailWord_777717) baseStart_777717 baseEnd_777717 := by
    simpa [prefixWord, tailWord_777717, baseEnd_777717] using wordTrace_append hprefix tailTrace_777717
  have hstable : (prefixWord ++ tailWord_777717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777717).length < 2 ^ (prefixWord ++ tailWord_777717).sum := by decide
  have hdescent : baseEnd_777717 < baseStart_777717 := by decide
  rcases family_descends (prefixWord ++ tailWord_777717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777735 : List Nat := [1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_777735 : Nat := 118140960795 + 777735 * 2 ^ 59
def prefixEnd_777735 : Nat := 4983230072969 + 3 ^ 40 * 777735 * 2
def baseEnd_777735 : Nat := 118326482022109582795783

theorem tailTrace_777735 : CollatzResearch.WordTrace tailWord_777735 prefixEnd_777735 118326482022109582795783 := by
  unfold tailWord_777735
  simp only [CollatzResearch.WordTrace]
  refine ⟨28366325837406396408246659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18910883891604264272164439 28366325837406396408246659)
  ·
    refine ⟨42549488756109594612369989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28366325837406396408246659 42549488756109594612369989)
    ·
      refine ⟨7978029141770548989819373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42549488756109594612369989 7978029141770548989819373)
      ·
        refine ⟨2991760928163955871182265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7978029141770548989819373 2991760928163955871182265)
        ·
          refine ⟨2243820696122966903386699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2991760928163955871182265 2243820696122966903386699)
          ·
            refine ⟨3365731044184450355080049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243820696122966903386699 3365731044184450355080049)
            ·
              refine ⟨2524298283138337766310037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3365731044184450355080049 2524298283138337766310037)
              ·
                refine ⟨118326482022109582795783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2524298283138337766310037 118326482022109582795783)
                ·
                  rfl

theorem cell20_777735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_777735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777735 prefixEnd_777735 := by exact prefixLift 777735
  have htrace : WordTrace (prefixWord ++ tailWord_777735) baseStart_777735 baseEnd_777735 := by
    simpa [prefixWord, tailWord_777735, baseEnd_777735] using wordTrace_append hprefix tailTrace_777735
  have hstable : (prefixWord ++ tailWord_777735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777735).length < 2 ^ (prefixWord ++ tailWord_777735).sum := by decide
  have hdescent : baseEnd_777735 < baseStart_777735 := by decide
  rcases family_descends (prefixWord ++ tailWord_777735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777762 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_777762 : Nat := 118140960795 + 777762 * 2 ^ 59
def prefixEnd_777762 : Nat := 4983230072969 + 3 ^ 40 * 777762 * 2
def baseEnd_777762 : Nat := 354991769602036654487239

theorem tailTrace_777762 : CollatzResearch.WordTrace tailWord_777762 prefixEnd_777762 354991769602036654487239 := by
  unfold tailWord_777762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091827652077145004869885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18911540405539053346319693 7091827652077145004869885)
  ·
    refine ⟨2659435369528929376826207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7091827652077145004869885 2659435369528929376826207)
    ·
      refine ⟨3989153054293394065239311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659435369528929376826207 3989153054293394065239311)
      ·
        refine ⟨5983729581440091097858967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989153054293394065239311 5983729581440091097858967)
        ·
          refine ⟨8975594372160136646788451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983729581440091097858967 8975594372160136646788451)
          ·
            refine ⟨13463391558240204970182677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8975594372160136646788451 13463391558240204970182677)
            ·
              refine ⟨631096479292509607977313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13463391558240204970182677 631096479292509607977313)
              ·
                refine ⟨473322359469382205982985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631096479292509607977313 473322359469382205982985)
                ·
                  refine ⟨354991769602036654487239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473322359469382205982985 354991769602036654487239)
                  ·
                    rfl

theorem cell20_777762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_777762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777762 prefixEnd_777762 := by exact prefixLift 777762
  have htrace : WordTrace (prefixWord ++ tailWord_777762) baseStart_777762 baseEnd_777762 := by
    simpa [prefixWord, tailWord_777762, baseEnd_777762] using wordTrace_append hprefix tailTrace_777762
  have hstable : (prefixWord ++ tailWord_777762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777762).length < 2 ^ (prefixWord ++ tailWord_777762).sum := by decide
  have hdescent : baseEnd_777762 < baseStart_777762 := by decide
  rcases family_descends (prefixWord ++ tailWord_777762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777842 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_777842 : Nat := 118140960795 + 777842 * 2 ^ 59
def prefixEnd_777842 : Nat := 4983230072969 + 3 ^ 40 * 777842 * 2
def baseEnd_777842 : Nat := 355028283781911931820245

theorem tailTrace_777842 : CollatzResearch.WordTrace tailWord_777842 prefixEnd_777842 355028283781911931820245 := by
  unfold tailWord_777842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092557112004688420597945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18913485632012502454927853 7092557112004688420597945)
  ·
    refine ⟨5319417834003516315448459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7092557112004688420597945 5319417834003516315448459)
    ·
      refine ⟨7979126751005274473172689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319417834003516315448459 7979126751005274473172689)
      ·
        refine ⟨5984345063253955854879517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7979126751005274473172689 5984345063253955854879517)
        ·
          refine ⟨2244129398720233445579819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5984345063253955854879517 2244129398720233445579819)
          ·
            refine ⟨3366194098080350168369729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244129398720233445579819 3366194098080350168369729)
            ·
              refine ⟨2524645573560262626277297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366194098080350168369729 2524645573560262626277297)
              ·
                refine ⟨1893484180170196969707973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524645573560262626277297 1893484180170196969707973)
                ·
                  refine ⟨355028283781911931820245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893484180170196969707973 355028283781911931820245)
                  ·
                    rfl

theorem cell20_777842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_777842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777842 prefixEnd_777842 := by exact prefixLift 777842
  have htrace : WordTrace (prefixWord ++ tailWord_777842) baseStart_777842 baseEnd_777842 := by
    simpa [prefixWord, tailWord_777842, baseEnd_777842] using wordTrace_append hprefix tailTrace_777842
  have hstable : (prefixWord ++ tailWord_777842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777842).length < 2 ^ (prefixWord ++ tailWord_777842).sum := by decide
  have hdescent : baseEnd_777842 < baseStart_777842 := by decide
  rcases family_descends (prefixWord ++ tailWord_777842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777845 : List Nat := [1, 3, 4, 2, 1, 3, 2, 4]
def baseStart_777845 : Nat := 118140960795 + 777845 * 2 ^ 59
def prefixEnd_777845 : Nat := 4983230072969 + 3 ^ 40 * 777845 * 2
def baseEnd_777845 : Nat := 118343217687885751573411

theorem tailTrace_777845 : CollatzResearch.WordTrace tailWord_777845 prefixEnd_777845 118343217687885751573411 := by
  unfold tailWord_777845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370337867007885194750989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18913558578005256796500659 28370337867007885194750989)
  ·
    refine ⟨10638876700127956948031621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28370337867007885194750989 10638876700127956948031621)
    ·
      refine ⟨1994789381273991927755929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10638876700127956948031621 1994789381273991927755929)
      ·
        refine ⟨1496092035955493945816947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1994789381273991927755929 1496092035955493945816947)
        ·
          refine ⟨2244138053933240918725421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496092035955493945816947 2244138053933240918725421)
          ·
            refine ⟨841551770224965344522033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2244138053933240918725421 841551770224965344522033)
            ·
              refine ⟨631163827668724008391525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841551770224965344522033 631163827668724008391525)
              ·
                refine ⟨118343217687885751573411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 631163827668724008391525 118343217687885751573411)
                ·
                  rfl

theorem cell20_777845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_777845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777845 prefixEnd_777845 := by exact prefixLift 777845
  have htrace : WordTrace (prefixWord ++ tailWord_777845) baseStart_777845 baseEnd_777845 := by
    simpa [prefixWord, tailWord_777845, baseEnd_777845] using wordTrace_append hprefix tailTrace_777845
  have hstable : (prefixWord ++ tailWord_777845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777845).length < 2 ^ (prefixWord ++ tailWord_777845).sum := by decide
  have hdescent : baseEnd_777845 < baseStart_777845 := by decide
  rcases family_descends (prefixWord ++ tailWord_777845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777876 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_777876 : Nat := 118140960795 + 777876 * 2 ^ 59
def prefixEnd_777876 : Nat := 4983230072969 + 3 ^ 40 * 777876 * 2
def baseEnd_777876 : Nat := 355043802308358924686773

theorem tailTrace_777876 : CollatzResearch.WordTrace tailWord_777876 prefixEnd_777876 355043802308358924686773 := by
  unfold tailWord_777876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185734264947788744564741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18914312353263718326086321 14185734264947788744564741)
  ·
    refine ⟨2659825174677710389605889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14185734264947788744564741 2659825174677710389605889)
    ·
      refine ⟨1994868881008282792204417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2659825174677710389605889 1994868881008282792204417)
      ·
        refine ⟨1496151660756212094153313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1994868881008282792204417 1496151660756212094153313)
        ·
          refine ⟨1122113745567159070614985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496151660756212094153313 1122113745567159070614985)
          ·
            refine ⟨841585309175369302961239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1122113745567159070614985 841585309175369302961239)
            ·
              refine ⟨1262377963763053954441859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841585309175369302961239 1262377963763053954441859)
              ·
                refine ⟨1893566945644580931662789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262377963763053954441859 1893566945644580931662789)
                ·
                  refine ⟨355043802308358924686773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893566945644580931662789 355043802308358924686773)
                  ·
                    rfl

theorem cell20_777876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_777876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777876 prefixEnd_777876 := by exact prefixLift 777876
  have htrace : WordTrace (prefixWord ++ tailWord_777876) baseStart_777876 baseEnd_777876 := by
    simpa [prefixWord, tailWord_777876, baseEnd_777876] using wordTrace_append hprefix tailTrace_777876
  have hstable : (prefixWord ++ tailWord_777876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777876).length < 2 ^ (prefixWord ++ tailWord_777876).sum := by decide
  have hdescent : baseEnd_777876 < baseStart_777876 := by decide
  rcases family_descends (prefixWord ++ tailWord_777876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777880 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_777880 : Nat := 118140960795 + 777880 * 2 ^ 59
def prefixEnd_777880 : Nat := 4983230072969 + 3 ^ 40 * 777880 * 2
def baseEnd_777880 : Nat := 355045628017352688553423

theorem tailTrace_777880 : CollatzResearch.WordTrace tailWord_777880 prefixEnd_777880 355045628017352688553423 := by
  unfold tailWord_777880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185807210940543086137547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18914409614587390781516729 14185807210940543086137547)
  ·
    refine ⟨21278710816410814629206321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14185807210940543086137547 21278710816410814629206321)
    ·
      refine ⟨15959033112308110971904741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21278710816410814629206321 15959033112308110971904741)
      ·
        refine ⟨2992318708557770807232139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15959033112308110971904741 2992318708557770807232139)
        ·
          refine ⟨4488478062836656210848209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992318708557770807232139 4488478062836656210848209)
          ·
            refine ⟨3366358547127492158136157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4488478062836656210848209 3366358547127492158136157)
            ·
              refine ⟨1262384455172809559301059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3366358547127492158136157 1262384455172809559301059)
              ·
                refine ⟨1893576682759214338951589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262384455172809559301059 1893576682759214338951589)
                ·
                  refine ⟨355045628017352688553423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893576682759214338951589 355045628017352688553423)
                  ·
                    rfl

theorem cell20_777880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_777880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777880 prefixEnd_777880 := by exact prefixLift 777880
  have htrace : WordTrace (prefixWord ++ tailWord_777880) baseStart_777880 baseEnd_777880 := by
    simpa [prefixWord, tailWord_777880, baseEnd_777880] using wordTrace_append hprefix tailTrace_777880
  have hstable : (prefixWord ++ tailWord_777880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777880).length < 2 ^ (prefixWord ++ tailWord_777880).sum := by decide
  have hdescent : baseEnd_777880 < baseStart_777880 := by decide
  rcases family_descends (prefixWord ++ tailWord_777880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777915 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_777915 : Nat := 118140960795 + 777915 * 2 ^ 59
def prefixEnd_777915 : Nat := 4983230072969 + 3 ^ 40 * 777915 * 2
def baseEnd_777915 : Nat := 355061602971048122386613

theorem tailTrace_777915 : CollatzResearch.WordTrace tailWord_777915 prefixEnd_777915 355061602971048122386613 := by
  unfold tailWord_777915
  simp only [CollatzResearch.WordTrace]
  refine ⟨28372890976754287149799199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18915260651169524766532799 28372890976754287149799199)
  ·
    refine ⟨42559336465131430724698799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28372890976754287149799199 42559336465131430724698799)
    ·
      refine ⟨63839004697697146087048199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42559336465131430724698799 63839004697697146087048199)
      ·
        refine ⟨95758507046545719130572299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63839004697697146087048199 95758507046545719130572299)
        ·
          refine ⟨143637760569818578695858449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95758507046545719130572299 143637760569818578695858449)
          ·
            refine ⟨107728320427363934021893837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143637760569818578695858449 107728320427363934021893837)
            ·
              refine ⟨40398120160261475258210189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107728320427363934021893837 40398120160261475258210189)
              ·
                refine ⟨15149295060098053221828821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40398120160261475258210189 15149295060098053221828821)
                ·
                  refine ⟨355061602971048122386613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15149295060098053221828821 355061602971048122386613)
                  ·
                    rfl

theorem cell20_777915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_777915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777915 prefixEnd_777915 := by exact prefixLift 777915
  have htrace : WordTrace (prefixWord ++ tailWord_777915) baseStart_777915 baseEnd_777915 := by
    simpa [prefixWord, tailWord_777915, baseEnd_777915] using wordTrace_append hprefix tailTrace_777915
  have hstable : (prefixWord ++ tailWord_777915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777915).length < 2 ^ (prefixWord ++ tailWord_777915).sum := by decide
  have hdescent : baseEnd_777915 < baseStart_777915 := by decide
  rcases family_descends (prefixWord ++ tailWord_777915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777959 : List Nat := [1, 1, 5, 4, 1, 1, 3, 4]
def baseStart_777959 : Nat := 118140960795 + 777959 * 2 ^ 59
def prefixEnd_777959 : Nat := 4983230072969 + 3 ^ 40 * 777959 * 2
def baseEnd_777959 : Nat := 118360561923326508306589

theorem tailTrace_777959 : CollatzResearch.WordTrace tailWord_777959 prefixEnd_777959 118360561923326508306589 := by
  unfold tailWord_777959
  simp only [CollatzResearch.WordTrace]
  refine ⟨28374495788594882664400931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18916330525729921776267287 28374495788594882664400931)
  ·
    refine ⟨42561743682892323996601397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28374495788594882664400931 42561743682892323996601397)
    ·
      refine ⟨3990163470271155374681381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42561743682892323996601397 3990163470271155374681381)
      ·
        refine ⟨748155650675841632752759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3990163470271155374681381 748155650675841632752759)
        ·
          refine ⟨1122233476013762449129139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748155650675841632752759 1122233476013762449129139)
          ·
            refine ⟨1683350214020643673693709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122233476013762449129139 1683350214020643673693709)
            ·
              refine ⟨631256330257741377635141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683350214020643673693709 631256330257741377635141)
              ·
                refine ⟨118360561923326508306589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 631256330257741377635141 118360561923326508306589)
                ·
                  rfl

theorem cell20_777959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_777959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777959 prefixEnd_777959 := by exact prefixLift 777959
  have htrace : WordTrace (prefixWord ++ tailWord_777959) baseStart_777959 baseEnd_777959 := by
    simpa [prefixWord, tailWord_777959, baseEnd_777959] using wordTrace_append hprefix tailTrace_777959
  have hstable : (prefixWord ++ tailWord_777959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777959).length < 2 ^ (prefixWord ++ tailWord_777959).sum := by decide
  have hdescent : baseEnd_777959 < baseStart_777959 := by decide
  rcases family_descends (prefixWord ++ tailWord_777959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777970 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_777970 : Nat := 118140960795 + 777970 * 2 ^ 59
def prefixEnd_777970 : Nat := 4983230072969 + 3 ^ 40 * 777970 * 2
def baseEnd_777970 : Nat := 355086706469712375553055

theorem tailTrace_777970 : CollatzResearch.WordTrace tailWord_777970 prefixEnd_777970 355086706469712375553055 := by
  unfold tailWord_777970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093724247888757885762841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18916597994370021028700909 7093724247888757885762841)
  ·
    refine ⟨5320293185916568414322131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7093724247888757885762841 5320293185916568414322131)
    ·
      refine ⟨7980439778874852621483197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5320293185916568414322131 7980439778874852621483197)
      ·
        refine ⟨2992664917078069733056199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7980439778874852621483197 2992664917078069733056199)
        ·
          refine ⟨4488997375617104599584299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992664917078069733056199 4488997375617104599584299)
          ·
            refine ⟨6733496063425656899376449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4488997375617104599584299 6733496063425656899376449)
            ·
              refine ⟨5050122047569242674532337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6733496063425656899376449 5050122047569242674532337)
              ·
                refine ⟨3787591535676932005899253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5050122047569242674532337 3787591535676932005899253)
                ·
                  refine ⟨355086706469712375553055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3787591535676932005899253 355086706469712375553055)
                  ·
                    rfl

theorem cell20_777970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_777970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777970 prefixEnd_777970 := by exact prefixLift 777970
  have htrace : WordTrace (prefixWord ++ tailWord_777970) baseStart_777970 baseEnd_777970 := by
    simpa [prefixWord, tailWord_777970, baseEnd_777970] using wordTrace_append hprefix tailTrace_777970
  have hstable : (prefixWord ++ tailWord_777970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777970).length < 2 ^ (prefixWord ++ tailWord_777970).sum := by decide
  have hdescent : baseEnd_777970 < baseStart_777970 := by decide
  rcases family_descends (prefixWord ++ tailWord_777970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777994 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_777994 : Nat := 118140960795 + 777994 * 2 ^ 59
def prefixEnd_777994 : Nat := 4983230072969 + 3 ^ 40 * 777994 * 2
def baseEnd_777994 : Nat := 355097660723674958752957

theorem tailTrace_777994 : CollatzResearch.WordTrace tailWord_777994 prefixEnd_777994 355097660723674958752957 := by
  unfold tailWord_777994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093943085867020910481259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18917181562312055761283357 7093943085867020910481259)
  ·
    refine ⟨10640914628800531365721889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7093943085867020910481259 10640914628800531365721889)
    ·
      refine ⟨7980685971600398524291417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10640914628800531365721889 7980685971600398524291417)
      ·
        refine ⟨5985514478700298893218563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7980685971600398524291417 5985514478700298893218563)
        ·
          refine ⟨8978271718050448339827845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985514478700298893218563 8978271718050448339827845)
          ·
            refine ⟨1683425947134459063717721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8978271718050448339827845 1683425947134459063717721)
            ·
              refine ⟨1262569460350844297788291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683425947134459063717721 1262569460350844297788291)
              ·
                refine ⟨1893854190526266446682437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262569460350844297788291 1893854190526266446682437)
                ·
                  refine ⟨355097660723674958752957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893854190526266446682437 355097660723674958752957)
                  ·
                    rfl

theorem cell20_777994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_777994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_777994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_777994 prefixEnd_777994 := by exact prefixLift 777994
  have htrace : WordTrace (prefixWord ++ tailWord_777994) baseStart_777994 baseEnd_777994 := by
    simpa [prefixWord, tailWord_777994, baseEnd_777994] using wordTrace_append hprefix tailTrace_777994
  have hstable : (prefixWord ++ tailWord_777994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777994).length < 2 ^ (prefixWord ++ tailWord_777994).sum := by decide
  have hdescent : baseEnd_777994 < baseStart_777994 := by decide
  rcases family_descends (prefixWord ++ tailWord_777994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778008 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_778008 : Nat := 118140960795 + 778008 * 2 ^ 59
def prefixEnd_778008 : Nat := 4983230072969 + 3 ^ 40 * 778008 * 2
def baseEnd_778008 : Nat := 355104050705153132286233

theorem tailTrace_778008 : CollatzResearch.WordTrace tailWord_778008 prefixEnd_778008 355104050705153132286233 := by
  unfold tailWord_778008
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188141482708682016467339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18917521976944909355289785 14188141482708682016467339)
  ·
    refine ⟨21282212224063023024701009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14188141482708682016467339 21282212224063023024701009)
    ·
      refine ⟨15961659168047267268525757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21282212224063023024701009 15961659168047267268525757)
      ·
        refine ⟨5985622188017725225697159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15961659168047267268525757 5985622188017725225697159)
        ·
          refine ⟨8978433282026587838545739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985622188017725225697159 8978433282026587838545739)
          ·
            refine ⟨13467649923039881757818609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978433282026587838545739 13467649923039881757818609)
            ·
              refine ⟨10100737442279911318363957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13467649923039881757818609 10100737442279911318363957)
              ·
                refine ⟨946944135213741686096621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10100737442279911318363957 946944135213741686096621)
                ·
                  refine ⟨355104050705153132286233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 946944135213741686096621 355104050705153132286233)
                  ·
                    rfl

theorem cell20_778008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_778008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778008 prefixEnd_778008 := by exact prefixLift 778008
  have htrace : WordTrace (prefixWord ++ tailWord_778008) baseStart_778008 baseEnd_778008 := by
    simpa [prefixWord, tailWord_778008, baseEnd_778008] using wordTrace_append hprefix tailTrace_778008
  have hstable : (prefixWord ++ tailWord_778008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778008).length < 2 ^ (prefixWord ++ tailWord_778008).sum := by decide
  have hdescent : baseEnd_778008 < baseStart_778008 := by decide
  rcases family_descends (prefixWord ++ tailWord_778008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778015 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_778015 : Nat := 118140960795 + 778015 * 2 ^ 59
def prefixEnd_778015 : Nat := 4983230072969 + 3 ^ 40 * 778015 * 2
def baseEnd_778015 : Nat := 355107245695892219052871

theorem tailTrace_778015 : CollatzResearch.WordTrace tailWord_778015 prefixEnd_778015 355107245695892219052871 := by
  unfold tailWord_778015
  simp only [CollatzResearch.WordTrace]
  refine ⟨28376538276392004228439499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18917692184261336152292999 28376538276392004228439499)
  ·
    refine ⟨42564807414588006342659249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28376538276392004228439499 42564807414588006342659249)
    ·
      refine ⟨31923605560941004756994437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42564807414588006342659249 31923605560941004756994437)
      ·
        refine ⟨5985676042676438391936457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31923605560941004756994437 5985676042676438391936457)
        ·
          refine ⟨4489257032007328793952343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5985676042676438391936457 4489257032007328793952343)
          ·
            refine ⟨6733885548010993190928515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489257032007328793952343 6733885548010993190928515)
            ·
              refine ⟨10100828322016489786392773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733885548010993190928515 10100828322016489786392773)
              ·
                refine ⟨1893905310378091834948645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10100828322016489786392773 1893905310378091834948645)
                ·
                  refine ⟨355107245695892219052871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893905310378091834948645 355107245695892219052871)
                  ·
                    rfl

theorem cell20_778015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_778015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778015 prefixEnd_778015 := by exact prefixLift 778015
  have htrace : WordTrace (prefixWord ++ tailWord_778015) baseStart_778015 baseEnd_778015 := by
    simpa [prefixWord, tailWord_778015, baseEnd_778015] using wordTrace_append hprefix tailTrace_778015
  have hstable : (prefixWord ++ tailWord_778015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778015).length < 2 ^ (prefixWord ++ tailWord_778015).sum := by decide
  have hdescent : baseEnd_778015 < baseStart_778015 := by decide
  rcases family_descends (prefixWord ++ tailWord_778015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778101 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_778101 : Nat := 118140960795 + 778101 * 2 ^ 59
def prefixEnd_778101 : Nat := 4983230072969 + 3 ^ 40 * 778101 * 2
def baseEnd_778101 : Nat := 355146498439258142185853

theorem tailTrace_778101 : CollatzResearch.WordTrace tailWord_778101 prefixEnd_778101 355146498439258142185853 := by
  unfold tailWord_778101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28379674954080440916070157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18919783302720293944046771 28379674954080440916070157)
  ·
    refine ⟨10642378107780165343526309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28379674954080440916070157 10642378107780165343526309)
    ·
      refine ⟨1995445895208781001911183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10642378107780165343526309 1995445895208781001911183)
      ·
        refine ⟨2993168842813171502866775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995445895208781001911183 2993168842813171502866775)
        ·
          refine ⟨4489753264219757254300163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993168842813171502866775 4489753264219757254300163)
          ·
            refine ⟨6734629896329635881450245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489753264219757254300163 6734629896329635881450245)
            ·
              refine ⟨1262743105561806727771921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6734629896329635881450245 1262743105561806727771921)
              ·
                refine ⟨947057329171355045828941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262743105561806727771921 947057329171355045828941)
                ·
                  refine ⟨355146498439258142185853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947057329171355045828941 355146498439258142185853)
                  ·
                    rfl

theorem cell20_778101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_778101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778101 prefixEnd_778101 := by exact prefixLift 778101
  have htrace : WordTrace (prefixWord ++ tailWord_778101) baseStart_778101 baseEnd_778101 := by
    simpa [prefixWord, tailWord_778101, baseEnd_778101] using wordTrace_append hprefix tailTrace_778101
  have hstable : (prefixWord ++ tailWord_778101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778101).length < 2 ^ (prefixWord ++ tailWord_778101).sum := by decide
  have hdescent : baseEnd_778101 < baseStart_778101 := by decide
  rcases family_descends (prefixWord ++ tailWord_778101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778115 : List Nat := [1, 1, 1, 3, 4, 4, 1, 5]
def baseStart_778115 : Nat := 118140960795 + 778115 * 2 ^ 59
def prefixEnd_778115 : Nat := 4983230072969 + 3 ^ 40 * 778115 * 2
def baseEnd_778115 : Nat := 118384296140245438573043

theorem tailTrace_778115 : CollatzResearch.WordTrace tailWord_778115 prefixEnd_778115 118384296140245438573043 := by
  unfold tailWord_778115
  simp only [CollatzResearch.WordTrace]
  refine ⟨28380185576029721307079799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18920123717353147538053199 28380185576029721307079799)
  ·
    refine ⟨42570278364044581960619699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28380185576029721307079799 42570278364044581960619699)
    ·
      refine ⟨63855417546066872940929549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42570278364044581960619699 63855417546066872940929549)
      ·
        refine ⟨23945781579775077352848581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63855417546066872940929549 23945781579775077352848581)
        ·
          refine ⟨4489834046207827003659109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23945781579775077352848581 4489834046207827003659109)
          ·
            refine ⟨841843883663967563186083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4489834046207827003659109 841843883663967563186083)
            ·
              refine ⟨1262765825495951344779125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841843883663967563186083 1262765825495951344779125)
              ·
                refine ⟨118384296140245438573043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1262765825495951344779125 118384296140245438573043)
                ·
                  rfl

theorem cell20_778115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_778115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778115 prefixEnd_778115 := by exact prefixLift 778115
  have htrace : WordTrace (prefixWord ++ tailWord_778115) baseStart_778115 baseEnd_778115 := by
    simpa [prefixWord, tailWord_778115, baseEnd_778115] using wordTrace_append hprefix tailTrace_778115
  have hstable : (prefixWord ++ tailWord_778115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778115).length < 2 ^ (prefixWord ++ tailWord_778115).sum := by decide
  have hdescent : baseEnd_778115 < baseStart_778115 := by decide
  rcases family_descends (prefixWord ++ tailWord_778115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778132 : List Nat := [2, 4, 2, 1, 1, 3, 3, 4]
def baseStart_778132 : Nat := 118140960795 + 778132 * 2 ^ 59
def prefixEnd_778132 : Nat := 4983230072969 + 3 ^ 40 * 778132 * 2
def baseEnd_778132 : Nat := 118386882561319937384131

theorem tailTrace_778132 : CollatzResearch.WordTrace tailWord_778132 prefixEnd_778132 118386882561319937384131 := by
  unfold tailWord_778132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190402808484066605224325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18920537077978755473632433 14190402808484066605224325)
  ·
    refine ⟨2660700526590762488479561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14190402808484066605224325 2660700526590762488479561)
    ·
      refine ⟨1995525394943071866359671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2660700526590762488479561 1995525394943071866359671)
      ·
        refine ⟨2993288092414607799539507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995525394943071866359671 2993288092414607799539507)
        ·
          refine ⟨4489932138621911699309261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993288092414607799539507 4489932138621911699309261)
          ·
            refine ⟨1683724551983216887240973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4489932138621911699309261 1683724551983216887240973)
            ·
              refine ⟨631396706993706332715365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683724551983216887240973 631396706993706332715365)
              ·
                refine ⟨118386882561319937384131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 631396706993706332715365 118386882561319937384131)
                ·
                  rfl

theorem cell20_778132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_778132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778132 prefixEnd_778132 := by exact prefixLift 778132
  have htrace : WordTrace (prefixWord ++ tailWord_778132) baseStart_778132 baseEnd_778132 := by
    simpa [prefixWord, tailWord_778132, baseEnd_778132] using wordTrace_append hprefix tailTrace_778132
  have hstable : (prefixWord ++ tailWord_778132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778132).length < 2 ^ (prefixWord ++ tailWord_778132).sum := by decide
  have hdescent : baseEnd_778132 < baseStart_778132 := by decide
  rcases family_descends (prefixWord ++ tailWord_778132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778152 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 3]
def baseStart_778152 : Nat := 118140960795 + 778152 * 2 ^ 59
def prefixEnd_778152 : Nat := 4983230072969 + 3 ^ 40 * 778152 * 2
def baseEnd_778152 : Nat := 355169776228928631485645

theorem tailTrace_778152 : CollatzResearch.WordTrace tailWord_778152 prefixEnd_778152 355169776228928631485645 := by
  unfold tailWord_778152
  simp only [CollatzResearch.WordTrace]
  refine ⟨14190767538447838313088355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18921023384597117750784473 14190767538447838313088355)
  ·
    refine ⟨21286151307671757469632533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14190767538447838313088355 21286151307671757469632533)
    ·
      refine ⟨997788342547113631389025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21286151307671757469632533 997788342547113631389025)
      ·
        refine ⟨748341256910335223541769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 997788342547113631389025 748341256910335223541769)
        ·
          refine ⟨561255942682751417656327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748341256910335223541769 561255942682751417656327)
          ·
            refine ⟨841883914024127126484491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561255942682751417656327 841883914024127126484491)
            ·
              refine ⟨1262825871036190689726737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841883914024127126484491 1262825871036190689726737)
              ·
                refine ⟨947119403277143017295053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262825871036190689726737 947119403277143017295053)
                ·
                  refine ⟨355169776228928631485645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947119403277143017295053 355169776228928631485645)
                  ·
                    rfl

theorem cell20_778152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_778152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778152 prefixEnd_778152 := by exact prefixLift 778152
  have htrace : WordTrace (prefixWord ++ tailWord_778152) baseStart_778152 baseEnd_778152 := by
    simpa [prefixWord, tailWord_778152, baseEnd_778152] using wordTrace_append hprefix tailTrace_778152
  have hstable : (prefixWord ++ tailWord_778152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778152).length < 2 ^ (prefixWord ++ tailWord_778152).sum := by decide
  have hdescent : baseEnd_778152 < baseStart_778152 := by decide
  rcases family_descends (prefixWord ++ tailWord_778152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778204 : List Nat := [2, 2, 6, 1, 2, 1, 6]
def baseStart_778204 : Nat := 118140960795 + 778204 * 2 ^ 59
def prefixEnd_778204 : Nat := 4983230072969 + 3 ^ 40 * 778204 * 2
def baseEnd_778204 : Nat := 39465945605094173528011

theorem tailTrace_778204 : CollatzResearch.WordTrace tailWord_778204 prefixEnd_778204 39465945605094173528011 := by
  unfold tailWord_778204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14191715836353644753534833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18922287781804859671379777 14191715836353644753534833)
  ·
    refine ⟨10643786877265233565151125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14191715836353644753534833 10643786877265233565151125)
    ·
      refine ⟨498927509871807823366459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10643786877265233565151125 498927509871807823366459)
      ·
        refine ⟨748391264807711735049689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498927509871807823366459 748391264807711735049689)
        ·
          refine ⟨561293448605783801287267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748391264807711735049689 561293448605783801287267)
          ·
            refine ⟨841940172908675701930901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561293448605783801287267 841940172908675701930901)
            ·
              refine ⟨39465945605094173528011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 841940172908675701930901 39465945605094173528011)
              ·
                rfl

theorem cell20_778204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 6].length) (baseStart_778204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778204 prefixEnd_778204 := by exact prefixLift 778204
  have htrace : WordTrace (prefixWord ++ tailWord_778204) baseStart_778204 baseEnd_778204 := by
    simpa [prefixWord, tailWord_778204, baseEnd_778204] using wordTrace_append hprefix tailTrace_778204
  have hstable : (prefixWord ++ tailWord_778204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778204).length < 2 ^ (prefixWord ++ tailWord_778204).sum := by decide
  have hdescent : baseEnd_778204 < baseStart_778204 := by decide
  rcases family_descends (prefixWord ++ tailWord_778204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778222 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_778222 : Nat := 118140960795 + 778222 * 2 ^ 59
def prefixEnd_778222 : Nat := 4983230072969 + 3 ^ 40 * 778222 * 2
def baseEnd_778222 : Nat := 355201726136319499152025

theorem tailTrace_778222 : CollatzResearch.WordTrace tailWord_778222 prefixEnd_778222 355201726136319499152025 := by
  unfold tailWord_778222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548011023330259822653115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18922725457761385720816613 3548011023330259822653115)
  ·
    refine ⟨5322016534995389733979673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3548011023330259822653115 5322016534995389733979673)
    ·
      refine ⟨3991512401246542300484755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5322016534995389733979673 3991512401246542300484755)
      ·
        refine ⟨5987268601869813450727133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991512401246542300484755 5987268601869813450727133)
        ·
          refine ⟨2245225725701180044022675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5987268601869813450727133 2245225725701180044022675)
          ·
            refine ⟨3367838588551770066034013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245225725701180044022675 3367838588551770066034013)
            ·
              refine ⟨1262939470706913774762755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3367838588551770066034013 1262939470706913774762755)
              ·
                refine ⟨1894409206060370662144133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262939470706913774762755 1894409206060370662144133)
                ·
                  refine ⟨355201726136319499152025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894409206060370662144133 355201726136319499152025)
                  ·
                    rfl

theorem cell20_778222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_778222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778222 prefixEnd_778222 := by exact prefixLift 778222
  have htrace : WordTrace (prefixWord ++ tailWord_778222) baseStart_778222 baseEnd_778222 := by
    simpa [prefixWord, tailWord_778222, baseEnd_778222] using wordTrace_append hprefix tailTrace_778222
  have hstable : (prefixWord ++ tailWord_778222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778222).length < 2 ^ (prefixWord ++ tailWord_778222).sum := by decide
  have hdescent : baseEnd_778222 < baseStart_778222 := by decide
  rcases family_descends (prefixWord ++ tailWord_778222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778236 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_778236 : Nat := 118140960795 + 778236 * 2 ^ 59
def prefixEnd_778236 : Nat := 4983230072969 + 3 ^ 40 * 778236 * 2
def baseEnd_778236 : Nat := 355208116117797672685301

theorem tailTrace_778236 : CollatzResearch.WordTrace tailWord_778236 prefixEnd_778236 355208116117797672685301 := by
  unfold tailWord_778236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192299404295679486117281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18923065872394239314823041 14192299404295679486117281)
  ·
    refine ⟨10644224553221759614587961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14192299404295679486117281 10644224553221759614587961)
    ·
      refine ⟨7983168414916319710940971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10644224553221759614587961 7983168414916319710940971)
      ·
        refine ⟨11974752622374479566411457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7983168414916319710940971 11974752622374479566411457)
        ·
          refine ⟨8981064466780859674808593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11974752622374479566411457 8981064466780859674808593)
          ·
            refine ⟨6735798350085644756106445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8981064466780859674808593 6735798350085644756106445)
            ·
              refine ⟨2525924381282116783539917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6735798350085644756106445 2525924381282116783539917)
              ·
                refine ⟨947221642980793793827469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2525924381282116783539917 947221642980793793827469)
                ·
                  refine ⟨355208116117797672685301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947221642980793793827469 355208116117797672685301)
                  ·
                    rfl

theorem cell20_778236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_778236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778236 prefixEnd_778236 := by exact prefixLift 778236
  have htrace : WordTrace (prefixWord ++ tailWord_778236) baseStart_778236 baseEnd_778236 := by
    simpa [prefixWord, tailWord_778236, baseEnd_778236] using wordTrace_append hprefix tailTrace_778236
  have hstable : (prefixWord ++ tailWord_778236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778236).length < 2 ^ (prefixWord ++ tailWord_778236).sum := by decide
  have hdescent : baseEnd_778236 < baseStart_778236 := by decide
  rcases family_descends (prefixWord ++ tailWord_778236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778273 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 2]
def baseStart_778273 : Nat := 118140960795 + 778273 * 2 ^ 59
def prefixEnd_778273 : Nat := 4983230072969 + 3 ^ 40 * 778273 * 2
def baseEnd_778273 : Nat := 355225003925989988451817

theorem tailTrace_778273 : CollatzResearch.WordTrace tailWord_778273 prefixEnd_778273 355225003925989988451817 := by
  unfold tailWord_778273
  simp only [CollatzResearch.WordTrace]
  refine ⟨28385948309457314291331473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18923965539638209527554315 28385948309457314291331473)
  ·
    refine ⟨21289461232092985718498605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28385948309457314291331473 21289461232092985718498605)
    ·
      refine ⟨7983547962034869644436977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21289461232092985718498605 7983547962034869644436977)
      ·
        refine ⟨5987660971526152233327733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7983547962034869644436977 5987660971526152233327733)
        ·
          refine ⟨561343216080576771874475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5987660971526152233327733 561343216080576771874475)
          ·
            refine ⟨842014824120865157811713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561343216080576771874475 842014824120865157811713)
            ·
              refine ⟨631511118090648868358785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842014824120865157811713 631511118090648868358785)
              ·
                refine ⟨473633338567986651269089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631511118090648868358785 473633338567986651269089)
                ·
                  refine ⟨355225003925989988451817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473633338567986651269089 355225003925989988451817)
                  ·
                    rfl

theorem cell20_778273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_778273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778273 prefixEnd_778273 := by exact prefixLift 778273
  have htrace : WordTrace (prefixWord ++ tailWord_778273) baseStart_778273 baseEnd_778273 := by
    simpa [prefixWord, tailWord_778273, baseEnd_778273] using wordTrace_append hprefix tailTrace_778273
  have hstable : (prefixWord ++ tailWord_778273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778273).length < 2 ^ (prefixWord ++ tailWord_778273).sum := by decide
  have hdescent : baseEnd_778273 < baseStart_778273 := by decide
  rcases family_descends (prefixWord ++ tailWord_778273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778277 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 2]
def baseStart_778277 : Nat := 118140960795 + 778277 * 2 ^ 59
def prefixEnd_778277 : Nat := 4983230072969 + 3 ^ 40 * 778277 * 2
def baseEnd_778277 : Nat := 355226829634983752318467

theorem tailTrace_778277 : CollatzResearch.WordTrace tailWord_778277 prefixEnd_778277 355226829634983752318467 := by
  unfold tailWord_778277
  simp only [CollatzResearch.WordTrace]
  refine ⟨28386094201442822974477085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18924062800961881982984723 28386094201442822974477085)
  ·
    refine ⟨10644785325541058615428907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28386094201442822974477085 10644785325541058615428907)
    ·
      refine ⟨15967177988311587923143361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644785325541058615428907 15967177988311587923143361)
      ·
        refine ⟨11975383491233690942357521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15967177988311587923143361 11975383491233690942357521)
        ·
          refine ⟨8981537618425268206768141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11975383491233690942357521 8981537618425268206768141)
          ·
            refine ⟨3368076606909475577538053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8981537618425268206768141 3368076606909475577538053)
            ·
              refine ⟨631514363795526670788385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3368076606909475577538053 631514363795526670788385)
              ·
                refine ⟨473635772846645003091289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631514363795526670788385 473635772846645003091289)
                ·
                  refine ⟨355226829634983752318467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473635772846645003091289 355226829634983752318467)
                  ·
                    rfl

theorem cell20_778277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_778277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778277 prefixEnd_778277 := by exact prefixLift 778277
  have htrace : WordTrace (prefixWord ++ tailWord_778277) baseStart_778277 baseEnd_778277 := by
    simpa [prefixWord, tailWord_778277, baseEnd_778277] using wordTrace_append hprefix tailTrace_778277
  have hstable : (prefixWord ++ tailWord_778277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778277).length < 2 ^ (prefixWord ++ tailWord_778277).sum := by decide
  have hdescent : baseEnd_778277 < baseStart_778277 := by decide
  rcases family_descends (prefixWord ++ tailWord_778277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778288 : List Nat := [2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_778288 : Nat := 118140960795 + 778288 * 2 ^ 59
def prefixEnd_778288 : Nat := 4983230072969 + 3 ^ 40 * 778288 * 2
def baseEnd_778288 : Nat := 118410616778238867650585

theorem tailTrace_778288 : CollatzResearch.WordTrace tailWord_778288 prefixEnd_778288 118410616778238867650585 := by
  unfold tailWord_778288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193247702201485926563759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18924330269601981235418345 14193247702201485926563759)
  ·
    refine ⟨21289871553302228889845639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14193247702201485926563759 21289871553302228889845639)
    ·
      refine ⟨31934807329953343334768459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21289871553302228889845639 31934807329953343334768459)
      ·
        refine ⟨47902210994930015002152689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31934807329953343334768459 47902210994930015002152689)
        ·
          refine ⟨35926658246197511251614517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47902210994930015002152689 35926658246197511251614517)
          ·
            refine ⟨3368124210581016679838861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35926658246197511251614517 3368124210581016679838861)
            ·
              refine ⟨1263046578967881254939573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3368124210581016679838861 1263046578967881254939573)
              ·
                refine ⟨118410616778238867650585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1263046578967881254939573 118410616778238867650585)
                ·
                  rfl

theorem cell20_778288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_778288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778288 prefixEnd_778288 := by exact prefixLift 778288
  have htrace : WordTrace (prefixWord ++ tailWord_778288) baseStart_778288 baseEnd_778288 := by
    simpa [prefixWord, tailWord_778288, baseEnd_778288] using wordTrace_append hprefix tailTrace_778288
  have hstable : (prefixWord ++ tailWord_778288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778288).length < 2 ^ (prefixWord ++ tailWord_778288).sum := by decide
  have hdescent : baseEnd_778288 < baseStart_778288 := by decide
  rcases family_descends (prefixWord ++ tailWord_778288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778336 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 2]
def baseStart_778336 : Nat := 118140960795 + 778336 * 2 ^ 59
def prefixEnd_778336 : Nat := 4983230072969 + 3 ^ 40 * 778336 * 2
def baseEnd_778336 : Nat := 355253758842641769351559

theorem tailTrace_778336 : CollatzResearch.WordTrace tailWord_778336 prefixEnd_778336 355253758842641769351559 := by
  unfold tailWord_778336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194123054114538025437431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18925497405486050700583241 14194123054114538025437431)
  ·
    refine ⟨21291184581171807038156147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14194123054114538025437431 21291184581171807038156147)
    ·
      refine ⟨31936776871757710557234221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21291184581171807038156147 31936776871757710557234221)
      ·
        refine ⟨11976291326909141458962833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31936776871757710557234221 11976291326909141458962833)
        ·
          refine ⟨8982218495181856094222125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11976291326909141458962833 8982218495181856094222125)
          ·
            refine ⟨3368331935693196035333297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8982218495181856094222125 3368331935693196035333297)
            ·
              refine ⟨2526248951769897026499973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368331935693196035333297 2526248951769897026499973)
              ·
                refine ⟨473671678456855692468745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2526248951769897026499973 473671678456855692468745)
                ·
                  refine ⟨355253758842641769351559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473671678456855692468745 355253758842641769351559)
                  ·
                    rfl

theorem cell20_778336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_778336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778336 prefixEnd_778336 := by exact prefixLift 778336
  have htrace : WordTrace (prefixWord ++ tailWord_778336) baseStart_778336 baseEnd_778336 := by
    simpa [prefixWord, tailWord_778336, baseEnd_778336] using wordTrace_append hprefix tailTrace_778336
  have hstable : (prefixWord ++ tailWord_778336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778336).length < 2 ^ (prefixWord ++ tailWord_778336).sum := by decide
  have hdescent : baseEnd_778336 < baseStart_778336 := by decide
  rcases family_descends (prefixWord ++ tailWord_778336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778346 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_778346 : Nat := 118140960795 + 778346 * 2 ^ 59
def prefixEnd_778346 : Nat := 4983230072969 + 3 ^ 40 * 778346 * 2
def baseEnd_778346 : Nat := 355258323115126179018185

theorem tailTrace_778346 : CollatzResearch.WordTrace tailWord_778346 prefixEnd_778346 355258323115126179018185 := by
  unfold tailWord_778346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097152709548211939684723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18925740558795231839159261 7097152709548211939684723)
  ·
    refine ⟨10645729064322317909527085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7097152709548211939684723 10645729064322317909527085)
    ·
      refine ⟨3992148399120869216072657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10645729064322317909527085 3992148399120869216072657)
      ·
        refine ⟨2994111299340651912054493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3992148399120869216072657 2994111299340651912054493)
        ·
          refine ⟨1122791737252744467020435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2994111299340651912054493 1122791737252744467020435)
          ·
            refine ⟨1684187605879116700530653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122791737252744467020435 1684187605879116700530653)
            ·
              refine ⟨631570352204668762698995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1684187605879116700530653 631570352204668762698995)
              ·
                refine ⟨947355528307003144048493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631570352204668762698995 947355528307003144048493)
                ·
                  refine ⟨355258323115126179018185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947355528307003144048493 355258323115126179018185)
                  ·
                    rfl

theorem cell20_778346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_778346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778346 prefixEnd_778346 := by exact prefixLift 778346
  have htrace : WordTrace (prefixWord ++ tailWord_778346) baseStart_778346 baseEnd_778346 := by
    simpa [prefixWord, tailWord_778346, baseEnd_778346] using wordTrace_append hprefix tailTrace_778346
  have hstable : (prefixWord ++ tailWord_778346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778346).length < 2 ^ (prefixWord ++ tailWord_778346).sum := by decide
  have hdescent : baseEnd_778346 < baseStart_778346 := by decide
  rcases family_descends (prefixWord ++ tailWord_778346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778364 : List Nat := [2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_778364 : Nat := 118140960795 + 778364 * 2 ^ 59
def prefixEnd_778364 : Nat := 4983230072969 + 3 ^ 40 * 778364 * 2
def baseEnd_778364 : Nat := 118422179601866038806037

theorem tailTrace_778364 : CollatzResearch.WordTrace tailWord_778364 prefixEnd_778364 118422179601866038806037 := by
  unfold tailWord_778364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194633676063818416447073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18926178234751757888596097 14194633676063818416447073)
  ·
    refine ⟨10645975257047863812335305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14194633676063818416447073 10645975257047863812335305)
    ·
      refine ⟨7984481442785897859251479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10645975257047863812335305 7984481442785897859251479)
      ·
        refine ⟨11976722164178846788877219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7984481442785897859251479 11976722164178846788877219)
        ·
          refine ⟨17965083246268270183315829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11976722164178846788877219 17965083246268270183315829)
          ·
            refine ⟨1684226554337650329685859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17965083246268270183315829 1684226554337650329685859)
            ·
              refine ⟨2526339831506475494528789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684226554337650329685859 2526339831506475494528789)
              ·
                refine ⟨118422179601866038806037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2526339831506475494528789 118422179601866038806037)
                ·
                  rfl

theorem cell20_778364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_778364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778364 prefixEnd_778364 := by exact prefixLift 778364
  have htrace : WordTrace (prefixWord ++ tailWord_778364) baseStart_778364 baseEnd_778364 := by
    simpa [prefixWord, tailWord_778364, baseEnd_778364] using wordTrace_append hprefix tailTrace_778364
  have hstable : (prefixWord ++ tailWord_778364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778364).length < 2 ^ (prefixWord ++ tailWord_778364).sum := by decide
  have hdescent : baseEnd_778364 < baseStart_778364 := by decide
  rcases family_descends (prefixWord ++ tailWord_778364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778371 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_778371 : Nat := 118140960795 + 778371 * 2 ^ 59
def prefixEnd_778371 : Nat := 4983230072969 + 3 ^ 40 * 778371 * 2
def baseEnd_778371 : Nat := 355269733796337203184749

theorem tailTrace_778371 : CollatzResearch.WordTrace tailWord_778371 prefixEnd_778371 355269733796337203184749 := by
  unfold tailWord_778371
  simp only [CollatzResearch.WordTrace]
  refine ⟨28389522663102277028398967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18926348442068184685599311 28389522663102277028398967)
  ·
    refine ⟨42584283994653415542598451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28389522663102277028398967 42584283994653415542598451)
    ·
      refine ⟨63876425991980123313897677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42584283994653415542598451 63876425991980123313897677)
      ·
        refine ⟨23953659746992546242711629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63876425991980123313897677 23953659746992546242711629)
        ·
          refine ⟨8982622405122204841016861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23953659746992546242711629 8982622405122204841016861)
          ·
            refine ⟨3368483401920826815381323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8982622405122204841016861 3368483401920826815381323)
            ·
              refine ⟨5052725102881240223071985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368483401920826815381323 5052725102881240223071985)
              ·
                refine ⟨3789543827160930167303989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052725102881240223071985 3789543827160930167303989)
                ·
                  refine ⟨355269733796337203184749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789543827160930167303989 355269733796337203184749)
                  ·
                    rfl

theorem cell20_778371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_778371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778371 prefixEnd_778371 := by exact prefixLift 778371
  have htrace : WordTrace (prefixWord ++ tailWord_778371) baseStart_778371 baseEnd_778371 := by
    simpa [prefixWord, tailWord_778371, baseEnd_778371] using wordTrace_append hprefix tailTrace_778371
  have hstable : (prefixWord ++ tailWord_778371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778371).length < 2 ^ (prefixWord ++ tailWord_778371).sum := by decide
  have hdescent : baseEnd_778371 < baseStart_778371 := by decide
  rcases family_descends (prefixWord ++ tailWord_778371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778391 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 4]
def baseStart_778391 : Nat := 118140960795 + 778391 * 2 ^ 59
def prefixEnd_778391 : Nat := 4983230072969 + 3 ^ 40 * 778391 * 2
def baseEnd_778391 : Nat := 355278862341306022518001

theorem tailTrace_778391 : CollatzResearch.WordTrace tailWord_778391 prefixEnd_778391 355278862341306022518001 := by
  unfold tailWord_778391
  simp only [CollatzResearch.WordTrace]
  refine ⟨28390252123029820444127027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18926834748686546962751351 28390252123029820444127027)
  ·
    refine ⟨42585378184544730666190541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28390252123029820444127027 42585378184544730666190541)
    ·
      refine ⟨15969516819204273999821453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42585378184544730666190541 15969516819204273999821453)
      ·
        refine ⟨5988568807201602749933045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15969516819204273999821453 5988568807201602749933045)
        ·
          refine ⟨561428325675150257806223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5988568807201602749933045 561428325675150257806223)
          ·
            refine ⟨842142488512725386709335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561428325675150257806223 842142488512725386709335)
            ·
              refine ⟨1263213732769088080064003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842142488512725386709335 1263213732769088080064003)
              ·
                refine ⟨1894820599153632120096005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263213732769088080064003 1894820599153632120096005)
                ·
                  refine ⟨355278862341306022518001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894820599153632120096005 355278862341306022518001)
                  ·
                    rfl

theorem cell20_778391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 4].length) (baseStart_778391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778391 prefixEnd_778391 := by exact prefixLift 778391
  have htrace : WordTrace (prefixWord ++ tailWord_778391) baseStart_778391 baseEnd_778391 := by
    simpa [prefixWord, tailWord_778391, baseEnd_778391] using wordTrace_append hprefix tailTrace_778391
  have hstable : (prefixWord ++ tailWord_778391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778391).length < 2 ^ (prefixWord ++ tailWord_778391).sum := by decide
  have hdescent : baseEnd_778391 < baseStart_778391 := by decide
  rcases family_descends (prefixWord ++ tailWord_778391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778398 : List Nat := [4, 3, 1, 1, 3, 1, 2, 5]
def baseStart_778398 : Nat := 118140960795 + 778398 * 2 ^ 59
def prefixEnd_778398 : Nat := 4983230072969 + 3 ^ 40 * 778398 * 2
def baseEnd_778398 : Nat := 118427352444015036428213

theorem tailTrace_778398 : CollatzResearch.WordTrace tailWord_778398 prefixEnd_778398 118427352444015036428213 := by
  unfold tailWord_778398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548813429250557579953981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18927004956002973759754565 3548813429250557579953981)
  ·
    refine ⟨1330805035968959092482743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3548813429250557579953981 1330805035968959092482743)
    ·
      refine ⟨1996207553953438638724115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330805035968959092482743 1996207553953438638724115)
      ·
        refine ⟨2994311330930157958086173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1996207553953438638724115 2994311330930157958086173)
        ·
          refine ⟨1122866749098809234282315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2994311330930157958086173 1122866749098809234282315)
          ·
            refine ⟨1684300123648213851423473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122866749098809234282315 1684300123648213851423473)
            ·
              refine ⟨1263225092736160388567605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684300123648213851423473 1263225092736160388567605)
              ·
                refine ⟨118427352444015036428213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1263225092736160388567605 118427352444015036428213)
                ·
                  rfl

theorem cell20_778398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_778398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778398 prefixEnd_778398 := by exact prefixLift 778398
  have htrace : WordTrace (prefixWord ++ tailWord_778398) baseStart_778398 baseEnd_778398 := by
    simpa [prefixWord, tailWord_778398, baseEnd_778398] using wordTrace_append hprefix tailTrace_778398
  have hstable : (prefixWord ++ tailWord_778398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778398).length < 2 ^ (prefixWord ++ tailWord_778398).sum := by decide
  have hdescent : baseEnd_778398 < baseStart_778398 := by decide
  rcases family_descends (prefixWord ++ tailWord_778398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778446 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_778446 : Nat := 118140960795 + 778446 * 2 ^ 59
def prefixEnd_778446 : Nat := 4983230072969 + 3 ^ 40 * 778446 * 2
def baseEnd_778446 : Nat := 355303965839970275684443

theorem tailTrace_778446 : CollatzResearch.WordTrace tailWord_778446 prefixEnd_778446 355303965839970275684443 := by
  unfold tailWord_778446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549032267228820604672399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18928172091887043224919461 3549032267228820604672399)
  ·
    refine ⟨5323548400843230907008599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3549032267228820604672399 5323548400843230907008599)
    ·
      refine ⟨7985322601264846360512899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5323548400843230907008599 7985322601264846360512899)
      ·
        refine ⟨11977983901897269540769349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985322601264846360512899 11977983901897269540769349)
        ·
          refine ⟨2245871981605738038894253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11977983901897269540769349 2245871981605738038894253)
          ·
            refine ⟨842201993102151764585345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2245871981605738038894253 842201993102151764585345)
            ·
              refine ⟨631651494826613823439009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842201993102151764585345 631651494826613823439009)
              ·
                refine ⟨473738621119960367579257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631651494826613823439009 473738621119960367579257)
                ·
                  refine ⟨355303965839970275684443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473738621119960367579257 355303965839970275684443)
                  ·
                    rfl

theorem cell20_778446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_778446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778446 prefixEnd_778446 := by exact prefixLift 778446
  have htrace : WordTrace (prefixWord ++ tailWord_778446) baseStart_778446 baseEnd_778446 := by
    simpa [prefixWord, tailWord_778446, baseEnd_778446] using wordTrace_append hprefix tailTrace_778446
  have hstable : (prefixWord ++ tailWord_778446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778446).length < 2 ^ (prefixWord ++ tailWord_778446).sum := by decide
  have hdescent : baseEnd_778446 < baseStart_778446 := by decide
  rcases family_descends (prefixWord ++ tailWord_778446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778471 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_778471 : Nat := 118140960795 + 778471 * 2 ^ 59
def prefixEnd_778471 : Nat := 4983230072969 + 3 ^ 40 * 778471 * 2
def baseEnd_778471 : Nat := 355315376521181299851007

theorem tailTrace_778471 : CollatzResearch.WordTrace tailWord_778471 prefixEnd_778471 355315376521181299851007 := by
  unfold tailWord_778471
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393169962739994107039267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18928779975159996071359511 28393169962739994107039267)
  ·
    refine ⟨42589754944109991160558901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28393169962739994107039267 42589754944109991160558901)
    ·
      refine ⟨3992789526010311671302397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42589754944109991160558901 3992789526010311671302397)
      ·
        refine ⟨1497296072253866876738399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3992789526010311671302397 1497296072253866876738399)
        ·
          refine ⟨2245944108380800315107599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497296072253866876738399 2245944108380800315107599)
          ·
            refine ⟨3368916162571200472661399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2245944108380800315107599 3368916162571200472661399)
            ·
              refine ⟨5053374243856800708992099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368916162571200472661399 5053374243856800708992099)
              ·
                refine ⟨7580061365785201063488149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053374243856800708992099 7580061365785201063488149)
                ·
                  refine ⟨355315376521181299851007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7580061365785201063488149 355315376521181299851007)
                  ·
                    rfl

theorem cell20_778471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_778471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778471 prefixEnd_778471 := by exact prefixLift 778471
  have htrace : WordTrace (prefixWord ++ tailWord_778471) baseStart_778471 baseEnd_778471 := by
    simpa [prefixWord, tailWord_778471, baseEnd_778471] using wordTrace_append hprefix tailTrace_778471
  have hstable : (prefixWord ++ tailWord_778471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778471).length < 2 ^ (prefixWord ++ tailWord_778471).sum := by decide
  have hdescent : baseEnd_778471 < baseStart_778471 := by decide
  rcases family_descends (prefixWord ++ tailWord_778471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778498 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_778498 : Nat := 118140960795 + 778498 * 2 ^ 59
def prefixEnd_778498 : Nat := 4983230072969 + 3 ^ 40 * 778498 * 2
def baseEnd_778498 : Nat := 355327700056889205950897

theorem tailTrace_778498 : CollatzResearch.WordTrace tailWord_778498 prefixEnd_778498 355327700056889205950897 := by
  unfold tailWord_778498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098538683410544429568037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18929436489094785145514765 7098538683410544429568037)
  ·
    refine ⟨1330976003139477080544007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7098538683410544429568037 1330976003139477080544007)
    ·
      refine ⟨1996464004709215620816011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330976003139477080544007 1996464004709215620816011)
      ·
        refine ⟨2994696007063823431224017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1996464004709215620816011 2994696007063823431224017)
        ·
          refine ⟨2246022005297867573418013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2994696007063823431224017 2246022005297867573418013)
          ·
            refine ⟨842258251986700340031755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2246022005297867573418013 842258251986700340031755)
            ·
              refine ⟨1263387377980050510047633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842258251986700340031755 1263387377980050510047633)
              ·
                refine ⟨947540533485037882535725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263387377980050510047633 947540533485037882535725)
                ·
                  refine ⟨355327700056889205950897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947540533485037882535725 355327700056889205950897)
                  ·
                    rfl

theorem cell20_778498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_778498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778498 prefixEnd_778498 := by exact prefixLift 778498
  have htrace : WordTrace (prefixWord ++ tailWord_778498) baseStart_778498 baseEnd_778498 := by
    simpa [prefixWord, tailWord_778498, baseEnd_778498] using wordTrace_append hprefix tailTrace_778498
  have hstable : (prefixWord ++ tailWord_778498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778498).length < 2 ^ (prefixWord ++ tailWord_778498).sum := by decide
  have hdescent : baseEnd_778498 < baseStart_778498 := by decide
  rcases family_descends (prefixWord ++ tailWord_778498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778499 : List Nat := [1, 1, 1, 3, 2, 3, 9]
def baseStart_778499 : Nat := 118140960795 + 778499 * 2 ^ 59
def prefixEnd_778499 : Nat := 4983230072969 + 3 ^ 40 * 778499 * 2
def baseEnd_778499 : Nat := 39480906276015294101951

theorem tailTrace_778499 : CollatzResearch.WordTrace tailWord_778499 prefixEnd_778499 39480906276015294101951 := by
  unfold tailWord_778499
  simp only [CollatzResearch.WordTrace]
  refine ⟨28394191206638554889058551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18929460804425703259372367 28394191206638554889058551)
  ·
    refine ⟨42591286809957832333587827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28394191206638554889058551 42591286809957832333587827)
    ·
      refine ⟨63886930214936748500381741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42591286809957832333587827 63886930214936748500381741)
      ·
        refine ⟨23957598830601280687643153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63886930214936748500381741 23957598830601280687643153)
        ·
          refine ⟨17968199122950960515732365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23957598830601280687643153 17968199122950960515732365)
          ·
            refine ⟨6738074671106610193399637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17968199122950960515732365 6738074671106610193399637)
            ·
              refine ⟨39480906276015294101951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6738074671106610193399637 39480906276015294101951)
              ·
                rfl

theorem cell20_778499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_778499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778499 prefixEnd_778499 := by exact prefixLift 778499
  have htrace : WordTrace (prefixWord ++ tailWord_778499) baseStart_778499 baseEnd_778499 := by
    simpa [prefixWord, tailWord_778499, baseEnd_778499] using wordTrace_append hprefix tailTrace_778499
  have hstable : (prefixWord ++ tailWord_778499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778499).length < 2 ^ (prefixWord ++ tailWord_778499).sum := by decide
  have hdescent : baseEnd_778499 < baseStart_778499 := by decide
  rcases family_descends (prefixWord ++ tailWord_778499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778519 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 3]
def baseStart_778519 : Nat := 118140960795 + 778519 * 2 ^ 59
def prefixEnd_778519 : Nat := 4983230072969 + 3 ^ 40 * 778519 * 2
def baseEnd_778519 : Nat := 355337285029106466250811

theorem tailTrace_778519 : CollatzResearch.WordTrace tailWord_778519 prefixEnd_778519 355337285029106466250811 := by
  unfold tailWord_778519
  simp only [CollatzResearch.WordTrace]
  refine ⟨28394920666566098304786611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18929947111044065536524407 28394920666566098304786611)
  ·
    refine ⟨42592380999849147457179917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28394920666566098304786611 42592380999849147457179917)
    ·
      refine ⟨15972142874943430296442469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42592380999849147457179917 15972142874943430296442469)
      ·
        refine ⟨2994776789051893180582963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15972142874943430296442469 2994776789051893180582963)
        ·
          refine ⟨4492165183577839770874445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994776789051893180582963 4492165183577839770874445)
          ·
            refine ⟨1684561943841689914077917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4492165183577839770874445 1684561943841689914077917)
            ·
              refine ⟨631710728940633717779219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1684561943841689914077917 631710728940633717779219)
              ·
                refine ⟨947566093410950576668829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631710728940633717779219 947566093410950576668829)
                ·
                  refine ⟨355337285029106466250811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947566093410950576668829 355337285029106466250811)
                  ·
                    rfl

theorem cell20_778519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_778519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778519 prefixEnd_778519 := by exact prefixLift 778519
  have htrace : WordTrace (prefixWord ++ tailWord_778519) baseStart_778519 baseEnd_778519 := by
    simpa [prefixWord, tailWord_778519, baseEnd_778519] using wordTrace_append hprefix tailTrace_778519
  have hstable : (prefixWord ++ tailWord_778519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778519).length < 2 ^ (prefixWord ++ tailWord_778519).sum := by decide
  have hdescent : baseEnd_778519 < baseStart_778519 := by decide
  rcases family_descends (prefixWord ++ tailWord_778519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778523 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_778523 : Nat := 118140960795 + 778523 * 2 ^ 59
def prefixEnd_778523 : Nat := 4983230072969 + 3 ^ 40 * 778523 * 2
def baseEnd_778523 : Nat := 355339110738100230117461

theorem tailTrace_778523 : CollatzResearch.WordTrace tailWord_778523 prefixEnd_778523 355339110738100230117461 := by
  unfold tailWord_778523
  simp only [CollatzResearch.WordTrace]
  refine ⟨28395066558551606987932223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18930044372367737991954815 28395066558551606987932223)
  ·
    refine ⟨42592599837827410481898335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28395066558551606987932223 42592599837827410481898335)
    ·
      refine ⟨63888899756741115722847503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42592599837827410481898335 63888899756741115722847503)
      ·
        refine ⟨95833349635111673584271255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63888899756741115722847503 95833349635111673584271255)
        ·
          refine ⟨143750024452667510376406883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95833349635111673584271255 143750024452667510376406883)
          ·
            refine ⟨215625036679001265564610325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143750024452667510376406883 215625036679001265564610325)
            ·
              refine ⟨10107423594328184323341109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215625036679001265564610325 10107423594328184323341109)
              ·
                refine ⟨947570961968267280313229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10107423594328184323341109 947570961968267280313229)
                ·
                  refine ⟨355339110738100230117461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947570961968267280313229 355339110738100230117461)
                  ·
                    rfl

theorem cell20_778523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_778523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778523 prefixEnd_778523 := by exact prefixLift 778523
  have htrace : WordTrace (prefixWord ++ tailWord_778523) baseStart_778523 baseEnd_778523 := by
    simpa [prefixWord, tailWord_778523, baseEnd_778523] using wordTrace_append hprefix tailTrace_778523
  have hstable : (prefixWord ++ tailWord_778523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778523).length < 2 ^ (prefixWord ++ tailWord_778523).sum := by decide
  have hdescent : baseEnd_778523 < baseStart_778523 := by decide
  rcases family_descends (prefixWord ++ tailWord_778523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778554 : List Nat := [3, 1, 1, 1, 4, 4, 6]
def baseStart_778554 : Nat := 118140960795 + 778554 * 2 ^ 59
def prefixEnd_778554 : Nat := 4983230072969 + 3 ^ 40 * 778554 * 2
def baseEnd_778554 : Nat := 39483695553644655564889

theorem tailTrace_778554 : CollatzResearch.WordTrace tailWord_778554 prefixEnd_778554 39483695553644655564889 := by
  unfold tailWord_778554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7099049305359824820577679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18930798147626199521540477 7099049305359824820577679)
  ·
    refine ⟨10648573958039737230866519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7099049305359824820577679 10648573958039737230866519)
    ·
      refine ⟨15972860937059605846299779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10648573958039737230866519 15972860937059605846299779)
      ·
        refine ⟨23959291405589408769449669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15972860937059605846299779 23959291405589408769449669)
        ·
          refine ⟨4492367138548014144271813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23959291405589408769449669 4492367138548014144271813)
          ·
            refine ⟨842318838477752652050965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4492367138548014144271813 842318838477752652050965)
            ·
              refine ⟨39483695553644655564889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 842318838477752652050965 39483695553644655564889)
              ·
                rfl

theorem cell20_778554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 6].length) (baseStart_778554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778554 prefixEnd_778554 := by exact prefixLift 778554
  have htrace : WordTrace (prefixWord ++ tailWord_778554) baseStart_778554 baseEnd_778554 := by
    simpa [prefixWord, tailWord_778554, baseEnd_778554] using wordTrace_append hprefix tailTrace_778554
  have hstable : (prefixWord ++ tailWord_778554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778554).length < 2 ^ (prefixWord ++ tailWord_778554).sum := by decide
  have hdescent : baseEnd_778554 < baseStart_778554 := by decide
  rcases family_descends (prefixWord ++ tailWord_778554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778619 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 2]
def baseStart_778619 : Nat := 118140960795 + 778619 * 2 ^ 59
def prefixEnd_778619 : Nat := 4983230072969 + 3 ^ 40 * 778619 * 2
def baseEnd_778619 : Nat := 355382927753950562917069

theorem tailTrace_778619 : CollatzResearch.WordTrace tailWord_778619 prefixEnd_778619 355382927753950562917069 := by
  unfold tailWord_778619
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398567966203815383426911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18932378644135876922284607 28398567966203815383426911)
  ·
    refine ⟨42597851949305723075140367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28398567966203815383426911 42597851949305723075140367)
    ·
      refine ⟨63896777923958584612710551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42597851949305723075140367 63896777923958584612710551)
      ·
        refine ⟨95845166885937876919065827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63896777923958584612710551 95845166885937876919065827)
        ·
          refine ⟨143767750328906815378598741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95845166885937876919065827 143767750328906815378598741)
          ·
            refine ⟨842389162083438371358977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 143767750328906815378598741 842389162083438371358977)
            ·
              refine ⟨631791871562578778519233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842389162083438371358977 631791871562578778519233)
              ·
                refine ⟨473843903671934083889425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631791871562578778519233 473843903671934083889425)
                ·
                  refine ⟨355382927753950562917069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473843903671934083889425 355382927753950562917069)
                  ·
                    rfl

theorem cell20_778619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 2].length) (baseStart_778619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778619 prefixEnd_778619 := by exact prefixLift 778619
  have htrace : WordTrace (prefixWord ++ tailWord_778619) baseStart_778619 baseEnd_778619 := by
    simpa [prefixWord, tailWord_778619, baseEnd_778619] using wordTrace_append hprefix tailTrace_778619
  have hstable : (prefixWord ++ tailWord_778619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778619).length < 2 ^ (prefixWord ++ tailWord_778619).sum := by decide
  have hdescent : baseEnd_778619 < baseStart_778619 := by decide
  rcases family_descends (prefixWord ++ tailWord_778619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778623 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 2]
def baseStart_778623 : Nat := 118140960795 + 778623 * 2 ^ 59
def prefixEnd_778623 : Nat := 4983230072969 + 3 ^ 40 * 778623 * 2
def baseEnd_778623 : Nat := 355384753462944326783719

theorem tailTrace_778623 : CollatzResearch.WordTrace tailWord_778623 prefixEnd_778623 355384753462944326783719 := by
  unfold tailWord_778623
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398713858189324066572523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18932475905459549377715015 28398713858189324066572523)
  ·
    refine ⟨42598070787283986099858785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28398713858189324066572523 42598070787283986099858785)
    ·
      refine ⟨31948553090462989574894089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42598070787283986099858785 31948553090462989574894089)
      ·
        refine ⟨23961414817847242181170567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31948553090462989574894089 23961414817847242181170567)
        ·
          refine ⟨35942122226770863271755851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23961414817847242181170567 35942122226770863271755851)
          ·
            refine ⟨53913183340156294907633777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35942122226770863271755851 53913183340156294907633777)
            ·
              refine ⟨40434887505117221180725333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53913183340156294907633777 40434887505117221180725333)
              ·
                refine ⟨473846337950592435711625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 40434887505117221180725333 473846337950592435711625)
                ·
                  refine ⟨355384753462944326783719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473846337950592435711625 355384753462944326783719)
                  ·
                    rfl

theorem cell20_778623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 2].length) (baseStart_778623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778623 prefixEnd_778623 := by exact prefixLift 778623
  have htrace : WordTrace (prefixWord ++ tailWord_778623) baseStart_778623 baseEnd_778623 := by
    simpa [prefixWord, tailWord_778623, baseEnd_778623] using wordTrace_append hprefix tailTrace_778623
  have hstable : (prefixWord ++ tailWord_778623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778623).length < 2 ^ (prefixWord ++ tailWord_778623).sum := by decide
  have hdescent : baseEnd_778623 < baseStart_778623 := by decide
  rcases family_descends (prefixWord ++ tailWord_778623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778723 : List Nat := [1, 1, 1, 6, 4, 1, 6]
def baseStart_778723 : Nat := 118140960795 + 778723 * 2 ^ 59
def prefixEnd_778723 : Nat := 4983230072969 + 3 ^ 40 * 778723 * 2
def baseEnd_778723 : Nat := 39492266243087602605553

theorem tailTrace_778723 : CollatzResearch.WordTrace tailWord_778723 prefixEnd_778723 39492266243087602605553 := by
  unfold tailWord_778723
  simp only [CollatzResearch.WordTrace]
  refine ⟨28402361157827041145212823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18934907438551360763475215 28402361157827041145212823)
  ·
    refine ⟨42603541736740561717819235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28402361157827041145212823 42603541736740561717819235)
    ·
      refine ⟨63905312605110842576728853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42603541736740561717819235 63905312605110842576728853)
      ·
        refine ⟨2995561528364570745784165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63905312605110842576728853 2995561528364570745784165)
        ·
          refine ⟨561667786568357014834531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2995561528364570745784165 561667786568357014834531)
          ·
            refine ⟨842501679852535522251797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561667786568357014834531 842501679852535522251797)
            ·
              refine ⟨39492266243087602605553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 842501679852535522251797 39492266243087602605553)
              ·
                rfl

theorem cell20_778723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 6].length) (baseStart_778723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778723 prefixEnd_778723 := by exact prefixLift 778723
  have htrace : WordTrace (prefixWord ++ tailWord_778723) baseStart_778723 baseEnd_778723 := by
    simpa [prefixWord, tailWord_778723, baseEnd_778723] using wordTrace_append hprefix tailTrace_778723
  have hstable : (prefixWord ++ tailWord_778723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778723).length < 2 ^ (prefixWord ++ tailWord_778723).sum := by decide
  have hdescent : baseEnd_778723 < baseStart_778723 := by decide
  rcases family_descends (prefixWord ++ tailWord_778723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778751 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_778751 : Nat := 118140960795 + 778751 * 2 ^ 59
def prefixEnd_778751 : Nat := 4983230072969 + 3 ^ 40 * 778751 * 2
def baseEnd_778751 : Nat := 355443176150744770516529

theorem tailTrace_778751 : CollatzResearch.WordTrace tailWord_778751 prefixEnd_778751 355443176150744770516529 := by
  unfold tailWord_778751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28403382401725601927232107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18935588267817067951488071 28403382401725601927232107)
  ·
    refine ⟨42605073602588402890848161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28403382401725601927232107 42605073602588402890848161)
    ·
      refine ⟨31953805201941302168136121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42605073602588402890848161 31953805201941302168136121)
      ·
        refine ⟨23965353901455976626102091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31953805201941302168136121 23965353901455976626102091)
        ·
          refine ⟨35948030852183964939153137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23965353901455976626102091 35948030852183964939153137)
          ·
            refine ⟨26961023139137973704364853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35948030852183964939153137 26961023139137973704364853)
            ·
              refine ⟨2527595919294185034784205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26961023139137973704364853 2527595919294185034784205)
              ·
                refine ⟨947848469735319388044077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2527595919294185034784205 947848469735319388044077)
                ·
                  refine ⟨355443176150744770516529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947848469735319388044077 355443176150744770516529)
                  ·
                    rfl

theorem cell20_778751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_778751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778751 prefixEnd_778751 := by exact prefixLift 778751
  have htrace : WordTrace (prefixWord ++ tailWord_778751) baseStart_778751 baseEnd_778751 := by
    simpa [prefixWord, tailWord_778751, baseEnd_778751] using wordTrace_append hprefix tailTrace_778751
  have hstable : (prefixWord ++ tailWord_778751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778751).length < 2 ^ (prefixWord ++ tailWord_778751).sum := by decide
  have hdescent : baseEnd_778751 < baseStart_778751 := by decide
  rcases family_descends (prefixWord ++ tailWord_778751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778789 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_778789 : Nat := 118140960795 + 778789 * 2 ^ 59
def prefixEnd_778789 : Nat := 4983230072969 + 3 ^ 40 * 778789 * 2
def baseEnd_778789 : Nat := 355460520386185527249707

theorem tailTrace_778789 : CollatzResearch.WordTrace tailWord_778789 prefixEnd_778789 355460520386185527249707 := by
  unfold tailWord_778789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28404768375587934417115421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18936512250391956278076947 28404768375587934417115421)
  ·
    refine ⟨10651788140845475406418283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28404768375587934417115421 10651788140845475406418283)
    ·
      refine ⟨15977682211268213109627425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10651788140845475406418283 15977682211268213109627425)
      ·
        refine ⟨11983261658451159832220569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15977682211268213109627425 11983261658451159832220569)
        ·
          refine ⟨8987446243838369874165427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11983261658451159832220569 8987446243838369874165427)
          ·
            refine ⟨13481169365757554811248141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8987446243838369874165427 13481169365757554811248141)
            ·
              refine ⟨5055438512159083054218053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13481169365757554811248141 5055438512159083054218053)
              ·
                refine ⟨947894721029828072665885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5055438512159083054218053 947894721029828072665885)
                ·
                  refine ⟨355460520386185527249707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947894721029828072665885 355460520386185527249707)
                  ·
                    rfl

theorem cell20_778789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_778789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778789 prefixEnd_778789 := by exact prefixLift 778789
  have htrace : WordTrace (prefixWord ++ tailWord_778789) baseStart_778789 baseEnd_778789 := by
    simpa [prefixWord, tailWord_778789, baseEnd_778789] using wordTrace_append hprefix tailTrace_778789
  have hstable : (prefixWord ++ tailWord_778789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778789).length < 2 ^ (prefixWord ++ tailWord_778789).sum := by decide
  have hdescent : baseEnd_778789 < baseStart_778789 := by decide
  rcases family_descends (prefixWord ++ tailWord_778789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778813 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_778813 : Nat := 118140960795 + 778813 * 2 ^ 59
def prefixEnd_778813 : Nat := 4983230072969 + 3 ^ 40 * 778813 * 2
def baseEnd_778813 : Nat := 355471474640148110449609

theorem tailTrace_778813 : CollatzResearch.WordTrace tailWord_778813 prefixEnd_778813 355471474640148110449609 := by
  unfold tailWord_778813
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405643727500986515989093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18937095818333991010659395 28405643727500986515989093)
  ·
    refine ⟨5326058198906434971747955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28405643727500986515989093 5326058198906434971747955)
    ·
      refine ⟨7989087298359652457621933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5326058198906434971747955 7989087298359652457621933)
      ·
        refine ⟨2995907736884869671608225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7989087298359652457621933 2995907736884869671608225)
        ·
          refine ⟨2246930802663652253706169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2995907736884869671608225 2246930802663652253706169)
          ·
            refine ⟨1685198101997739190279627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2246930802663652253706169 1685198101997739190279627)
            ·
              refine ⟨2527797152996608785419441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685198101997739190279627 2527797152996608785419441)
              ·
                refine ⟨1895847864747456589064581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527797152996608785419441 1895847864747456589064581)
                ·
                  refine ⟨355471474640148110449609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895847864747456589064581 355471474640148110449609)
                  ·
                    rfl

theorem cell20_778813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_778813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_778813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_778813 prefixEnd_778813 := by exact prefixLift 778813
  have htrace : WordTrace (prefixWord ++ tailWord_778813) baseStart_778813 baseEnd_778813 := by
    simpa [prefixWord, tailWord_778813, baseEnd_778813] using wordTrace_append hprefix tailTrace_778813
  have hstable : (prefixWord ++ tailWord_778813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778813).length < 2 ^ (prefixWord ++ tailWord_778813).sum := by decide
  have hdescent : baseEnd_778813 < baseStart_778813 := by decide
  rcases family_descends (prefixWord ++ tailWord_778813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
