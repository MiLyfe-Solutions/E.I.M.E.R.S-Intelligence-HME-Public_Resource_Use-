import V185TrunkScan19Chunk012

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_131828 : List Nat := [2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_131828 : Nat := 118140960795 + 131828 * 2 ^ 59
def prefixEnd_131828 : Nat := 4983230072969 + 3 ^ 40 * 131828 * 2
def baseEnd_131828 : Nat := 40113260871712862840735

theorem tailTrace_131828 : CollatzResearch.WordTrace tailWord_131828 prefixEnd_131828 40113260871712862840735 := by
  unfold tailWord_131828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404081083208572637522069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3205441444278096850029425 2404081083208572637522069)
  ·
    refine ⟨112691300775401842383847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2404081083208572637522069 112691300775401842383847)
    ·
      refine ⟨169036951163102763575771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112691300775401842383847 169036951163102763575771)
      ·
        refine ⟨253555426744654145363657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169036951163102763575771 253555426744654145363657)
        ·
          refine ⟨190166570058490609022743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253555426744654145363657 190166570058490609022743)
          ·
            refine ⟨285249855087735913534115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190166570058490609022743 285249855087735913534115)
            ·
              refine ⟨427874782631603870301173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285249855087735913534115 427874782631603870301173)
              ·
                refine ⟨40113260871712862840735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 427874782631603870301173 40113260871712862840735)
                ·
                  rfl

theorem cell19_131828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_131828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131828 prefixEnd_131828 := by exact prefixLift 131828
  have htrace : WordTrace (prefixWord ++ tailWord_131828) baseStart_131828 baseEnd_131828 := by
    simpa [prefixWord, tailWord_131828, baseEnd_131828] using wordTrace_append hprefix tailTrace_131828
  have hstable : (prefixWord ++ tailWord_131828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131828).length < 2 ^ (prefixWord ++ tailWord_131828).sum := by decide
  have hdescent : baseEnd_131828 < baseStart_131828 := by decide
  rcases family_descends (prefixWord ++ tailWord_131828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131872 : List Nat := [2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_131872 : Nat := 118140960795 + 131872 * 2 ^ 59
def prefixEnd_131872 : Nat := 4983230072969 + 3 ^ 40 * 131872 * 2
def baseEnd_131872 : Nat := 40126649404333797862837

theorem tailTrace_131872 : CollatzResearch.WordTrace tailWord_131872 prefixEnd_131872 40126649404333797862837 := by
  unfold tailWord_131872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404883489128870394822935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3206511318838493859763913 2404883489128870394822935)
  ·
    refine ⟨3607325233693305592234403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2404883489128870394822935 3607325233693305592234403)
    ·
      refine ⟨5410987850539958388351605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607325233693305592234403 5410987850539958388351605)
      ·
        refine ⟨507280110988121098907963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5410987850539958388351605 507280110988121098907963)
        ·
          refine ⟨760920166482181648361945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507280110988121098907963 760920166482181648361945)
          ·
            refine ⟨570690124861636236271459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760920166482181648361945 570690124861636236271459)
            ·
              refine ⟨856035187292454354407189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570690124861636236271459 856035187292454354407189)
              ·
                refine ⟨40126649404333797862837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 856035187292454354407189 40126649404333797862837)
                ·
                  rfl

theorem cell19_131872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_131872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131872 prefixEnd_131872 := by exact prefixLift 131872
  have htrace : WordTrace (prefixWord ++ tailWord_131872) baseStart_131872 baseEnd_131872 := by
    simpa [prefixWord, tailWord_131872, baseEnd_131872] using wordTrace_append hprefix tailTrace_131872
  have hstable : (prefixWord ++ tailWord_131872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131872).length < 2 ^ (prefixWord ++ tailWord_131872).sum := by decide
  have hdescent : baseEnd_131872 < baseStart_131872 := by decide
  rcases family_descends (prefixWord ++ tailWord_131872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131891 : List Nat := [1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_131891 : Nat := 118140960795 + 131891 * 2 ^ 59
def prefixEnd_131891 : Nat := 4983230072969 + 3 ^ 40 * 131891 * 2
def baseEnd_131891 : Nat := 40132430816147383440563

theorem tailTrace_131891 : CollatzResearch.WordTrace tailWord_131891 prefixEnd_131891 40132430816147383440563 := by
  unfold tailWord_131891
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810459965188907034587527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3206973310125938023058351 4810459965188907034587527)
  ·
    refine ⟨7215689947783360551881291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4810459965188907034587527 7215689947783360551881291)
    ·
      refine ⟨10823534921675040827821937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215689947783360551881291 10823534921675040827821937)
      ·
        refine ⟨8117651191256280620866453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10823534921675040827821937 8117651191256280620866453)
        ·
          refine ⟨380514899590138154103115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8117651191256280620866453 380514899590138154103115)
          ·
            refine ⟨570772349385207231154673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380514899590138154103115 570772349385207231154673)
            ·
              refine ⟨428079262038905423366005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570772349385207231154673 428079262038905423366005)
              ·
                refine ⟨40132430816147383440563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 428079262038905423366005 40132430816147383440563)
                ·
                  rfl

theorem cell19_131891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_131891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131891 prefixEnd_131891 := by exact prefixLift 131891
  have htrace : WordTrace (prefixWord ++ tailWord_131891) baseStart_131891 baseEnd_131891 := by
    simpa [prefixWord, tailWord_131891, baseEnd_131891] using wordTrace_append hprefix tailTrace_131891
  have hstable : (prefixWord ++ tailWord_131891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131891).length < 2 ^ (prefixWord ++ tailWord_131891).sum := by decide
  have hdescent : baseEnd_131891 < baseStart_131891 := by decide
  rcases family_descends (prefixWord ++ tailWord_131891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131908 : List Nat := [2, 3, 4, 2, 8]
def baseStart_131908 : Nat := 118140960795 + 131908 * 2 ^ 59
def prefixEnd_131908 : Nat := 4983230072969 + 3 ^ 40 * 131908 * 2
def baseEnd_131908 : Nat := 1486577913270236335657

theorem tailTrace_131908 : CollatzResearch.WordTrace tailWord_131908 prefixEnd_131908 1486577913270236335657 := by
  unfold tailWord_131908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405540003063659468978189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3207386670751545958637585 2405540003063659468978189)
  ·
    refine ⟨902077501148872300866821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2405540003063659468978189 902077501148872300866821)
    ·
      refine ⟨169139531465413556412529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 902077501148872300866821 169139531465413556412529)
      ·
        refine ⟨126854648599060167309397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169139531465413556412529 126854648599060167309397)
        ·
          refine ⟨1486577913270236335657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 126854648599060167309397 1486577913270236335657)
          ·
            rfl

theorem cell19_131908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 8].length) (baseStart_131908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131908 prefixEnd_131908 := by exact prefixLift 131908
  have htrace : WordTrace (prefixWord ++ tailWord_131908) baseStart_131908 baseEnd_131908 := by
    simpa [prefixWord, tailWord_131908, baseEnd_131908] using wordTrace_append hprefix tailTrace_131908
  have hstable : (prefixWord ++ tailWord_131908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131908).length < 2 ^ (prefixWord ++ tailWord_131908).sum := by decide
  have hdescent : baseEnd_131908 < baseStart_131908 := by decide
  rcases family_descends (prefixWord ++ tailWord_131908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131927 : List Nat := [1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_131927 : Nat := 118140960795 + 131927 * 2 ^ 59
def prefixEnd_131927 : Nat := 4983230072969 + 3 ^ 40 * 131927 * 2
def baseEnd_131927 : Nat := 40143385070109966640465

theorem tailTrace_131927 : CollatzResearch.WordTrace tailWord_131927 prefixEnd_131927 40143385070109966640465 := by
  unfold tailWord_131927
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811772993058485182898035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3207848662038990121932023 4811772993058485182898035)
  ·
    refine ⟨7217659489587727774347053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4811772993058485182898035 7217659489587727774347053)
    ·
      refine ⟨2706622308595397915380145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7217659489587727774347053 2706622308595397915380145)
      ·
        refine ⟨2029966731446548436535109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2706622308595397915380145 2029966731446548436535109)
        ·
          refine ⟨380618762146227831850333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2029966731446548436535109 380618762146227831850333)
          ·
            refine ⟨142732035804835436943875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380618762146227831850333 142732035804835436943875)
            ·
              refine ⟨214098053707253155415813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142732035804835436943875 214098053707253155415813)
              ·
                refine ⟨40143385070109966640465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214098053707253155415813 40143385070109966640465)
                ·
                  rfl

theorem cell19_131927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_131927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131927 prefixEnd_131927 := by exact prefixLift 131927
  have htrace : WordTrace (prefixWord ++ tailWord_131927) baseStart_131927 baseEnd_131927 := by
    simpa [prefixWord, tailWord_131927, baseEnd_131927] using wordTrace_append hprefix tailTrace_131927
  have hstable : (prefixWord ++ tailWord_131927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131927).length < 2 ^ (prefixWord ++ tailWord_131927).sum := by decide
  have hdescent : baseEnd_131927 < baseStart_131927 := by decide
  rcases family_descends (prefixWord ++ tailWord_131927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131929 : List Nat := [1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_131929 : Nat := 118140960795 + 131929 * 2 ^ 59
def prefixEnd_131929 : Nat := 4983230072969 + 3 ^ 40 * 131929 * 2
def baseEnd_131929 : Nat := 40143993639774554596015

theorem tailTrace_131929 : CollatzResearch.WordTrace tailWord_131929 prefixEnd_131929 40143993639774554596015 := by
  unfold tailWord_131929
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811845939051239524470841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3207897292700826349647227 4811845939051239524470841)
  ·
    refine ⟨3608884454288429643353131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4811845939051239524470841 3608884454288429643353131)
    ·
      refine ⟨5413326681432644465029697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608884454288429643353131 5413326681432644465029697)
      ·
        refine ⟨4059995011074483348772273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5413326681432644465029697 4059995011074483348772273)
        ·
          refine ⟨3044996258305862511579205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4059995011074483348772273 3044996258305862511579205)
          ·
            refine ⟨570936798432349220921101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3044996258305862511579205 570936798432349220921101)
            ·
              refine ⟨214101299412130957845413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570936798432349220921101 214101299412130957845413)
              ·
                refine ⟨40143993639774554596015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214101299412130957845413 40143993639774554596015)
                ·
                  rfl

theorem cell19_131929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_131929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131929 prefixEnd_131929 := by exact prefixLift 131929
  have htrace : WordTrace (prefixWord ++ tailWord_131929) baseStart_131929 baseEnd_131929 := by
    simpa [prefixWord, tailWord_131929, baseEnd_131929] using wordTrace_append hprefix tailTrace_131929
  have hstable : (prefixWord ++ tailWord_131929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131929).length < 2 ^ (prefixWord ++ tailWord_131929).sum := by decide
  have hdescent : baseEnd_131929 < baseStart_131929 := by decide
  rcases family_descends (prefixWord ++ tailWord_131929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132001 : List Nat := [1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_132001 : Nat := 118140960795 + 132001 * 2 ^ 59
def prefixEnd_132001 : Nat := 4983230072969 + 3 ^ 40 * 132001 * 2
def baseEnd_132001 : Nat := 40165902147699720995819

theorem tailTrace_132001 : CollatzResearch.WordTrace tailWord_132001 prefixEnd_132001 40165902147699720995819 := by
  unfold tailWord_132001
  simp only [CollatzResearch.WordTrace]
  refine ⟨4814471994790395821091857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3209647996526930547394571 4814471994790395821091857)
  ·
    refine ⟨3610853996092796865818893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4814471994790395821091857 3610853996092796865818893)
    ·
      refine ⟨1354070248534798824682085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3610853996092796865818893 1354070248534798824682085)
      ·
        refine ⟨253888171600274779627891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1354070248534798824682085 253888171600274779627891)
        ·
          refine ⟨380832257400412169441837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253888171600274779627891 380832257400412169441837)
          ·
            refine ⟨142812096525154563540689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380832257400412169441837 142812096525154563540689)
            ·
              refine ⟨107109072393865922655517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142812096525154563540689 107109072393865922655517)
              ·
                refine ⟨40165902147699720995819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107109072393865922655517 40165902147699720995819)
                ·
                  rfl

theorem cell19_132001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_132001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132001 prefixEnd_132001 := by exact prefixLift 132001
  have htrace : WordTrace (prefixWord ++ tailWord_132001) baseStart_132001 baseEnd_132001 := by
    simpa [prefixWord, tailWord_132001, baseEnd_132001] using wordTrace_append hprefix tailTrace_132001
  have hstable : (prefixWord ++ tailWord_132001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132001).length < 2 ^ (prefixWord ++ tailWord_132001).sum := by decide
  have hdescent : baseEnd_132001 < baseStart_132001 := by decide
  rcases family_descends (prefixWord ++ tailWord_132001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132020 : List Nat := [2, 5, 2, 1, 1, 3, 5]
def baseStart_132020 : Nat := 118140960795 + 132020 * 2 ^ 59
def prefixEnd_132020 : Nat := 4983230072969 + 3 ^ 40 * 132020 * 2
def baseEnd_132020 : Nat := 13390561186504435524515

theorem tailTrace_132020 : CollatzResearch.WordTrace tailWord_132020 prefixEnd_132020 13390561186504435524515 := by
  unfold tailWord_132020
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407582490860781033016757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3210109987814374710689009 2407582490860781033016757)
  ·
    refine ⟨225710858518198221845321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2407582490860781033016757 225710858518198221845321)
    ·
      refine ⟨169283143888648666383991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225710858518198221845321 169283143888648666383991)
      ·
        refine ⟨253924715832972999575987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169283143888648666383991 253924715832972999575987)
        ·
          refine ⟨380887073749459499363981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253924715832972999575987 380887073749459499363981)
          ·
            refine ⟨142832652656047312261493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380887073749459499363981 142832652656047312261493)
            ·
              refine ⟨13390561186504435524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142832652656047312261493 13390561186504435524515)
              ·
                rfl

theorem cell19_132020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_132020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132020 prefixEnd_132020 := by exact prefixLift 132020
  have htrace : WordTrace (prefixWord ++ tailWord_132020) baseStart_132020 baseEnd_132020 := by
    simpa [prefixWord, tailWord_132020, baseEnd_132020] using wordTrace_append hprefix tailTrace_132020
  have hstable : (prefixWord ++ tailWord_132020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132020).length < 2 ^ (prefixWord ++ tailWord_132020).sum := by decide
  have hdescent : baseEnd_132020 < baseStart_132020 := by decide
  rcases family_descends (prefixWord ++ tailWord_132020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132024 : List Nat := [2, 1, 2, 1, 2, 6, 5]
def baseStart_132024 : Nat := 118140960795 + 132024 * 2 ^ 59
def prefixEnd_132024 : Nat := 4983230072969 + 3 ^ 40 * 132024 * 2
def baseEnd_132024 : Nat := 13390966899614160828215

theorem tailTrace_132024 : CollatzResearch.WordTrace tailWord_132024 prefixEnd_132024 13390966899614160828215 := by
  unfold tailWord_132024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407655436853535374589563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3210207249138047166119417 2407655436853535374589563)
  ·
    refine ⟨3611483155280303061884345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2407655436853535374589563 3611483155280303061884345)
    ·
      refine ⟨2708612366460227296413259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3611483155280303061884345 2708612366460227296413259)
      ·
        refine ⟨4062918549690340944619889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708612366460227296413259 4062918549690340944619889)
        ·
          refine ⟨3047188912267755708464917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4062918549690340944619889 3047188912267755708464917)
          ·
            refine ⟨142836980262551048834293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3047188912267755708464917 142836980262551048834293)
            ·
              refine ⟨13390966899614160828215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142836980262551048834293 13390966899614160828215)
              ·
                rfl

theorem cell19_132024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_132024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132024 prefixEnd_132024 := by exact prefixLift 132024
  have htrace : WordTrace (prefixWord ++ tailWord_132024) baseStart_132024 baseEnd_132024 := by
    simpa [prefixWord, tailWord_132024, baseEnd_132024] using wordTrace_append hprefix tailTrace_132024
  have hstable : (prefixWord ++ tailWord_132024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132024).length < 2 ^ (prefixWord ++ tailWord_132024).sum := by decide
  have hdescent : baseEnd_132024 < baseStart_132024 := by decide
  rcases family_descends (prefixWord ++ tailWord_132024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132043 : List Nat := [1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_132043 : Nat := 118140960795 + 132043 * 2 ^ 59
def prefixEnd_132043 : Nat := 4983230072969 + 3 ^ 40 * 132043 * 2
def baseEnd_132043 : Nat := 40178682110656068062371

theorem tailTrace_132043 : CollatzResearch.WordTrace tailWord_132043 prefixEnd_132043 40178682110656068062371 := by
  unfold tailWord_132043
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816003860638236994120783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3210669240425491329413855 4816003860638236994120783)
  ·
    refine ⟨7224005790957355491181175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4816003860638236994120783 7224005790957355491181175)
    ·
      refine ⟨10836008686436033236771763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7224005790957355491181175 10836008686436033236771763)
      ·
        refine ⟨16254013029654049855157645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10836008686436033236771763 16254013029654049855157645)
        ·
          refine ⟨6095254886120268695684117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16254013029654049855157645 6095254886120268695684117)
          ·
            refine ⟨285715072786887595110193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6095254886120268695684117 285715072786887595110193)
            ·
              refine ⟨214286304590165696332645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285715072786887595110193 214286304590165696332645)
              ·
                refine ⟨40178682110656068062371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214286304590165696332645 40178682110656068062371)
                ·
                  rfl

theorem cell19_132043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_132043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132043 prefixEnd_132043 := by exact prefixLift 132043
  have htrace : WordTrace (prefixWord ++ tailWord_132043) baseStart_132043 baseEnd_132043 := by
    simpa [prefixWord, tailWord_132043, baseEnd_132043] using wordTrace_append hprefix tailTrace_132043
  have hstable : (prefixWord ++ tailWord_132043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132043).length < 2 ^ (prefixWord ++ tailWord_132043).sum := by decide
  have hdescent : baseEnd_132043 < baseStart_132043 := by decide
  rcases family_descends (prefixWord ++ tailWord_132043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132094 : List Nat := [4, 2, 2, 2, 3, 1, 1, 4]
def baseStart_132094 : Nat := 118140960795 + 132094 * 2 ^ 59
def prefixEnd_132094 : Nat := 4983230072969 + 3 ^ 40 * 132094 * 2
def baseEnd_132094 : Nat := 40194200637103060928899

theorem tailTrace_132094 : CollatzResearch.WordTrace tailWord_132094 prefixEnd_132094 40194200637103060928899 := by
  unfold tailWord_132094
  simp only [CollatzResearch.WordTrace]
  refine ⟨602232997931684088028417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3211909322302315136151557 602232997931684088028417)
  ·
    refine ⟨451674748448763066021313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602232997931684088028417 451674748448763066021313)
    ·
      refine ⟨338756061336572299515985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451674748448763066021313 338756061336572299515985)
      ·
        refine ⟨254067046002429224636989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338756061336572299515985 254067046002429224636989)
        ·
          refine ⟨95275142250910959238871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254067046002429224636989 95275142250910959238871)
          ·
            refine ⟨142912713376366438858307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95275142250910959238871 142912713376366438858307)
            ·
              refine ⟨214369070064549658287461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142912713376366438858307 214369070064549658287461)
              ·
                refine ⟨40194200637103060928899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214369070064549658287461 40194200637103060928899)
                ·
                  rfl

theorem cell19_132094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_132094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132094 prefixEnd_132094 := by exact prefixLift 132094
  have htrace : WordTrace (prefixWord ++ tailWord_132094) baseStart_132094 baseEnd_132094 := by
    simpa [prefixWord, tailWord_132094, baseEnd_132094] using wordTrace_append hprefix tailTrace_132094
  have hstable : (prefixWord ++ tailWord_132094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132094).length < 2 ^ (prefixWord ++ tailWord_132094).sum := by decide
  have hdescent : baseEnd_132094 < baseStart_132094 := by decide
  rcases family_descends (prefixWord ++ tailWord_132094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132117 : List Nat := [1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_132117 : Nat := 118140960795 + 132117 * 2 ^ 59
def prefixEnd_132117 : Nat := 4983230072969 + 3 ^ 40 * 132117 * 2
def baseEnd_132117 : Nat := 40201199188245822417725

theorem tailTrace_132117 : CollatzResearch.WordTrace tailWord_132117 prefixEnd_132117 40201199188245822417725 := by
  unfold tailWord_132117
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818702862370147632314605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3212468574913431754876403 4818702862370147632314605)
  ·
    refine ⟨1807013573388805362117977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4818702862370147632314605 1807013573388805362117977)
    ·
      refine ⟨1355260180041604021588483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1807013573388805362117977 1355260180041604021588483)
      ·
        refine ⟨2032890270062406032382725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355260180041604021588483 2032890270062406032382725)
        ·
          refine ⟨381166925636701131071761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2032890270062406032382725 381166925636701131071761)
          ·
            refine ⟨285875194227525848303821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381166925636701131071761 285875194227525848303821)
            ·
              refine ⟨107203197835322193113933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285875194227525848303821 107203197835322193113933)
              ·
                refine ⟨40201199188245822417725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107203197835322193113933 40201199188245822417725)
                ·
                  rfl

theorem cell19_132117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_132117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132117 prefixEnd_132117 := by exact prefixLift 132117
  have htrace : WordTrace (prefixWord ++ tailWord_132117) baseStart_132117 baseEnd_132117 := by
    simpa [prefixWord, tailWord_132117, baseEnd_132117] using wordTrace_append hprefix tailTrace_132117
  have hstable : (prefixWord ++ tailWord_132117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132117).length < 2 ^ (prefixWord ++ tailWord_132117).sum := by decide
  have hdescent : baseEnd_132117 < baseStart_132117 := by decide
  rcases family_descends (prefixWord ++ tailWord_132117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132121 : List Nat := [1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_132121 : Nat := 118140960795 + 132121 * 2 ^ 59
def prefixEnd_132121 : Nat := 4983230072969 + 3 ^ 40 * 132121 * 2
def baseEnd_132121 : Nat := 40202416327574998328825

theorem tailTrace_132121 : CollatzResearch.WordTrace tailWord_132121 prefixEnd_132121 40202416327574998328825 := by
  unfold tailWord_132121
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818848754355656315460217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3212565836237104210306811 4818848754355656315460217)
  ·
    refine ⟨3614136565766742236595163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4818848754355656315460217 3614136565766742236595163)
    ·
      refine ⟨5421204848650113354892745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614136565766742236595163 5421204848650113354892745)
      ·
        refine ⟨4065903636487585016169559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5421204848650113354892745 4065903636487585016169559)
        ·
          refine ⟨6098855454731377524254339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065903636487585016169559 6098855454731377524254339)
          ·
            refine ⟨9148283182097066286381509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098855454731377524254339 9148283182097066286381509)
            ·
              refine ⟨1715303096643199928696533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9148283182097066286381509 1715303096643199928696533)
              ·
                refine ⟨40202416327574998328825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1715303096643199928696533 40202416327574998328825)
                ·
                  rfl

theorem cell19_132121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_132121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132121 prefixEnd_132121 := by exact prefixLift 132121
  have htrace : WordTrace (prefixWord ++ tailWord_132121) baseStart_132121 baseEnd_132121 := by
    simpa [prefixWord, tailWord_132121, baseEnd_132121] using wordTrace_append hprefix tailTrace_132121
  have hstable : (prefixWord ++ tailWord_132121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132121).length < 2 ^ (prefixWord ++ tailWord_132121).sum := by decide
  have hdescent : baseEnd_132121 < baseStart_132121 := by decide
  rcases family_descends (prefixWord ++ tailWord_132121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132140 : List Nat := [2, 2, 1, 1, 1, 2, 10]
def baseStart_132140 : Nat := 118140960795 + 132140 * 2 ^ 59
def prefixEnd_132140 : Nat := 4983230072969 + 3 ^ 40 * 132140 * 2
def baseEnd_132140 : Nat := 13402732579796194635517

theorem tailTrace_132140 : CollatzResearch.WordTrace tailWord_132140 prefixEnd_132140 13402732579796194635517 := by
  unfold tailWord_132140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409770870643411280200937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3213027827524548373601249 2409770870643411280200937)
  ·
    refine ⟨1807328152982558460150703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2409770870643411280200937 1807328152982558460150703)
    ·
      refine ⟨2710992229473837690226055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1807328152982558460150703 2710992229473837690226055)
      ·
        refine ⟨4066488344210756535339083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2710992229473837690226055 4066488344210756535339083)
        ·
          refine ⟨6099732516316134803008625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4066488344210756535339083 6099732516316134803008625)
          ·
            refine ⟨4574799387237101102256469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6099732516316134803008625 4574799387237101102256469)
            ·
              refine ⟨13402732579796194635517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4574799387237101102256469 13402732579796194635517)
              ·
                rfl

theorem cell19_132140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_132140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132140 prefixEnd_132140 := by exact prefixLift 132140
  have htrace : WordTrace (prefixWord ++ tailWord_132140) baseStart_132140 baseEnd_132140 := by
    simpa [prefixWord, tailWord_132140, baseEnd_132140] using wordTrace_append hprefix tailTrace_132140
  have hstable : (prefixWord ++ tailWord_132140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132140).length < 2 ^ (prefixWord ++ tailWord_132140).sum := by decide
  have hdescent : baseEnd_132140 < baseStart_132140 := by decide
  rcases family_descends (prefixWord ++ tailWord_132140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132159 : List Nat := [1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_132159 : Nat := 118140960795 + 132159 * 2 ^ 59
def prefixEnd_132159 : Nat := 4983230072969 + 3 ^ 40 * 132159 * 2
def baseEnd_132159 : Nat := 40213979151202169484277

theorem tailTrace_132159 : CollatzResearch.WordTrace tailWord_132159 prefixEnd_132159 40213979151202169484277 := by
  unfold tailWord_132159
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820234728217988805343531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3213489818811992536895687 4820234728217988805343531)
  ·
    refine ⟨7230352092326983208015297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4820234728217988805343531 7230352092326983208015297)
    ·
      refine ⟨5422764069245237406011473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7230352092326983208015297 5422764069245237406011473)
      ·
        refine ⟨4067073051933928054508605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5422764069245237406011473 4067073051933928054508605)
        ·
          refine ⟨1525152394475223020440727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4067073051933928054508605 1525152394475223020440727)
          ·
            refine ⟨2287728591712834530661091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525152394475223020440727 2287728591712834530661091)
            ·
              refine ⟨3431592887569251795991637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287728591712834530661091 3431592887569251795991637)
              ·
                refine ⟨40213979151202169484277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3431592887569251795991637 40213979151202169484277)
                ·
                  rfl

theorem cell19_132159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_132159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132159 prefixEnd_132159 := by exact prefixLift 132159
  have htrace : WordTrace (prefixWord ++ tailWord_132159) baseStart_132159 baseEnd_132159 := by
    simpa [prefixWord, tailWord_132159, baseEnd_132159] using wordTrace_append hprefix tailTrace_132159
  have hstable : (prefixWord ++ tailWord_132159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132159).length < 2 ^ (prefixWord ++ tailWord_132159).sum := by decide
  have hdescent : baseEnd_132159 < baseStart_132159 := by decide
  rcases family_descends (prefixWord ++ tailWord_132159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132216 : List Nat := [2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_132216 : Nat := 118140960795 + 132216 * 2 ^ 59
def prefixEnd_132216 : Nat := 4983230072969 + 3 ^ 40 * 132216 * 2
def baseEnd_132216 : Nat := 40231323386642926217455

theorem tailTrace_132216 : CollatzResearch.WordTrace tailWord_132216 prefixEnd_132216 40231323386642926217455 := by
  unfold tailWord_132216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411156844505743770084251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3214875792674325026779001 2411156844505743770084251)
  ·
    refine ⟨3616735266758615655126377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2411156844505743770084251 3616735266758615655126377)
    ·
      refine ⟨2712551450068961741344783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3616735266758615655126377 2712551450068961741344783)
      ·
        refine ⟨4068827175103442612017175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712551450068961741344783 4068827175103442612017175)
        ·
          refine ⟨6103240762655163918025763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4068827175103442612017175 6103240762655163918025763)
          ·
            refine ⟨9154861143982745877038645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6103240762655163918025763 9154861143982745877038645)
            ·
              refine ⟨858268232248382425972373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9154861143982745877038645 858268232248382425972373)
              ·
                refine ⟨40231323386642926217455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858268232248382425972373 40231323386642926217455)
                ·
                  rfl

theorem cell19_132216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_132216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132216 prefixEnd_132216 := by exact prefixLift 132216
  have htrace : WordTrace (prefixWord ++ tailWord_132216) baseStart_132216 baseEnd_132216 := by
    simpa [prefixWord, tailWord_132216, baseEnd_132216] using wordTrace_append hprefix tailTrace_132216
  have hstable : (prefixWord ++ tailWord_132216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132216).length < 2 ^ (prefixWord ++ tailWord_132216).sum := by decide
  have hdescent : baseEnd_132216 < baseStart_132216 := by decide
  rcases family_descends (prefixWord ++ tailWord_132216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132288 : List Nat := [2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_132288 : Nat := 118140960795 + 132288 * 2 ^ 59
def prefixEnd_132288 : Nat := 4983230072969 + 3 ^ 40 * 132288 * 2
def baseEnd_132288 : Nat := 40253231894568092617259

theorem tailTrace_132288 : CollatzResearch.WordTrace tailWord_132288 prefixEnd_132288 40253231894568092617259 := by
  unfold tailWord_132288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412469872375321918394759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3216626496500429224526345 2412469872375321918394759)
  ·
    refine ⟨3618704808562982877592139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2412469872375321918394759 3618704808562982877592139)
    ·
      refine ⟨5428057212844474316388209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3618704808562982877592139 5428057212844474316388209)
      ·
        refine ⟨4071042909633355737291157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5428057212844474316388209 4071042909633355737291157)
        ·
          refine ⟨190830136389063550185523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4071042909633355737291157 190830136389063550185523)
          ·
            refine ⟨286245204583595325278285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190830136389063550185523 286245204583595325278285)
            ·
              refine ⟨107341951718848246979357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286245204583595325278285 107341951718848246979357)
              ·
                refine ⟨40253231894568092617259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107341951718848246979357 40253231894568092617259)
                ·
                  rfl

theorem cell19_132288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_132288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132288 prefixEnd_132288 := by exact prefixLift 132288
  have htrace : WordTrace (prefixWord ++ tailWord_132288) baseStart_132288 baseEnd_132288 := by
    simpa [prefixWord, tailWord_132288, baseEnd_132288] using wordTrace_append hprefix tailTrace_132288
  have hstable : (prefixWord ++ tailWord_132288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132288).length < 2 ^ (prefixWord ++ tailWord_132288).sum := by decide
  have hdescent : baseEnd_132288 < baseStart_132288 := by decide
  rcases family_descends (prefixWord ++ tailWord_132288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132309 : List Nat := [1, 3, 2, 4, 1, 2, 6]
def baseStart_132309 : Nat := 118140960795 + 132309 * 2 ^ 59
def prefixEnd_132309 : Nat := 4983230072969 + 3 ^ 40 * 132309 * 2
def baseEnd_132309 : Nat := 13419873958682088716845

theorem tailTrace_132309 : CollatzResearch.WordTrace tailWord_132309 prefixEnd_132309 13419873958682088716845 := by
  unfold tailWord_132309
  simp only [CollatzResearch.WordTrace]
  refine ⟨4825705677674564423303981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3217137118449709615535987 4825705677674564423303981)
  ·
    refine ⟨1809639629127961658738993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4825705677674564423303981 1809639629127961658738993)
    ·
      refine ⟨1357229721845971244054245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1809639629127961658738993 1357229721845971244054245)
      ·
        refine ⟨254480572846119608260171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1357229721845971244054245 254480572846119608260171)
        ·
          refine ⟨381720859269179412390257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254480572846119608260171 381720859269179412390257)
          ·
            refine ⟨286290644451884559292693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381720859269179412390257 286290644451884559292693)
            ·
              refine ⟨13419873958682088716845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286290644451884559292693 13419873958682088716845)
              ·
                rfl

theorem cell19_132309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_132309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132309 prefixEnd_132309 := by exact prefixLift 132309
  have htrace : WordTrace (prefixWord ++ tailWord_132309) baseStart_132309 baseEnd_132309 := by
    simpa [prefixWord, tailWord_132309, baseEnd_132309] using wordTrace_append hprefix tailTrace_132309
  have hstable : (prefixWord ++ tailWord_132309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132309).length < 2 ^ (prefixWord ++ tailWord_132309).sum := by decide
  have hdescent : baseEnd_132309 < baseStart_132309 := by decide
  rcases family_descends (prefixWord ++ tailWord_132309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132366 : List Nat := [4, 1, 1, 2, 1, 5, 5]
def baseStart_132366 : Nat := 118140960795 + 132366 * 2 ^ 59
def prefixEnd_132366 : Nat := 4983230072969 + 3 ^ 40 * 132366 * 2
def baseEnd_132366 : Nat := 13425655370495674294571

theorem tailTrace_132366 : CollatzResearch.WordTrace tailWord_132366 prefixEnd_132366 13425655370495674294571 := by
  unfold tailWord_132366
  simp only [CollatzResearch.WordTrace]
  refine ⟨603473079808507894766119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3218523092312042105419301 603473079808507894766119)
  ·
    refine ⟨905209619712761842149179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 603473079808507894766119 905209619712761842149179)
    ·
      refine ⟨1357814429569142763223769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 905209619712761842149179 1357814429569142763223769)
      ·
        refine ⟨1018360822176857072417827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1357814429569142763223769 1018360822176857072417827)
        ·
          refine ⟨1527541233265285608626741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018360822176857072417827 1527541233265285608626741)
          ·
            refine ⟨143206990618620525808757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1527541233265285608626741 143206990618620525808757)
            ·
              refine ⟨13425655370495674294571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143206990618620525808757 13425655370495674294571)
              ·
                rfl

theorem cell19_132366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_132366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132366 prefixEnd_132366 := by exact prefixLift 132366
  have htrace : WordTrace (prefixWord ++ tailWord_132366) baseStart_132366 baseEnd_132366 := by
    simpa [prefixWord, tailWord_132366, baseEnd_132366] using wordTrace_append hprefix tailTrace_132366
  have hstable : (prefixWord ++ tailWord_132366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132366).length < 2 ^ (prefixWord ++ tailWord_132366).sum := by decide
  have hdescent : baseEnd_132366 < baseStart_132366 := by decide
  rcases family_descends (prefixWord ++ tailWord_132366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132387 : List Nat := [1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_132387 : Nat := 118140960795 + 132387 * 2 ^ 59
def prefixEnd_132387 : Nat := 4983230072969 + 3 ^ 40 * 132387 * 2
def baseEnd_132387 : Nat := 40283356092965196416989

theorem tailTrace_132387 : CollatzResearch.WordTrace tailWord_132387 prefixEnd_132387 40283356092965196416989 := by
  unfold tailWord_132387
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828550571391983744643415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3219033714261322496428943 4828550571391983744643415)
  ·
    refine ⟨7242825857087975616965123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4828550571391983744643415 7242825857087975616965123)
    ·
      refine ⟨10864238785631963425447685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7242825857087975616965123 10864238785631963425447685)
      ·
        refine ⟨2037044772305993142271441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10864238785631963425447685 2037044772305993142271441)
        ·
          refine ⟨1527783579229494856703581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2037044772305993142271441 1527783579229494856703581)
          ·
            refine ⟨572918842211060571263843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1527783579229494856703581 572918842211060571263843)
            ·
              refine ⟨859378263316590856895765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572918842211060571263843 859378263316590856895765)
              ·
                refine ⟨40283356092965196416989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 859378263316590856895765 40283356092965196416989)
                ·
                  rfl

theorem cell19_132387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_132387 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132387 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132387 prefixEnd_132387 := by exact prefixLift 132387
  have htrace : WordTrace (prefixWord ++ tailWord_132387) baseStart_132387 baseEnd_132387 := by
    simpa [prefixWord, tailWord_132387, baseEnd_132387] using wordTrace_append hprefix tailTrace_132387
  have hstable : (prefixWord ++ tailWord_132387).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132387).length < 2 ^ (prefixWord ++ tailWord_132387).sum := by decide
  have hdescent : baseEnd_132387 < baseStart_132387 := by decide
  rcases family_descends (prefixWord ++ tailWord_132387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132404 : List Nat := [2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_132404 : Nat := 118140960795 + 132404 * 2 ^ 59
def prefixEnd_132404 : Nat := 4983230072969 + 3 ^ 40 * 132404 * 2
def baseEnd_132404 : Nat := 40288528935114194039165

theorem tailTrace_132404 : CollatzResearch.WordTrace tailWord_132404 prefixEnd_132404 40288528935114194039165 := by
  unfold tailWord_132404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414585306165197824006133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3219447074886930432008177 2414585306165197824006133)
  ·
    refine ⟨226367372452987296000575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2414585306165197824006133 226367372452987296000575)
    ·
      refine ⟨339551058679480944000863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226367372452987296000575 339551058679480944000863)
      ·
        refine ⟨509326588019221416001295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339551058679480944000863 509326588019221416001295)
        ·
          refine ⟨763989882028832124001943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509326588019221416001295 763989882028832124001943)
          ·
            refine ⟨1145984823043248186002915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763989882028832124001943 1145984823043248186002915)
            ·
              refine ⟨1718977234564872279004373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145984823043248186002915 1718977234564872279004373)
              ·
                refine ⟨40288528935114194039165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1718977234564872279004373 40288528935114194039165)
                ·
                  rfl

theorem cell19_132404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_132404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132404 prefixEnd_132404 := by exact prefixLift 132404
  have htrace : WordTrace (prefixWord ++ tailWord_132404) baseStart_132404 baseEnd_132404 := by
    simpa [prefixWord, tailWord_132404, baseEnd_132404] using wordTrace_append hprefix tailTrace_132404
  have hstable : (prefixWord ++ tailWord_132404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132404).length < 2 ^ (prefixWord ++ tailWord_132404).sum := by decide
  have hdescent : baseEnd_132404 < baseStart_132404 := by decide
  rcases family_descends (prefixWord ++ tailWord_132404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132537 : List Nat := [1, 2, 1, 4, 4, 2, 5]
def baseStart_132537 : Nat := 118140960795 + 132537 * 2 ^ 59
def prefixEnd_132537 : Nat := 4983230072969 + 3 ^ 40 * 132537 * 2
def baseEnd_132537 : Nat := 13442999605936431027749

theorem tailTrace_132537 : CollatzResearch.WordTrace tailWord_132537 prefixEnd_132537 13442999605936431027749 := by
  unfold tailWord_132537
  simp only [CollatzResearch.WordTrace]
  refine ⟨4834021520848559362603865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3222681013899039575069243 4834021520848559362603865)
  ·
    refine ⟨3625516140636419521952899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4834021520848559362603865 3625516140636419521952899)
    ·
      refine ⟨5438274210954629282929349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625516140636419521952899 5438274210954629282929349)
      ·
        refine ⟨1019676414553992990549253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5438274210954629282929349 1019676414553992990549253)
        ·
          refine ⟨191189327728873685727985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1019676414553992990549253 191189327728873685727985)
          ·
            refine ⟨143391995796655264295989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191189327728873685727985 143391995796655264295989)
            ·
              refine ⟨13442999605936431027749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143391995796655264295989 13442999605936431027749)
              ·
                rfl

theorem cell19_132537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_132537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132537 prefixEnd_132537 := by exact prefixLift 132537
  have htrace : WordTrace (prefixWord ++ tailWord_132537) baseStart_132537 baseEnd_132537 := by
    simpa [prefixWord, tailWord_132537, baseEnd_132537] using wordTrace_append hprefix tailTrace_132537
  have hstable : (prefixWord ++ tailWord_132537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132537).length < 2 ^ (prefixWord ++ tailWord_132537).sum := by decide
  have hdescent : baseEnd_132537 < baseStart_132537 := by decide
  rcases family_descends (prefixWord ++ tailWord_132537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132556 : List Nat := [2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_132556 : Nat := 118140960795 + 132556 * 2 ^ 59
def prefixEnd_132556 : Nat := 4983230072969 + 3 ^ 40 * 132556 * 2
def baseEnd_132556 : Nat := 40334780229622878660973

theorem tailTrace_132556 : CollatzResearch.WordTrace tailWord_132556 prefixEnd_132556 40334780229622878660973 := by
  unfold tailWord_132556
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417357253889862803772761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3223143005186483738363681 2417357253889862803772761)
  ·
    refine ⟨1813017940417397102829571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2417357253889862803772761 1813017940417397102829571)
    ·
      refine ⟨2719526910626095654244357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1813017940417397102829571 2719526910626095654244357)
      ·
        refine ⟨509911295742392935170817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2719526910626095654244357 509911295742392935170817)
        ·
          refine ⟨382433471806794701378113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509911295742392935170817 382433471806794701378113)
          ·
            refine ⟨286825103855096026033585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382433471806794701378113 286825103855096026033585)
            ·
              refine ⟨215118827891322019525189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286825103855096026033585 215118827891322019525189)
              ·
                refine ⟨40334780229622878660973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215118827891322019525189 40334780229622878660973)
                ·
                  rfl

theorem cell19_132556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_132556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132556 prefixEnd_132556 := by exact prefixLift 132556
  have htrace : WordTrace (prefixWord ++ tailWord_132556) baseStart_132556 baseEnd_132556 := by
    simpa [prefixWord, tailWord_132556, baseEnd_132556] using wordTrace_append hprefix tailTrace_132556
  have hstable : (prefixWord ++ tailWord_132556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132556).length < 2 ^ (prefixWord ++ tailWord_132556).sum := by decide
  have hdescent : baseEnd_132556 < baseStart_132556 := by decide
  rcases family_descends (prefixWord ++ tailWord_132556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132558 : List Nat := [4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_132558 : Nat := 118140960795 + 132558 * 2 ^ 59
def prefixEnd_132558 : Nat := 4983230072969 + 3 ^ 40 * 132558 * 2
def baseEnd_132558 : Nat := 40335388799287466616523

theorem tailTrace_132558 : CollatzResearch.WordTrace tailWord_132558 prefixEnd_132558 40335388799287466616523 := by
  unfold tailWord_132558
  simp only [CollatzResearch.WordTrace]
  refine ⟨604348431721559993639791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3223191635848319966078885 604348431721559993639791)
  ·
    refine ⟨906522647582339990459687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 604348431721559993639791 906522647582339990459687)
    ·
      refine ⟨1359783971373509985689531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906522647582339990459687 1359783971373509985689531)
      ·
        refine ⟨2039675957060264978534297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359783971373509985689531 2039675957060264978534297)
        ·
          refine ⟨1529756967795198733900723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2039675957060264978534297 1529756967795198733900723)
          ·
            refine ⟨2294635451692798100851085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529756967795198733900723 2294635451692798100851085)
            ·
              refine ⟨860488294384799287819157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2294635451692798100851085 860488294384799287819157)
              ·
                refine ⟨40335388799287466616523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 860488294384799287819157 40335388799287466616523)
                ·
                  rfl

theorem cell19_132558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_132558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132558 prefixEnd_132558 := by exact prefixLift 132558
  have htrace : WordTrace (prefixWord ++ tailWord_132558) baseStart_132558 baseEnd_132558 := by
    simpa [prefixWord, tailWord_132558, baseEnd_132558] using wordTrace_append hprefix tailTrace_132558
  have hstable : (prefixWord ++ tailWord_132558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132558).length < 2 ^ (prefixWord ++ tailWord_132558).sum := by decide
  have hdescent : baseEnd_132558 < baseStart_132558 := by decide
  rcases family_descends (prefixWord ++ tailWord_132558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132577 : List Nat := [1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_132577 : Nat := 118140960795 + 132577 * 2 ^ 59
def prefixEnd_132577 : Nat := 4983230072969 + 3 ^ 40 * 132577 * 2
def baseEnd_132577 : Nat := 40341170211101052194249

theorem tailTrace_132577 : CollatzResearch.WordTrace tailWord_132577 prefixEnd_132577 40341170211101052194249 := by
  unfold tailWord_132577
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835480440703646194059985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3223653627135764129373323 4835480440703646194059985)
  ·
    refine ⟨3626610330527734645544989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4835480440703646194059985 3626610330527734645544989)
    ·
      refine ⟨1359978873947900492079371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3626610330527734645544989 1359978873947900492079371)
      ·
        refine ⟨2039968310921850738119057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359978873947900492079371 2039968310921850738119057)
        ·
          refine ⟨1529976233191388053589293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2039968310921850738119057 1529976233191388053589293)
          ·
            refine ⟨573741087446770520095985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1529976233191388053589293 573741087446770520095985)
            ·
              refine ⟨430305815585077890071989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573741087446770520095985 430305815585077890071989)
              ·
                refine ⟨40341170211101052194249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 430305815585077890071989 40341170211101052194249)
                ·
                  rfl

theorem cell19_132577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_132577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132577 prefixEnd_132577 := by exact prefixLift 132577
  have htrace : WordTrace (prefixWord ++ tailWord_132577) baseStart_132577 baseEnd_132577 := by
    simpa [prefixWord, tailWord_132577, baseEnd_132577] using wordTrace_append hprefix tailTrace_132577
  have hstable : (prefixWord ++ tailWord_132577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132577).length < 2 ^ (prefixWord ++ tailWord_132577).sum := by decide
  have hdescent : baseEnd_132577 < baseStart_132577 := by decide
  rcases family_descends (prefixWord ++ tailWord_132577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132628 : List Nat := [2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_132628 : Nat := 118140960795 + 132628 * 2 ^ 59
def prefixEnd_132628 : Nat := 4983230072969 + 3 ^ 40 * 132628 * 2
def baseEnd_132628 : Nat := 40356688737548045060777

theorem tailTrace_132628 : CollatzResearch.WordTrace tailWord_132628 prefixEnd_132628 40356688737548045060777 := by
  unfold tailWord_132628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418670281759440952083269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3224893709012587936111025 2418670281759440952083269)
  ·
    refine ⟨453500677829895178515613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2418670281759440952083269 453500677829895178515613)
    ·
      refine ⟨170062754186210691943355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453500677829895178515613 170062754186210691943355)
      ·
        refine ⟨255094131279316037915033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170062754186210691943355 255094131279316037915033)
        ·
          refine ⟨191320598459487028436275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255094131279316037915033 191320598459487028436275)
          ·
            refine ⟨286980897689230542654413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191320598459487028436275 286980897689230542654413)
            ·
              refine ⟨107617836633461453495405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286980897689230542654413 107617836633461453495405)
              ·
                refine ⟨40356688737548045060777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107617836633461453495405 40356688737548045060777)
                ·
                  rfl

theorem cell19_132628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_132628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132628 prefixEnd_132628 := by exact prefixLift 132628
  have htrace : WordTrace (prefixWord ++ tailWord_132628) baseStart_132628 baseEnd_132628 := by
    simpa [prefixWord, tailWord_132628, baseEnd_132628] using wordTrace_append hprefix tailTrace_132628
  have hstable : (prefixWord ++ tailWord_132628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132628).length < 2 ^ (prefixWord ++ tailWord_132628).sum := by decide
  have hdescent : baseEnd_132628 < baseStart_132628 := by decide
  rcases family_descends (prefixWord ++ tailWord_132628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132685 : List Nat := [1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_132685 : Nat := 118140960795 + 132685 * 2 ^ 59
def prefixEnd_132685 : Nat := 4983230072969 + 3 ^ 40 * 132685 * 2
def baseEnd_132685 : Nat := 40374032972988801793955

theorem tailTrace_132685 : CollatzResearch.WordTrace tailWord_132685 prefixEnd_132685 40374032972988801793955 := by
  unfold tailWord_132685
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839419524312380638991509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3226279682874920425994339 4839419524312380638991509)
  ·
    refine ⟨226847790202142842452727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4839419524312380638991509 226847790202142842452727)
    ·
      refine ⟨340271685303214263679091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226847790202142842452727 340271685303214263679091)
      ·
        refine ⟨510407527954821395518637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340271685303214263679091 510407527954821395518637)
        ·
          refine ⟨191402822983058023319489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510407527954821395518637 191402822983058023319489)
          ·
            refine ⟨143552117237293517489617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191402822983058023319489 143552117237293517489617)
            ·
              refine ⟨107664087927970138117213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143552117237293517489617 107664087927970138117213)
              ·
                refine ⟨40374032972988801793955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107664087927970138117213 40374032972988801793955)
                ·
                  rfl

theorem cell19_132685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_132685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132685 prefixEnd_132685 := by exact prefixLift 132685
  have htrace : WordTrace (prefixWord ++ tailWord_132685) baseStart_132685 baseEnd_132685 := by
    simpa [prefixWord, tailWord_132685, baseEnd_132685] using wordTrace_append hprefix tailTrace_132685
  have hstable : (prefixWord ++ tailWord_132685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132685).length < 2 ^ (prefixWord ++ tailWord_132685).sum := by decide
  have hdescent : baseEnd_132685 < baseStart_132685 := by decide
  rcases family_descends (prefixWord ++ tailWord_132685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132729 : List Nat := [1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_132729 : Nat := 118140960795 + 132729 * 2 ^ 59
def prefixEnd_132729 : Nat := 4983230072969 + 3 ^ 40 * 132729 * 2
def baseEnd_132729 : Nat := 40387421505609736816057

theorem tailTrace_132729 : CollatzResearch.WordTrace tailWord_132729 prefixEnd_132729 40387421505609736816057 := by
  unfold tailWord_132729
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841024336152976153593241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3227349557435317435728827 4841024336152976153593241)
  ·
    refine ⟨3630768252114732115194931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4841024336152976153593241 3630768252114732115194931)
    ·
      refine ⟨5446152378172098172792397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630768252114732115194931 5446152378172098172792397)
      ·
        refine ⟨2042307141814536814797149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5446152378172098172792397 2042307141814536814797149)
        ·
          refine ⟨765865178180451305548931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2042307141814536814797149 765865178180451305548931)
          ·
            refine ⟨1148797767270676958323397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765865178180451305548931 1148797767270676958323397)
            ·
              refine ⟨215399581363251929685637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1148797767270676958323397 215399581363251929685637)
              ·
                refine ⟨40387421505609736816057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215399581363251929685637 40387421505609736816057)
                ·
                  rfl

theorem cell19_132729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_132729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132729 prefixEnd_132729 := by exact prefixLift 132729
  have htrace : WordTrace (prefixWord ++ tailWord_132729) baseStart_132729 baseEnd_132729 := by
    simpa [prefixWord, tailWord_132729, baseEnd_132729] using wordTrace_append hprefix tailTrace_132729
  have hstable : (prefixWord ++ tailWord_132729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132729).length < 2 ^ (prefixWord ++ tailWord_132729).sum := by decide
  have hdescent : baseEnd_132729 < baseStart_132729 := by decide
  rcases family_descends (prefixWord ++ tailWord_132729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132767 : List Nat := [1, 1, 2, 7, 8]
def baseStart_132767 : Nat := 118140960795 + 132767 * 2 ^ 59
def prefixEnd_132767 : Nat := 4983230072969 + 3 ^ 40 * 132767 * 2
def baseEnd_132767 : Nat := 1496258678860626221167

theorem tailTrace_132767 : CollatzResearch.WordTrace tailWord_132767 prefixEnd_132767 1496258678860626221167 := by
  unfold tailWord_132767
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842410310015308643476555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3228273540010205762317703 4842410310015308643476555)
  ·
    refine ⟨7263615465022962965214833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4842410310015308643476555 7263615465022962965214833)
    ·
      refine ⟨5447711598767222223911125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7263615465022962965214833 5447711598767222223911125)
      ·
        refine ⟨127680740596106770872917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5447711598767222223911125 127680740596106770872917)
        ·
          refine ⟨1496258678860626221167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 127680740596106770872917 1496258678860626221167)
          ·
            rfl

theorem cell19_132767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 8].length) (baseStart_132767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132767 prefixEnd_132767 := by exact prefixLift 132767
  have htrace : WordTrace (prefixWord ++ tailWord_132767) baseStart_132767 baseEnd_132767 := by
    simpa [prefixWord, tailWord_132767, baseEnd_132767] using wordTrace_append hprefix tailTrace_132767
  have hstable : (prefixWord ++ tailWord_132767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132767).length < 2 ^ (prefixWord ++ tailWord_132767).sum := by decide
  have hdescent : baseEnd_132767 < baseStart_132767 := by decide
  rcases family_descends (prefixWord ++ tailWord_132767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132786 : List Nat := [3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_132786 : Nat := 118140960795 + 132786 * 2 ^ 59
def prefixEnd_132786 : Nat := 4983230072969 + 3 ^ 40 * 132786 * 2
def baseEnd_132786 : Nat := 40404765741050493549235

theorem tailTrace_132786 : CollatzResearch.WordTrace tailWord_132786 prefixEnd_132786 40404765741050493549235 := by
  unfold tailWord_132786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210775824236618722104553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3228735531297649925612141 1210775824236618722104553)
  ·
    refine ⟨908081868177464041578415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1210775824236618722104553 908081868177464041578415)
    ·
      refine ⟨1362122802266196062367623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908081868177464041578415 1362122802266196062367623)
      ·
        refine ⟨2043184203399294093551435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362122802266196062367623 2043184203399294093551435)
        ·
          refine ⟨3064776305098941140327153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043184203399294093551435 3064776305098941140327153)
          ·
            refine ⟨2298582228824205855245365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3064776305098941140327153 2298582228824205855245365)
            ·
              refine ⟨215492083952269298929253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2298582228824205855245365 215492083952269298929253)
              ·
                refine ⟨40404765741050493549235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215492083952269298929253 40404765741050493549235)
                ·
                  rfl

theorem cell19_132786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_132786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132786 prefixEnd_132786 := by exact prefixLift 132786
  have htrace : WordTrace (prefixWord ++ tailWord_132786) baseStart_132786 baseEnd_132786 := by
    simpa [prefixWord, tailWord_132786, baseEnd_132786] using wordTrace_append hprefix tailTrace_132786
  have hstable : (prefixWord ++ tailWord_132786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132786).length < 2 ^ (prefixWord ++ tailWord_132786).sum := by decide
  have hdescent : baseEnd_132786 < baseStart_132786 := by decide
  rcases family_descends (prefixWord ++ tailWord_132786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132864 : List Nat := [2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_132864 : Nat := 118140960795 + 132864 * 2 ^ 59
def prefixEnd_132864 : Nat := 4983230072969 + 3 ^ 40 * 132864 * 2
def baseEnd_132864 : Nat := 40428499957969423815689

theorem tailTrace_132864 : CollatzResearch.WordTrace tailWord_132864 prefixEnd_132864 40428499957969423815689 := by
  unfold tailWord_132864
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422974095331947104878823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3230632127109262806505097 2422974095331947104878823)
  ·
    refine ⟨3634461142997920657318235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2422974095331947104878823 3634461142997920657318235)
    ·
      refine ⟨5451691714496880985977353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634461142997920657318235 5451691714496880985977353)
      ·
        refine ⟨4088768785872660739483015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5451691714496880985977353 4088768785872660739483015)
        ·
          refine ⟨6133153178808991109224523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088768785872660739483015 6133153178808991109224523)
          ·
            refine ⟨9199729768213486663836785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133153178808991109224523 9199729768213486663836785)
            ·
              refine ⟨6899797326160114997877589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9199729768213486663836785 6899797326160114997877589)
              ·
                refine ⟨40428499957969423815689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6899797326160114997877589 40428499957969423815689)
                ·
                  rfl

theorem cell19_132864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_132864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132864 prefixEnd_132864 := by exact prefixLift 132864
  have htrace : WordTrace (prefixWord ++ tailWord_132864) baseStart_132864 baseEnd_132864 := by
    simpa [prefixWord, tailWord_132864, baseEnd_132864] using wordTrace_append hprefix tailTrace_132864
  have hstable : (prefixWord ++ tailWord_132864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132864).length < 2 ^ (prefixWord ++ tailWord_132864).sum := by decide
  have hdescent : baseEnd_132864 < baseStart_132864 := by decide
  rcases family_descends (prefixWord ++ tailWord_132864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132894 : List Nat := [4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_132894 : Nat := 118140960795 + 132894 * 2 ^ 59
def prefixEnd_132894 : Nat := 4983230072969 + 3 ^ 40 * 132894 * 2
def baseEnd_132894 : Nat := 40437628502938243148941

theorem tailTrace_132894 : CollatzResearch.WordTrace tailWord_132894 prefixEnd_132894 40437628502938243148941 := by
  unfold tailWord_132894
  simp only [CollatzResearch.WordTrace]
  refine ⟨605880297569401166668717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3231361587036806222233157 605880297569401166668717)
  ·
    refine ⟨227205111588525437500769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 605880297569401166668717 227205111588525437500769)
    ·
      refine ⟨170403833691394078125577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227205111588525437500769 170403833691394078125577)
      ·
        refine ⟨127802875268545558594183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170403833691394078125577 127802875268545558594183)
        ·
          refine ⟨191704312902818337891275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127802875268545558594183 191704312902818337891275)
          ·
            refine ⟨287556469354227506836913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191704312902818337891275 287556469354227506836913)
            ·
              refine ⟨215667352015670630127685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287556469354227506836913 215667352015670630127685)
              ·
                refine ⟨40437628502938243148941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215667352015670630127685 40437628502938243148941)
                ·
                  rfl

theorem cell19_132894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_132894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132894 prefixEnd_132894 := by exact prefixLift 132894
  have htrace : WordTrace (prefixWord ++ tailWord_132894) baseStart_132894 baseEnd_132894 := by
    simpa [prefixWord, tailWord_132894, baseEnd_132894] using wordTrace_append hprefix tailTrace_132894
  have hstable : (prefixWord ++ tailWord_132894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132894).length < 2 ^ (prefixWord ++ tailWord_132894).sum := by decide
  have hdescent : baseEnd_132894 < baseStart_132894 := by decide
  rcases family_descends (prefixWord ++ tailWord_132894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132900 : List Nat := [2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_132900 : Nat := 118140960795 + 132900 * 2 ^ 59
def prefixEnd_132900 : Nat := 4983230072969 + 3 ^ 40 * 132900 * 2
def baseEnd_132900 : Nat := 40439454211932007015591

theorem tailTrace_132900 : CollatzResearch.WordTrace tailWord_132900 prefixEnd_132900 40439454211932007015591 := by
  unfold tailWord_132900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423630609266736179034077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3231507479022314905378769 2423630609266736179034077)
  ·
    refine ⟨908861478475026067137779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2423630609266736179034077 908861478475026067137779)
    ·
      refine ⟨1363292217712539100706669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908861478475026067137779 1363292217712539100706669)
      ·
        refine ⟨511234581642202162765001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1363292217712539100706669 511234581642202162765001)
        ·
          refine ⟨383425936231651622073751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511234581642202162765001 383425936231651622073751)
          ·
            refine ⟨575138904347477433110627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383425936231651622073751 575138904347477433110627)
            ·
              refine ⟨862708356521216149665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575138904347477433110627 862708356521216149665941)
              ·
                refine ⟨40439454211932007015591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 862708356521216149665941 40439454211932007015591)
                ·
                  rfl

theorem cell19_132900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_132900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132900 prefixEnd_132900 := by exact prefixLift 132900
  have htrace : WordTrace (prefixWord ++ tailWord_132900) baseStart_132900 baseEnd_132900 := by
    simpa [prefixWord, tailWord_132900, baseEnd_132900] using wordTrace_append hprefix tailTrace_132900
  have hstable : (prefixWord ++ tailWord_132900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132900).length < 2 ^ (prefixWord ++ tailWord_132900).sum := by decide
  have hdescent : baseEnd_132900 < baseStart_132900 := by decide
  rcases family_descends (prefixWord ++ tailWord_132900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132940 : List Nat := [2, 2, 1, 3, 11]
def baseStart_132940 : Nat := 118140960795 + 132940 * 2 ^ 59
def prefixEnd_132940 : Nat := 4983230072969 + 3 ^ 40 * 132940 * 2
def baseEnd_132940 : Nat := 1498208355749028375059

theorem tailTrace_132940 : CollatzResearch.WordTrace tailWord_132940 prefixEnd_132940 1498208355749028375059 := by
  unfold tailWord_132940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2424360069194279594762137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3232480092259039459682849 2424360069194279594762137)
  ·
    refine ⟨1818270051895709696071603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2424360069194279594762137 1818270051895709696071603)
    ·
      refine ⟨2727405077843564544107405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818270051895709696071603 2727405077843564544107405)
      ·
        refine ⟨1022776904191336704040277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2727405077843564544107405 1022776904191336704040277)
        ·
          refine ⟨1498208355749028375059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1022776904191336704040277 1498208355749028375059)
          ·
            rfl

theorem cell19_132940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 11].length) (baseStart_132940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132940 prefixEnd_132940 := by exact prefixLift 132940
  have htrace : WordTrace (prefixWord ++ tailWord_132940) baseStart_132940 baseEnd_132940 := by
    simpa [prefixWord, tailWord_132940, baseEnd_132940] using wordTrace_append hprefix tailTrace_132940
  have hstable : (prefixWord ++ tailWord_132940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132940).length < 2 ^ (prefixWord ++ tailWord_132940).sum := by decide
  have hdescent : baseEnd_132940 < baseStart_132940 := by decide
  rcases family_descends (prefixWord ++ tailWord_132940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132993 : List Nat := [1, 2, 4, 4, 1, 1, 6]
def baseStart_132993 : Nat := 118140960795 + 132993 * 2 ^ 59
def prefixEnd_132993 : Nat := 4983230072969 + 3 ^ 40 * 132993 * 2
def baseEnd_132993 : Nat := 13489250900445115649557

theorem tailTrace_132993 : CollatzResearch.WordTrace tailWord_132993 prefixEnd_132993 13489250900445115649557 := by
  unfold tailWord_132993
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850653207196549241203633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3233768804797699494135755 4850653207196549241203633)
  ·
    refine ⟨3637989905397411930902725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4850653207196549241203633 3637989905397411930902725)
    ·
      refine ⟨682123107262014737044261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3637989905397411930902725 682123107262014737044261)
      ·
        refine ⟨127898082611627763195799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682123107262014737044261 127898082611627763195799)
        ·
          refine ⟨191847123917441644793699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127898082611627763195799 191847123917441644793699)
          ·
            refine ⟨287770685876162467190549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191847123917441644793699 287770685876162467190549)
            ·
              refine ⟨13489250900445115649557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287770685876162467190549 13489250900445115649557)
              ·
                rfl

theorem cell19_132993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_132993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132993 prefixEnd_132993 := by exact prefixLift 132993
  have htrace : WordTrace (prefixWord ++ tailWord_132993) baseStart_132993 baseEnd_132993 := by
    simpa [prefixWord, tailWord_132993, baseEnd_132993] using wordTrace_append hprefix tailTrace_132993
  have hstable : (prefixWord ++ tailWord_132993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132993).length < 2 ^ (prefixWord ++ tailWord_132993).sum := by decide
  have hdescent : baseEnd_132993 < baseStart_132993 := by decide
  rcases family_descends (prefixWord ++ tailWord_132993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132997 : List Nat := [1, 3, 1, 1, 3, 2, 8]
def baseStart_132997 : Nat := 118140960795 + 132997 * 2 ^ 59
def prefixEnd_132997 : Nat := 4983230072969 + 3 ^ 40 * 132997 * 2
def baseEnd_132997 : Nat := 13489656613554840953257

theorem tailTrace_132997 : CollatzResearch.WordTrace tailWord_132997 prefixEnd_132997 13489656613554840953257 := by
  unfold tailWord_132997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850799099182057924349245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3233866066121371949566163 4850799099182057924349245)
  ·
    refine ⟨1819049662193271721630967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4850799099182057924349245 1819049662193271721630967)
    ·
      refine ⟨2728574493289907582446451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819049662193271721630967 2728574493289907582446451)
      ·
        refine ⟨4092861739934861373669677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728574493289907582446451 4092861739934861373669677)
        ·
          refine ⟨1534823152475573015126129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4092861739934861373669677 1534823152475573015126129)
          ·
            refine ⟨1151117364356679761344597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1534823152475573015126129 1151117364356679761344597)
            ·
              refine ⟨13489656613554840953257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1151117364356679761344597 13489656613554840953257)
              ·
                rfl

theorem cell19_132997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_132997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_132997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_132997 prefixEnd_132997 := by exact prefixLift 132997
  have htrace : WordTrace (prefixWord ++ tailWord_132997) baseStart_132997 baseEnd_132997 := by
    simpa [prefixWord, tailWord_132997, baseEnd_132997] using wordTrace_append hprefix tailTrace_132997
  have hstable : (prefixWord ++ tailWord_132997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132997).length < 2 ^ (prefixWord ++ tailWord_132997).sum := by decide
  have hdescent : baseEnd_132997 < baseStart_132997 := by decide
  rcases family_descends (prefixWord ++ tailWord_132997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133031 : List Nat := [1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_133031 : Nat := 118140960795 + 133031 * 2 ^ 59
def prefixEnd_133031 : Nat := 4983230072969 + 3 ^ 40 * 133031 * 2
def baseEnd_133031 : Nat := 40479315524962518104123

theorem tailTrace_133031 : CollatzResearch.WordTrace tailWord_133031 prefixEnd_133031 40479315524962518104123 := by
  unfold tailWord_133031
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852039181058881731086947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3234692787372587820724631 4852039181058881731086947)
  ·
    refine ⟨7278058771588322596630421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4852039181058881731086947 7278058771588322596630421)
    ·
      refine ⟨341159004918202621717051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7278058771588322596630421 341159004918202621717051)
      ·
        refine ⟨511738507377303932575577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341159004918202621717051 511738507377303932575577)
        ·
          refine ⟨383803880532977949431683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511738507377303932575577 383803880532977949431683)
          ·
            refine ⟨575705820799466924147525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383803880532977949431683 575705820799466924147525)
            ·
              refine ⟨107944841399900048277661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575705820799466924147525 107944841399900048277661)
              ·
                refine ⟨40479315524962518104123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107944841399900048277661 40479315524962518104123)
                ·
                  rfl

theorem cell19_133031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_133031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133031 prefixEnd_133031 := by exact prefixLift 133031
  have htrace : WordTrace (prefixWord ++ tailWord_133031) baseStart_133031 baseEnd_133031 := by
    simpa [prefixWord, tailWord_133031, baseEnd_133031] using wordTrace_append hprefix tailTrace_133031
  have hstable : (prefixWord ++ tailWord_133031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133031).length < 2 ^ (prefixWord ++ tailWord_133031).sum := by decide
  have hdescent : baseEnd_133031 < baseStart_133031 := by decide
  rcases family_descends (prefixWord ++ tailWord_133031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133092 : List Nat := [2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_133092 : Nat := 118140960795 + 133092 * 2 ^ 59
def prefixEnd_133092 : Nat := 4983230072969 + 3 ^ 40 * 133092 * 2
def baseEnd_133092 : Nat := 40497876899732450748401

theorem tailTrace_133092 : CollatzResearch.WordTrace tailWord_133092 prefixEnd_133092 40497876899732450748401 := by
  unfold tailWord_133092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427132016918944574528765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3236176022558592766038353 2427132016918944574528765)
  ·
    refine ⟨910174506344604215448287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2427132016918944574528765 910174506344604215448287)
    ·
      refine ⟨1365261759516906323172431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910174506344604215448287 1365261759516906323172431)
      ·
        refine ⟨2047892639275359484758647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365261759516906323172431 2047892639275359484758647)
        ·
          refine ⟨3071838958913039227137971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047892639275359484758647 3071838958913039227137971)
          ·
            refine ⟨4607758438369558840706957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071838958913039227137971 4607758438369558840706957)
            ·
              refine ⟨1727909414388584565265109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4607758438369558840706957 1727909414388584565265109)
              ·
                refine ⟨40497876899732450748401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1727909414388584565265109 40497876899732450748401)
                ·
                  rfl

theorem cell19_133092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_133092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133092 prefixEnd_133092 := by exact prefixLift 133092
  have htrace : WordTrace (prefixWord ++ tailWord_133092) baseStart_133092 baseEnd_133092 := by
    simpa [prefixWord, tailWord_133092, baseEnd_133092] using wordTrace_append hprefix tailTrace_133092
  have hstable : (prefixWord ++ tailWord_133092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133092).length < 2 ^ (prefixWord ++ tailWord_133092).sum := by decide
  have hdescent : baseEnd_133092 < baseStart_133092 := by decide
  rcases family_descends (prefixWord ++ tailWord_133092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133124 : List Nat := [2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_133124 : Nat := 118140960795 + 133124 * 2 ^ 59
def prefixEnd_133124 : Nat := 4983230072969 + 3 ^ 40 * 133124 * 2
def baseEnd_133124 : Nat := 40507614014365858037203

theorem tailTrace_133124 : CollatzResearch.WordTrace tailWord_133124 prefixEnd_133124 40507614014365858037203 := by
  unfold tailWord_133124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427715584860979307111213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3236954113147972409481617 2427715584860979307111213)
  ·
    refine ⟨910393344322867240166705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2427715584860979307111213 910393344322867240166705)
    ·
      refine ⟨682795008242150430125029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 910393344322867240166705 682795008242150430125029)
      ·
        refine ⟨128024064045403205648443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682795008242150430125029 128024064045403205648443)
        ·
          refine ⟨192036096068104808472665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128024064045403205648443 192036096068104808472665)
          ·
            refine ⟨144027072051078606354499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192036096068104808472665 144027072051078606354499)
            ·
              refine ⟨216040608076617909531749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144027072051078606354499 216040608076617909531749)
              ·
                refine ⟨40507614014365858037203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216040608076617909531749 40507614014365858037203)
                ·
                  rfl

theorem cell19_133124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_133124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133124 prefixEnd_133124 := by exact prefixLift 133124
  have htrace : WordTrace (prefixWord ++ tailWord_133124) baseStart_133124 baseEnd_133124 := by
    simpa [prefixWord, tailWord_133124, baseEnd_133124] using wordTrace_append hprefix tailTrace_133124
  have hstable : (prefixWord ++ tailWord_133124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133124).length < 2 ^ (prefixWord ++ tailWord_133124).sum := by decide
  have hdescent : baseEnd_133124 < baseStart_133124 := by decide
  rcases family_descends (prefixWord ++ tailWord_133124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133166 : List Nat := [4, 1, 3, 1, 1, 3, 6]
def baseStart_133166 : Nat := 118140960795 + 133166 * 2 ^ 59
def prefixEnd_133166 : Nat := 4983230072969 + 3 ^ 40 * 133166 * 2
def baseEnd_133166 : Nat := 13506797992440735034585

theorem tailTrace_133166 : CollatzResearch.WordTrace tailWord_133166 prefixEnd_133166 13506797992440735034585 := by
  unfold tailWord_133166
  simp only [CollatzResearch.WordTrace]
  refine ⟨607120379446224973406419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3237975357046533191500901 607120379446224973406419)
  ·
    refine ⟨910680569169337460109629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607120379446224973406419 910680569169337460109629)
    ·
      refine ⟨341505213438501547541111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 910680569169337460109629 341505213438501547541111)
      ·
        refine ⟨512257820157752321311667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341505213438501547541111 512257820157752321311667)
        ·
          refine ⟨768386730236628481967501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512257820157752321311667 768386730236628481967501)
          ·
            refine ⟨288145023838735680737813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768386730236628481967501 288145023838735680737813)
            ·
              refine ⟨13506797992440735034585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288145023838735680737813 13506797992440735034585)
              ·
                rfl

theorem cell19_133166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_133166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133166 prefixEnd_133166 := by exact prefixLift 133166
  have htrace : WordTrace (prefixWord ++ tailWord_133166) baseStart_133166 baseEnd_133166 := by
    simpa [prefixWord, tailWord_133166, baseEnd_133166] using wordTrace_append hprefix tailTrace_133166
  have hstable : (prefixWord ++ tailWord_133166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133166).length < 2 ^ (prefixWord ++ tailWord_133166).sum := by decide
  have hdescent : baseEnd_133166 < baseStart_133166 := by decide
  rcases family_descends (prefixWord ++ tailWord_133166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133168 : List Nat := [2, 1, 1, 1, 2, 6, 6]
def baseStart_133168 : Nat := 118140960795 + 133168 * 2 ^ 59
def prefixEnd_133168 : Nat := 4983230072969 + 3 ^ 40 * 133168 * 2
def baseEnd_133168 : Nat := 13507000848995597686435

theorem tailTrace_133168 : CollatzResearch.WordTrace tailWord_133168 prefixEnd_133168 13507000848995597686435 := by
  unfold tailWord_133168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428517990781277064412079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3238023987708369419216105 2428517990781277064412079)
  ·
    refine ⟨3642776986171915596618119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2428517990781277064412079 3642776986171915596618119)
    ·
      refine ⟨5464165479257873394927179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3642776986171915596618119 5464165479257873394927179)
      ·
        refine ⟨8196248218886810092390769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464165479257873394927179 8196248218886810092390769)
        ·
          refine ⟨6147186164165107569293077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8196248218886810092390769 6147186164165107569293077)
          ·
            refine ⟨288149351445239417310613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6147186164165107569293077 288149351445239417310613)
            ·
              refine ⟨13507000848995597686435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288149351445239417310613 13507000848995597686435)
              ·
                rfl

theorem cell19_133168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_133168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133168 prefixEnd_133168 := by exact prefixLift 133168
  have htrace : WordTrace (prefixWord ++ tailWord_133168) baseStart_133168 baseEnd_133168 := by
    simpa [prefixWord, tailWord_133168, baseEnd_133168] using wordTrace_append hprefix tailTrace_133168
  have hstable : (prefixWord ++ tailWord_133168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133168).length < 2 ^ (prefixWord ++ tailWord_133168).sum := by decide
  have hdescent : baseEnd_133168 < baseStart_133168 := by decide
  rcases family_descends (prefixWord ++ tailWord_133168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133244 : List Nat := [2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_133244 : Nat := 118140960795 + 133244 * 2 ^ 59
def prefixEnd_133244 : Nat := 4983230072969 + 3 ^ 40 * 133244 * 2
def baseEnd_133244 : Nat := 40544128194241135370209

theorem tailTrace_133244 : CollatzResearch.WordTrace tailWord_133244 prefixEnd_133244 40544128194241135370209 := by
  unfold tailWord_133244
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429903964643609554295393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3239871952858146072393857 2429903964643609554295393)
  ·
    refine ⟨1822427973482707165721545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2429903964643609554295393 1822427973482707165721545)
    ·
      refine ⟨1366820980112030374291159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1822427973482707165721545 1366820980112030374291159)
      ·
        refine ⟨2050231470168045561436739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366820980112030374291159 2050231470168045561436739)
        ·
          refine ⟨3075347205252068342155109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050231470168045561436739 3075347205252068342155109)
          ·
            refine ⟨576627600984762814154083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3075347205252068342155109 576627600984762814154083)
            ·
              refine ⟨864941401477144221231125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576627600984762814154083 864941401477144221231125)
              ·
                refine ⟨40544128194241135370209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 864941401477144221231125 40544128194241135370209)
                ·
                  rfl

theorem cell19_133244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_133244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133244 prefixEnd_133244 := by exact prefixLift 133244
  have htrace : WordTrace (prefixWord ++ tailWord_133244) baseStart_133244 baseEnd_133244 := by
    simpa [prefixWord, tailWord_133244, baseEnd_133244] using wordTrace_append hprefix tailTrace_133244
  have hstable : (prefixWord ++ tailWord_133244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133244).length < 2 ^ (prefixWord ++ tailWord_133244).sum := by decide
  have hdescent : baseEnd_133244 < baseStart_133244 := by decide
  rcases family_descends (prefixWord ++ tailWord_133244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133278 : List Nat := [4, 3, 1, 1, 4, 6]
def baseStart_133278 : Nat := 118140960795 + 133278 * 2 ^ 59
def prefixEnd_133278 : Nat := 4983230072969 + 3 ^ 40 * 133278 * 2
def baseEnd_133278 : Nat := 4506052653171014512729

theorem tailTrace_133278 : CollatzResearch.WordTrace tailWord_133278 prefixEnd_133278 4506052653171014512729 := by
  unfold tailWord_133278
  simp only [CollatzResearch.WordTrace]
  refine ⟨607631001395505364416061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3240698674109361943552325 607631001395505364416061)
  ·
    refine ⟨227861625523314511656023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 607631001395505364416061 227861625523314511656023)
    ·
      refine ⟨341792438284971767484035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227861625523314511656023 341792438284971767484035)
      ·
        refine ⟨512688657427457651226053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341792438284971767484035 512688657427457651226053)
        ·
          refine ⟨96129123267648309604885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512688657427457651226053 96129123267648309604885)
          ·
            refine ⟨4506052653171014512729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96129123267648309604885 4506052653171014512729)
            ·
              rfl

theorem cell19_133278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_133278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133278 prefixEnd_133278 := by exact prefixLift 133278
  have htrace : WordTrace (prefixWord ++ tailWord_133278) baseStart_133278 baseEnd_133278 := by
    simpa [prefixWord, tailWord_133278, baseEnd_133278] using wordTrace_append hprefix tailTrace_133278
  have hstable : (prefixWord ++ tailWord_133278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133278).length < 2 ^ (prefixWord ++ tailWord_133278).sum := by decide
  have hdescent : baseEnd_133278 < baseStart_133278 := by decide
  rcases family_descends (prefixWord ++ tailWord_133278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133297 : List Nat := [1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_133297 : Nat := 118140960795 + 133297 * 2 ^ 59
def prefixEnd_133297 : Nat := 4983230072969 + 3 ^ 40 * 133297 * 2
def baseEnd_133297 : Nat := 40560255290352716192287

theorem tailTrace_133297 : CollatzResearch.WordTrace tailWord_133297 prefixEnd_133297 40560255290352716192287 := by
  unfold tailWord_133297
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861740998095209160270145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3241160665396806106846763 4861740998095209160270145)
  ·
    refine ⟨3646305748571406870202609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4861740998095209160270145 3646305748571406870202609)
    ·
      refine ⟨2734729311428555152651957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3646305748571406870202609 2734729311428555152651957)
      ·
        refine ⟨256380872946427045561121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2734729311428555152651957 256380872946427045561121)
        ·
          refine ⟨192285654709820284170841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256380872946427045561121 192285654709820284170841)
          ·
            refine ⟨144214241032365213128131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192285654709820284170841 144214241032365213128131)
            ·
              refine ⟨216321361548547819692197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144214241032365213128131 216321361548547819692197)
              ·
                refine ⟨40560255290352716192287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216321361548547819692197 40560255290352716192287)
                ·
                  rfl

theorem cell19_133297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_133297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133297 prefixEnd_133297 := by exact prefixLift 133297
  have htrace : WordTrace (prefixWord ++ tailWord_133297) baseStart_133297 baseEnd_133297 := by
    simpa [prefixWord, tailWord_133297, baseEnd_133297] using wordTrace_append hprefix tailTrace_133297
  have hstable : (prefixWord ++ tailWord_133297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133297).length < 2 ^ (prefixWord ++ tailWord_133297).sum := by decide
  have hdescent : baseEnd_133297 < baseStart_133297 := by decide
  rcases family_descends (prefixWord ++ tailWord_133297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133316 : List Nat := [2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_133316 : Nat := 118140960795 + 133316 * 2 ^ 59
def prefixEnd_133316 : Nat := 4983230072969 + 3 ^ 40 * 133316 * 2
def baseEnd_133316 : Nat := 40566036702166301770013

theorem tailTrace_133316 : CollatzResearch.WordTrace tailWord_133316 prefixEnd_133316 40566036702166301770013 := by
  unfold tailWord_133316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431216992513187702605901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3241622656684250270141201 2431216992513187702605901)
  ·
    refine ⟨911706372192445388477213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2431216992513187702605901 911706372192445388477213)
    ·
      refine ⟨341889889572167020678955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 911706372192445388477213 341889889572167020678955)
      ·
        refine ⟨512834834358250531018433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341889889572167020678955 512834834358250531018433)
        ·
          refine ⟨384626125768687898263825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512834834358250531018433 384626125768687898263825)
          ·
            refine ⟨288469594326515923697869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384626125768687898263825 288469594326515923697869)
            ·
              refine ⟨108176097872443471386701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288469594326515923697869 108176097872443471386701)
              ·
                refine ⟨40566036702166301770013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108176097872443471386701 40566036702166301770013)
                ·
                  rfl

theorem cell19_133316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_133316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133316 prefixEnd_133316 := by exact prefixLift 133316
  have htrace : WordTrace (prefixWord ++ tailWord_133316) baseStart_133316 baseEnd_133316 := by
    simpa [prefixWord, tailWord_133316, baseEnd_133316] using wordTrace_append hprefix tailTrace_133316
  have hstable : (prefixWord ++ tailWord_133316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133316).length < 2 ^ (prefixWord ++ tailWord_133316).sum := by decide
  have hdescent : baseEnd_133316 < baseStart_133316 := by decide
  rcases family_descends (prefixWord ++ tailWord_133316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133358 : List Nat := [4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_133358 : Nat := 118140960795 + 133358 * 2 ^ 59
def prefixEnd_133358 : Nat := 4983230072969 + 3 ^ 40 * 133358 * 2
def baseEnd_133358 : Nat := 40578816665122648836565

theorem tailTrace_133358 : CollatzResearch.WordTrace tailWord_133358 prefixEnd_133358 40578816665122648836565 := by
  unfold tailWord_133358
  simp only [CollatzResearch.WordTrace]
  refine ⟨607995731359277072280091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3242643900582811052160485 607995731359277072280091)
  ·
    refine ⟨911993597038915608420137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607995731359277072280091 911993597038915608420137)
    ·
      refine ⟨683995197779186706315103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 911993597038915608420137 683995197779186706315103)
      ·
        refine ⟨1025992796668780059472655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683995197779186706315103 1025992796668780059472655)
        ·
          refine ⟨1538989195003170089208983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025992796668780059472655 1538989195003170089208983)
          ·
            refine ⟨2308483792504755133813475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538989195003170089208983 2308483792504755133813475)
            ·
              refine ⟨3462725688757132700720213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308483792504755133813475 3462725688757132700720213)
              ·
                refine ⟨40578816665122648836565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3462725688757132700720213 40578816665122648836565)
                ·
                  rfl

theorem cell19_133358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_133358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133358 prefixEnd_133358 := by exact prefixLift 133358
  have htrace : WordTrace (prefixWord ++ tailWord_133358) baseStart_133358 baseEnd_133358 := by
    simpa [prefixWord, tailWord_133358, baseEnd_133358] using wordTrace_append hprefix tailTrace_133358
  have hstable : (prefixWord ++ tailWord_133358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133358).length < 2 ^ (prefixWord ++ tailWord_133358).sum := by decide
  have hdescent : baseEnd_133358 < baseStart_133358 := by decide
  rcases family_descends (prefixWord ++ tailWord_133358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133377 : List Nat := [1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_133377 : Nat := 118140960795 + 133377 * 2 ^ 59
def prefixEnd_133377 : Nat := 4983230072969 + 3 ^ 40 * 133377 * 2
def baseEnd_133377 : Nat := 40584598076936234414291

theorem tailTrace_133377 : CollatzResearch.WordTrace tailWord_133377 prefixEnd_133377 40584598076936234414291 := by
  unfold tailWord_133377
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864658837805382823182385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3243105891870255215454923 4864658837805382823182385)
  ·
    refine ⟨3648494128354037117386789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4864658837805382823182385 3648494128354037117386789)
    ·
      refine ⟨684092649066381959510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3648494128354037117386789 684092649066381959510023)
      ·
        refine ⟨1026138973599572939265035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684092649066381959510023 1026138973599572939265035)
        ·
          refine ⟨1539208460399359408897553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026138973599572939265035 1539208460399359408897553)
          ·
            refine ⟨1154406345299519556673165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539208460399359408897553 1154406345299519556673165)
            ·
              refine ⟨432902379487319833752437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1154406345299519556673165 432902379487319833752437)
              ·
                refine ⟨40584598076936234414291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432902379487319833752437 40584598076936234414291)
                ·
                  rfl

theorem cell19_133377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_133377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133377 prefixEnd_133377 := by exact prefixLift 133377
  have htrace : WordTrace (prefixWord ++ tailWord_133377) baseStart_133377 baseEnd_133377 := by
    simpa [prefixWord, tailWord_133377, baseEnd_133377] using wordTrace_append hprefix tailTrace_133377
  have hstable : (prefixWord ++ tailWord_133377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133377).length < 2 ^ (prefixWord ++ tailWord_133377).sum := by decide
  have hdescent : baseEnd_133377 < baseStart_133377 := by decide
  rcases family_descends (prefixWord ++ tailWord_133377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133413 : List Nat := [1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_133413 : Nat := 118140960795 + 133413 * 2 ^ 59
def prefixEnd_133413 : Nat := 4983230072969 + 3 ^ 40 * 133413 * 2
def baseEnd_133413 : Nat := 40595552330898817614193

theorem tailTrace_133413 : CollatzResearch.WordTrace tailWord_133413 prefixEnd_133413 40595552330898817614193 := by
  unfold tailWord_133413
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865971865674960971492893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3243981243783307314328595 4865971865674960971492893)
  ·
    refine ⟨1824739449628110364309835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4865971865674960971492893 1824739449628110364309835)
    ·
      refine ⟨2737109174442165546464753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824739449628110364309835 2737109174442165546464753)
      ·
        refine ⟨2052831880831624159848565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2737109174442165546464753 2052831880831624159848565)
        ·
          refine ⟨192452988827964764985803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2052831880831624159848565 192452988827964764985803)
          ·
            refine ⟨288679483241947147478705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192452988827964764985803 288679483241947147478705)
            ·
              refine ⟨216509612431460360609029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288679483241947147478705 216509612431460360609029)
              ·
                refine ⟨40595552330898817614193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216509612431460360609029 40595552330898817614193)
                ·
                  rfl

theorem cell19_133413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_133413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133413 prefixEnd_133413 := by exact prefixLift 133413
  have htrace : WordTrace (prefixWord ++ tailWord_133413) baseStart_133413 baseEnd_133413 := by
    simpa [prefixWord, tailWord_133413, baseEnd_133413] using wordTrace_append hprefix tailTrace_133413
  have hstable : (prefixWord ++ tailWord_133413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133413).length < 2 ^ (prefixWord ++ tailWord_133413).sum := by decide
  have hdescent : baseEnd_133413 < baseStart_133413 := by decide
  rcases family_descends (prefixWord ++ tailWord_133413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133434 : List Nat := [3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_133434 : Nat := 118140960795 + 133434 * 2 ^ 59
def prefixEnd_133434 : Nat := 4983230072969 + 3 ^ 40 * 133434 * 2
def baseEnd_133434 : Nat := 40601942312376991147469

theorem tailTrace_133434 : CollatzResearch.WordTrace tailWord_133434 prefixEnd_133434 40601942312376991147469 := by
  unfold tailWord_133434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216684449649720389501839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3244491865732587705338237 1216684449649720389501839)
  ·
    refine ⟨1825026674474580584252759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216684449649720389501839 1825026674474580584252759)
    ·
      refine ⟨2737540011711870876379139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1825026674474580584252759 2737540011711870876379139)
      ·
        refine ⟨4106310017567806314568709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737540011711870876379139 4106310017567806314568709)
        ·
          refine ⟨769933128293963683981633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4106310017567806314568709 769933128293963683981633)
          ·
            refine ⟨577449846220472762986225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769933128293963683981633 577449846220472762986225)
            ·
              refine ⟨433087384665354572239669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577449846220472762986225 433087384665354572239669)
              ·
                refine ⟨40601942312376991147469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433087384665354572239669 40601942312376991147469)
                ·
                  rfl

theorem cell19_133434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_133434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133434 prefixEnd_133434 := by exact prefixLift 133434
  have htrace : WordTrace (prefixWord ++ tailWord_133434) baseStart_133434 baseEnd_133434 := by
    simpa [prefixWord, tailWord_133434, baseEnd_133434] using wordTrace_append hprefix tailTrace_133434
  have hstable : (prefixWord ++ tailWord_133434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133434).length < 2 ^ (prefixWord ++ tailWord_133434).sum := by decide
  have hdescent : baseEnd_133434 < baseStart_133434 := by decide
  rcases family_descends (prefixWord ++ tailWord_133434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133453 : List Nat := [1, 6, 1, 11]
def baseStart_133453 : Nat := 118140960795 + 133453 * 2 ^ 59
def prefixEnd_133453 : Nat := 4983230072969 + 3 ^ 40 * 133453 * 2
def baseEnd_133453 : Nat := 501329922520871317595

theorem tailTrace_133453 : CollatzResearch.WordTrace tailWord_133453 prefixEnd_133453 501329922520871317595 := by
  unfold tailWord_133453
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867430785530047802949013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3244953857020031868632675 4867430785530047802949013)
  ·
    refine ⟨228160818071720990763235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4867430785530047802949013 228160818071720990763235)
    ·
      refine ⟨342241227107581486144853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228160818071720990763235 342241227107581486144853)
      ·
        refine ⟨501329922520871317595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 342241227107581486144853 501329922520871317595)
        ·
          rfl

theorem cell19_133453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 11].length) (baseStart_133453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133453 prefixEnd_133453 := by exact prefixLift 133453
  have htrace : WordTrace (prefixWord ++ tailWord_133453) baseStart_133453 baseEnd_133453 := by
    simpa [prefixWord, tailWord_133453, baseEnd_133453] using wordTrace_append hprefix tailTrace_133453
  have hstable : (prefixWord ++ tailWord_133453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133453).length < 2 ^ (prefixWord ++ tailWord_133453).sum := by decide
  have hdescent : baseEnd_133453 < baseStart_133453 := by decide
  rcases family_descends (prefixWord ++ tailWord_133453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133506 : List Nat := [3, 4, 2, 1, 2, 1, 6]
def baseStart_133506 : Nat := 118140960795 + 133506 * 2 ^ 59
def prefixEnd_133506 : Nat := 4983230072969 + 3 ^ 40 * 133506 * 2
def baseEnd_133506 : Nat := 13541283606767385849091

theorem tailTrace_133506 : CollatzResearch.WordTrace tailWord_133506 prefixEnd_133506 13541283606767385849091 := by
  unfold tailWord_133506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1217340963584509463657093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3246242569558691903085581 1217340963584509463657093)
  ·
    refine ⟨228251430672095524435705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1217340963584509463657093 228251430672095524435705)
    ·
      refine ⟨171188573004071643326779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228251430672095524435705 171188573004071643326779)
      ·
        refine ⟨256782859506107464990169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171188573004071643326779 256782859506107464990169)
        ·
          refine ⟨192587144629580598742627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256782859506107464990169 192587144629580598742627)
          ·
            refine ⟨288880716944370898113941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192587144629580598742627 288880716944370898113941)
            ·
              refine ⟨13541283606767385849091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288880716944370898113941 13541283606767385849091)
              ·
                rfl

theorem cell19_133506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_133506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133506 prefixEnd_133506 := by exact prefixLift 133506
  have htrace : WordTrace (prefixWord ++ tailWord_133506) baseStart_133506 baseEnd_133506 := by
    simpa [prefixWord, tailWord_133506, baseEnd_133506] using wordTrace_append hprefix tailTrace_133506
  have hstable : (prefixWord ++ tailWord_133506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133506).length < 2 ^ (prefixWord ++ tailWord_133506).sum := by decide
  have hdescent : baseEnd_133506 < baseStart_133506 := by decide
  rcases family_descends (prefixWord ++ tailWord_133506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133544 : List Nat := [2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_133544 : Nat := 118140960795 + 133544 * 2 ^ 59
def prefixEnd_133544 : Nat := 4983230072969 + 3 ^ 40 * 133544 * 2
def baseEnd_133544 : Nat := 40635413643929328702725

theorem tailTrace_133544 : CollatzResearch.WordTrace tailWord_133544 prefixEnd_133544 40635413643929328702725 := by
  unfold tailWord_133544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435374914100185172255843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3247166552133580229674457 2435374914100185172255843)
  ·
    refine ⟨3653062371150277758383765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2435374914100185172255843 3653062371150277758383765)
    ·
      refine ⟨171237298647669269924239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3653062371150277758383765 171237298647669269924239)
      ·
        refine ⟨256855947971503904886359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171237298647669269924239 256855947971503904886359)
        ·
          refine ⟨385283921957255857329539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256855947971503904886359 385283921957255857329539)
          ·
            refine ⟨577925882935883785994309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385283921957255857329539 577925882935883785994309)
            ·
              refine ⟨108361103050478209873933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577925882935883785994309 108361103050478209873933)
              ·
                refine ⟨40635413643929328702725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108361103050478209873933 40635413643929328702725)
                ·
                  rfl

theorem cell19_133544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_133544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133544 prefixEnd_133544 := by exact prefixLift 133544
  have htrace : WordTrace (prefixWord ++ tailWord_133544) baseStart_133544 baseEnd_133544 := by
    simpa [prefixWord, tailWord_133544, baseEnd_133544] using wordTrace_append hprefix tailTrace_133544
  have hstable : (prefixWord ++ tailWord_133544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133544).length < 2 ^ (prefixWord ++ tailWord_133544).sum := by decide
  have hdescent : baseEnd_133544 < baseStart_133544 := by decide
  rcases family_descends (prefixWord ++ tailWord_133544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133639 : List Nat := [1, 1, 4, 3, 4, 1, 1, 4]
def baseStart_133639 : Nat := 118140960795 + 133639 * 2 ^ 59
def prefixEnd_133639 : Nat := 4983230072969 + 3 ^ 40 * 133639 * 2
def baseEnd_133639 : Nat := 40664320702997256591355

theorem tailTrace_133639 : CollatzResearch.WordTrace tailWord_133639 prefixEnd_133639 40664320702997256591355 := by
  unfold tailWord_133639
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874214762856201569219971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3249476508570801046146647 4874214762856201569219971)
  ·
    refine ⟨7311322144284302353829957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874214762856201569219971 7311322144284302353829957)
    ·
      refine ⟨1370872902053306691343117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7311322144284302353829957 1370872902053306691343117)
      ·
        refine ⟨514077338269990009253669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1370872902053306691343117 514077338269990009253669)
        ·
          refine ⟨96389500925623126735063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514077338269990009253669 96389500925623126735063)
          ·
            refine ⟨144584251388434690102595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96389500925623126735063 144584251388434690102595)
            ·
              refine ⟨216876377082652035153893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144584251388434690102595 216876377082652035153893)
              ·
                refine ⟨40664320702997256591355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216876377082652035153893 40664320702997256591355)
                ·
                  rfl

theorem cell19_133639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_133639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133639 prefixEnd_133639 := by exact prefixLift 133639
  have htrace : WordTrace (prefixWord ++ tailWord_133639) baseStart_133639 baseEnd_133639 := by
    simpa [prefixWord, tailWord_133639, baseEnd_133639] using wordTrace_append hprefix tailTrace_133639
  have hstable : (prefixWord ++ tailWord_133639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133639).length < 2 ^ (prefixWord ++ tailWord_133639).sum := by decide
  have hdescent : baseEnd_133639 < baseStart_133639 := by decide
  rcases family_descends (prefixWord ++ tailWord_133639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133643 : List Nat := [1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_133643 : Nat := 118140960795 + 133643 * 2 ^ 59
def prefixEnd_133643 : Nat := 4983230072969 + 3 ^ 40 * 133643 * 2
def baseEnd_133643 : Nat := 40665537842326432502455

theorem tailTrace_133643 : CollatzResearch.WordTrace tailWord_133643 prefixEnd_133643 40665537842326432502455 := by
  unfold tailWord_133643
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874360654841710252365583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3249573769894473501577055 4874360654841710252365583)
  ·
    refine ⟨7311540982262565378548375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874360654841710252365583 7311540982262565378548375)
    ·
      refine ⟨10967311473393848067822563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7311540982262565378548375 10967311473393848067822563)
      ·
        refine ⟨16450967210090772101733845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10967311473393848067822563 16450967210090772101733845)
        ·
          refine ⟨385569543986502471134387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16450967210090772101733845 385569543986502471134387)
          ·
            refine ⟨578354315979753706701581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385569543986502471134387 578354315979753706701581)
            ·
              refine ⟨216882868492407640013093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 578354315979753706701581 216882868492407640013093)
              ·
                refine ⟨40665537842326432502455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216882868492407640013093 40665537842326432502455)
                ·
                  rfl

theorem cell19_133643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_133643 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133643 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133643 prefixEnd_133643 := by exact prefixLift 133643
  have htrace : WordTrace (prefixWord ++ tailWord_133643) baseStart_133643 baseEnd_133643 := by
    simpa [prefixWord, tailWord_133643, baseEnd_133643] using wordTrace_append hprefix tailTrace_133643
  have hstable : (prefixWord ++ tailWord_133643).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133643).length < 2 ^ (prefixWord ++ tailWord_133643).sum := by decide
  have hdescent : baseEnd_133643 < baseStart_133643 := by decide
  rcases family_descends (prefixWord ++ tailWord_133643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133660 : List Nat := [2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_133660 : Nat := 118140960795 + 133660 * 2 ^ 59
def prefixEnd_133660 : Nat := 4983230072969 + 3 ^ 40 * 133660 * 2
def baseEnd_133660 : Nat := 40670710684475430124631

theorem tailTrace_133660 : CollatzResearch.WordTrace tailWord_133660 prefixEnd_133660 40670710684475430124631 := by
  unfold tailWord_133660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437490347890061077867217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3249987130520081437156289 2437490347890061077867217)
  ·
    refine ⟨1828117760917545808400413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2437490347890061077867217 1828117760917545808400413)
    ·
      refine ⟨685544160344079678150155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1828117760917545808400413 685544160344079678150155)
      ·
        refine ⟨1028316240516119517225233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685544160344079678150155 1028316240516119517225233)
        ·
          refine ⟨771237180387089637918925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028316240516119517225233 771237180387089637918925)
          ·
            refine ⟨289213942645158614219597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771237180387089637918925 289213942645158614219597)
            ·
              refine ⟨108455228491934480332349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289213942645158614219597 108455228491934480332349)
              ·
                refine ⟨40670710684475430124631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108455228491934480332349 40670710684475430124631)
                ·
                  rfl

theorem cell19_133660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_133660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133660 prefixEnd_133660 := by exact prefixLift 133660
  have htrace : WordTrace (prefixWord ++ tailWord_133660) baseStart_133660 baseEnd_133660 := by
    simpa [prefixWord, tailWord_133660, baseEnd_133660] using wordTrace_append hprefix tailTrace_133660
  have hstable : (prefixWord ++ tailWord_133660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133660).length < 2 ^ (prefixWord ++ tailWord_133660).sum := by decide
  have hdescent : baseEnd_133660 < baseStart_133660 := by decide
  rcases family_descends (prefixWord ++ tailWord_133660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133683 : List Nat := [1, 1, 1, 2, 4, 2, 8]
def baseStart_133683 : Nat := 118140960795 + 133683 * 2 ^ 59
def prefixEnd_133683 : Nat := 4983230072969 + 3 ^ 40 * 133683 * 2
def baseEnd_133683 : Nat := 13559236411872730537819

theorem tailTrace_133683 : CollatzResearch.WordTrace tailWord_133683 prefixEnd_133683 13559236411872730537819 := by
  unfold tailWord_133683
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875819574696797083821703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3250546383131198055881135 4875819574696797083821703)
  ·
    refine ⟨7313729362045195625732555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4875819574696797083821703 7313729362045195625732555)
    ·
      refine ⟨10970594043067793438598833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7313729362045195625732555 10970594043067793438598833)
      ·
        refine ⟨8227945532300845078949125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10970594043067793438598833 8227945532300845078949125)
        ·
          refine ⟨1542739787306408452302961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8227945532300845078949125 1542739787306408452302961)
          ·
            refine ⟨1157054840479806339227221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542739787306408452302961 1157054840479806339227221)
            ·
              refine ⟨13559236411872730537819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1157054840479806339227221 13559236411872730537819)
              ·
                rfl

theorem cell19_133683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_133683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133683 prefixEnd_133683 := by exact prefixLift 133683
  have htrace : WordTrace (prefixWord ++ tailWord_133683) baseStart_133683 baseEnd_133683 := by
    simpa [prefixWord, tailWord_133683, baseEnd_133683] using wordTrace_append hprefix tailTrace_133683
  have hstable : (prefixWord ++ tailWord_133683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133683).length < 2 ^ (prefixWord ++ tailWord_133683).sum := by decide
  have hdescent : baseEnd_133683 < baseStart_133683 := by decide
  rcases family_descends (prefixWord ++ tailWord_133683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133736 : List Nat := [2, 1, 4, 3, 2, 2, 5]
def baseStart_133736 : Nat := 118140960795 + 133736 * 2 ^ 59
def prefixEnd_133736 : Nat := 4983230072969 + 3 ^ 40 * 133736 * 2
def baseEnd_133736 : Nat := 13564612110576590811845

theorem tailTrace_133736 : CollatzResearch.WordTrace tailWord_133736 prefixEnd_133736 13564612110576590811845 := by
  unfold tailWord_133736
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438876321752393567750531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3251835095669858090334041 2438876321752393567750531)
  ·
    refine ⟨3658314482628590351625797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2438876321752393567750531 3658314482628590351625797)
    ·
      refine ⟨685933965492860690929837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3658314482628590351625797 685933965492860690929837)
      ·
        refine ⟨257225237059822759098689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685933965492860690929837 257225237059822759098689)
        ·
          refine ⟨192918927794867069324017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257225237059822759098689 192918927794867069324017)
          ·
            refine ⟨144689195846150301993013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192918927794867069324017 144689195846150301993013)
            ·
              refine ⟨13564612110576590811845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144689195846150301993013 13564612110576590811845)
              ·
                rfl

theorem cell19_133736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_133736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133736 prefixEnd_133736 := by exact prefixLift 133736
  have htrace : WordTrace (prefixWord ++ tailWord_133736) baseStart_133736 baseEnd_133736 := by
    simpa [prefixWord, tailWord_133736, baseEnd_133736] using wordTrace_append hprefix tailTrace_133736
  have hstable : (prefixWord ++ tailWord_133736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133736).length < 2 ^ (prefixWord ++ tailWord_133736).sum := by decide
  have hdescent : baseEnd_133736 < baseStart_133736 := by decide
  rcases family_descends (prefixWord ++ tailWord_133736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133740 : List Nat := [2, 2, 1, 1, 3, 1, 9]
def baseStart_133740 : Nat := 118140960795 + 133740 * 2 ^ 59
def prefixEnd_133740 : Nat := 4983230072969 + 3 ^ 40 * 133740 * 2
def baseEnd_133740 : Nat := 13565017823686316115545

theorem tailTrace_133740 : CollatzResearch.WordTrace tailWord_133740 prefixEnd_133740 13565017823686316115545 := by
  unfold tailWord_133740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438949267745147909323337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3251932356993530545764449 2438949267745147909323337)
  ·
    refine ⟨1829211950808860931992503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2438949267745147909323337 1829211950808860931992503)
    ·
      refine ⟨2743817926213291397988755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1829211950808860931992503 2743817926213291397988755)
      ·
        refine ⟨4115726889319937096983133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743817926213291397988755 4115726889319937096983133)
        ·
          refine ⟨1543397583494976411368675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4115726889319937096983133 1543397583494976411368675)
          ·
            refine ⟨2315096375242464617053013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543397583494976411368675 2315096375242464617053013)
            ·
              refine ⟨13565017823686316115545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2315096375242464617053013 13565017823686316115545)
              ·
                rfl

theorem cell19_133740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_133740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133740 prefixEnd_133740 := by exact prefixLift 133740
  have htrace : WordTrace (prefixWord ++ tailWord_133740) baseStart_133740 baseEnd_133740 := by
    simpa [prefixWord, tailWord_133740, baseEnd_133740] using wordTrace_append hprefix tailTrace_133740
  have hstable : (prefixWord ++ tailWord_133740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133740).length < 2 ^ (prefixWord ++ tailWord_133740).sum := by decide
  have hdescent : baseEnd_133740 < baseStart_133740 := by decide
  rcases family_descends (prefixWord ++ tailWord_133740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133873 : List Nat := [1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_133873 : Nat := 118140960795 + 133873 * 2 ^ 59
def prefixEnd_133873 : Nat := 4983230072969 + 3 ^ 40 * 133873 * 2
def baseEnd_133873 : Nat := 40735523353754047390717

theorem tailTrace_133873 : CollatzResearch.WordTrace tailWord_133873 prefixEnd_133873 40735523353754047390717 := by
  unfold tailWord_133873
  simp only [CollatzResearch.WordTrace]
  refine ⟨4882749444008459533238273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3255166296005639688825515 4882749444008459533238273)
  ·
    refine ⟨3662062083006344649928705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4882749444008459533238273 3662062083006344649928705)
    ·
      refine ⟨2746546562254758487446529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3662062083006344649928705 2746546562254758487446529)
      ·
        refine ⟨2059909921691068865584897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2746546562254758487446529 2059909921691068865584897)
        ·
          refine ⟨1544932441268301649188673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2059909921691068865584897 1544932441268301649188673)
          ·
            refine ⟨1158699330951226236891505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544932441268301649188673 1158699330951226236891505)
            ·
              refine ⟨869024498213419677668629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158699330951226236891505 869024498213419677668629)
              ·
                refine ⟨40735523353754047390717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 869024498213419677668629 40735523353754047390717)
                ·
                  rfl

theorem cell19_133873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_133873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133873 prefixEnd_133873 := by exact prefixLift 133873
  have htrace : WordTrace (prefixWord ++ tailWord_133873) baseStart_133873 baseEnd_133873 := by
    simpa [prefixWord, tailWord_133873, baseEnd_133873] using wordTrace_append hprefix tailTrace_133873
  have hstable : (prefixWord ++ tailWord_133873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133873).length < 2 ^ (prefixWord ++ tailWord_133873).sum := by decide
  have hdescent : baseEnd_133873 < baseStart_133873 := by decide
  rcases family_descends (prefixWord ++ tailWord_133873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133886 : List Nat := [4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_133886 : Nat := 118140960795 + 133886 * 2 ^ 59
def prefixEnd_133886 : Nat := 4983230072969 + 3 ^ 40 * 133886 * 2
def baseEnd_133886 : Nat := 40739479056573869101793

theorem tailTrace_133886 : CollatzResearch.WordTrace tailWord_133886 prefixEnd_133886 40739479056573869101793 := by
  unfold tailWord_133886
  simp only [CollatzResearch.WordTrace]
  refine ⟨610402949120170344182689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3255482395307575168974341 610402949120170344182689)
  ·
    refine ⟨457802211840127758137017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 610402949120170344182689 457802211840127758137017)
    ·
      refine ⟨343351658880095818602763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457802211840127758137017 343351658880095818602763)
      ·
        refine ⟨515027488320143727904145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343351658880095818602763 515027488320143727904145)
        ·
          refine ⟨386270616240107795928109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515027488320143727904145 386270616240107795928109)
          ·
            refine ⟨144851481090040423473041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386270616240107795928109 144851481090040423473041)
            ·
              refine ⟨108638610817530317604781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144851481090040423473041 108638610817530317604781)
              ·
                refine ⟨40739479056573869101793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108638610817530317604781 40739479056573869101793)
                ·
                  rfl

theorem cell19_133886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_133886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133886 prefixEnd_133886 := by exact prefixLift 133886
  have htrace : WordTrace (prefixWord ++ tailWord_133886) baseStart_133886 baseEnd_133886 := by
    simpa [prefixWord, tailWord_133886, baseEnd_133886] using wordTrace_append hprefix tailTrace_133886
  have hstable : (prefixWord ++ tailWord_133886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133886).length < 2 ^ (prefixWord ++ tailWord_133886).sum := by decide
  have hdescent : baseEnd_133886 < baseStart_133886 := by decide
  rcases family_descends (prefixWord ++ tailWord_133886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133928 : List Nat := [2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_133928 : Nat := 118140960795 + 133928 * 2 ^ 59
def prefixEnd_133928 : Nat := 4983230072969 + 3 ^ 40 * 133928 * 2
def baseEnd_133928 : Nat := 40752259019530216168345

theorem tailTrace_133928 : CollatzResearch.WordTrace tailWord_133928 prefixEnd_133928 40752259019530216168345 := by
  unfold tailWord_133928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442377729404601963245219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3256503639206135950993625 2442377729404601963245219)
  ·
    refine ⟨3663566594106902944867829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2442377729404601963245219 3663566594106902944867829)
    ·
      refine ⟨343459368197522151081359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3663566594106902944867829 343459368197522151081359)
      ·
        refine ⟨515189052296283226622039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343459368197522151081359 515189052296283226622039)
        ·
          refine ⟨772783578444424839933059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515189052296283226622039 772783578444424839933059)
          ·
            refine ⟨1159175367666637259899589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772783578444424839933059 1159175367666637259899589)
            ·
              refine ⟨217345381437494486231173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1159175367666637259899589 217345381437494486231173)
              ·
                refine ⟨40752259019530216168345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217345381437494486231173 40752259019530216168345)
                ·
                  rfl

theorem cell19_133928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_133928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_133928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_133928 prefixEnd_133928 := by exact prefixLift 133928
  have htrace : WordTrace (prefixWord ++ tailWord_133928) baseStart_133928 baseEnd_133928 := by
    simpa [prefixWord, tailWord_133928, baseEnd_133928] using wordTrace_append hprefix tailTrace_133928
  have hstable : (prefixWord ++ tailWord_133928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133928).length < 2 ^ (prefixWord ++ tailWord_133928).sum := by decide
  have hdescent : baseEnd_133928 < baseStart_133928 := by decide
  rcases family_descends (prefixWord ++ tailWord_133928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134025 : List Nat := [1, 2, 1, 1, 5, 3, 6]
def baseStart_134025 : Nat := 118140960795 + 134025 * 2 ^ 59
def prefixEnd_134025 : Nat := 4983230072969 + 3 ^ 40 * 134025 * 2
def baseEnd_134025 : Nat := 13593924882754244004175

theorem tailTrace_134025 : CollatzResearch.WordTrace tailWord_134025 prefixEnd_134025 13593924882754244004175 := by
  unfold tailWord_134025
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888293339457789492771529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3258862226305192995181019 4888293339457789492771529)
  ·
    refine ⟨3666220004593342119578647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4888293339457789492771529 3666220004593342119578647)
    ·
      refine ⟨5499330006890013179367971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666220004593342119578647 5499330006890013179367971)
      ·
        refine ⟨8248995010335019769051957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5499330006890013179367971 8248995010335019769051957)
        ·
          refine ⟨773343282218908103348621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8248995010335019769051957 773343282218908103348621)
          ·
            refine ⟨290003730832090538755733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 773343282218908103348621 290003730832090538755733)
            ·
              refine ⟨13593924882754244004175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 290003730832090538755733 13593924882754244004175)
              ·
                rfl

theorem cell19_134025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_134025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134025 prefixEnd_134025 := by exact prefixLift 134025
  have htrace : WordTrace (prefixWord ++ tailWord_134025) baseStart_134025 baseEnd_134025 := by
    simpa [prefixWord, tailWord_134025, baseEnd_134025] using wordTrace_append hprefix tailTrace_134025
  have hstable : (prefixWord ++ tailWord_134025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134025).length < 2 ^ (prefixWord ++ tailWord_134025).sum := by decide
  have hdescent : baseEnd_134025 < baseStart_134025 := by decide
  rcases family_descends (prefixWord ++ tailWord_134025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134093 : List Nat := [1, 6, 3, 1, 1, 1, 2, 4]
def baseStart_134093 : Nat := 118140960795 + 134093 * 2 ^ 59
def prefixEnd_134093 : Nat := 4983230072969 + 3 ^ 40 * 134093 * 2
def baseEnd_134093 : Nat := 40802466016858722501229

theorem tailTrace_134093 : CollatzResearch.WordTrace tailWord_134093 prefixEnd_134093 40802466016858722501229 := by
  unfold tailWord_134093
  simp only [CollatzResearch.WordTrace]
  refine ⟨4890773503211437106246933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3260515668807624737497955 4890773503211437106246933)
  ·
    refine ⟨229255007963036114355325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4890773503211437106246933 229255007963036114355325)
    ·
      refine ⟨85970627986138542883247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229255007963036114355325 85970627986138542883247)
      ·
        refine ⟨128955941979207814324871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85970627986138542883247 128955941979207814324871)
        ·
          refine ⟨193433912968811721487307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128955941979207814324871 193433912968811721487307)
          ·
            refine ⟨290150869453217582230961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193433912968811721487307 290150869453217582230961)
            ·
              refine ⟨217613152089913186673221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290150869453217582230961 217613152089913186673221)
              ·
                refine ⟨40802466016858722501229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217613152089913186673221 40802466016858722501229)
                ·
                  rfl

theorem cell19_134093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_134093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134093 prefixEnd_134093 := by exact prefixLift 134093
  have htrace : WordTrace (prefixWord ++ tailWord_134093) baseStart_134093 baseEnd_134093 := by
    simpa [prefixWord, tailWord_134093, baseEnd_134093] using wordTrace_append hprefix tailTrace_134093
  have hstable : (prefixWord ++ tailWord_134093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134093).length < 2 ^ (prefixWord ++ tailWord_134093).sum := by decide
  have hdescent : baseEnd_134093 < baseStart_134093 := by decide
  rcases family_descends (prefixWord ++ tailWord_134093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134120 : List Nat := [2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_134120 : Nat := 118140960795 + 134120 * 2 ^ 59
def prefixEnd_134120 : Nat := 4983230072969 + 3 ^ 40 * 134120 * 2
def baseEnd_134120 : Nat := 40810681707330659901155

theorem tailTrace_134120 : CollatzResearch.WordTrace tailWord_134120 prefixEnd_134120 40810681707330659901155 := by
  unfold tailWord_134120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445879137056810358739907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3261172182742413811653209 2445879137056810358739907)
  ·
    refine ⟨3668818705585215538109861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2445879137056810358739907 3668818705585215538109861)
    ·
      refine ⟨687903507297227913395599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3668818705585215538109861 687903507297227913395599)
      ·
        refine ⟨1031855260945841870093399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687903507297227913395599 1031855260945841870093399)
        ·
          refine ⟨1547782891418762805140099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031855260945841870093399 1547782891418762805140099)
          ·
            refine ⟨2321674337128144207710149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547782891418762805140099 2321674337128144207710149)
            ·
              refine ⟨435313938211527038945653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2321674337128144207710149 435313938211527038945653)
              ·
                refine ⟨40810681707330659901155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435313938211527038945653 40810681707330659901155)
                ·
                  rfl

theorem cell19_134120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_134120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134120 prefixEnd_134120 := by exact prefixLift 134120
  have htrace : WordTrace (prefixWord ++ tailWord_134120) baseStart_134120 baseEnd_134120 := by
    simpa [prefixWord, tailWord_134120, baseEnd_134120] using wordTrace_append hprefix tailTrace_134120
  have hstable : (prefixWord ++ tailWord_134120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134120).length < 2 ^ (prefixWord ++ tailWord_134120).sum := by decide
  have hdescent : baseEnd_134120 < baseStart_134120 := by decide
  rcases family_descends (prefixWord ++ tailWord_134120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134156 : List Nat := [2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_134156 : Nat := 118140960795 + 134156 * 2 ^ 59
def prefixEnd_134156 : Nat := 4983230072969 + 3 ^ 40 * 134156 * 2
def baseEnd_134156 : Nat := 40821635961293243101057

theorem tailTrace_134156 : CollatzResearch.WordTrace tailWord_134156 prefixEnd_134156 40821635961293243101057 := by
  unfold tailWord_134156
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446535650991599432895161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3262047534655465910526881 2446535650991599432895161)
  ·
    refine ⟨1834901738243699574671371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2446535650991599432895161 1834901738243699574671371)
    ·
      refine ⟨2752352607365549362007057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1834901738243699574671371 2752352607365549362007057)
      ·
        refine ⟨2064264455524162021505293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2752352607365549362007057 2064264455524162021505293)
        ·
          refine ⟨774099170821560758064485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2064264455524162021505293 774099170821560758064485)
          ·
            refine ⟨145143594529042642137091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 774099170821560758064485 145143594529042642137091)
            ·
              refine ⟨217715391793563963205637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145143594529042642137091 217715391793563963205637)
              ·
                refine ⟨40821635961293243101057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217715391793563963205637 40821635961293243101057)
                ·
                  rfl

theorem cell19_134156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_134156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134156 prefixEnd_134156 := by exact prefixLift 134156
  have htrace : WordTrace (prefixWord ++ tailWord_134156) baseStart_134156 baseEnd_134156 := by
    simpa [prefixWord, tailWord_134156, baseEnd_134156] using wordTrace_append hprefix tailTrace_134156
  have hstable : (prefixWord ++ tailWord_134156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134156).length < 2 ^ (prefixWord ++ tailWord_134156).sum := by decide
  have hdescent : baseEnd_134156 < baseStart_134156 := by decide
  rcases family_descends (prefixWord ++ tailWord_134156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134173 : List Nat := [1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_134173 : Nat := 118140960795 + 134173 * 2 ^ 59
def prefixEnd_134173 : Nat := 4983230072969 + 3 ^ 40 * 134173 * 2
def baseEnd_134173 : Nat := 40826808803442240723233

theorem tailTrace_134173 : CollatzResearch.WordTrace tailWord_134173 prefixEnd_134173 40826808803442240723233 := by
  unfold tailWord_134173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893691342921610769159173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3262460895281073846106115 4893691342921610769159173)
  ·
    refine ⟨917567126797802019217345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4893691342921610769159173 917567126797802019217345)
    ·
      refine ⟨688175345098351514413009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 917567126797802019217345 688175345098351514413009)
      ·
        refine ⟨516131508823763635809757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688175345098351514413009 516131508823763635809757)
        ·
          refine ⟨193549315808911363428659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516131508823763635809757 193549315808911363428659)
          ·
            refine ⟨290323973713367045142989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193549315808911363428659 290323973713367045142989)
            ·
              refine ⟨108871490142512641928621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290323973713367045142989 108871490142512641928621)
              ·
                refine ⟨40826808803442240723233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108871490142512641928621 40826808803442240723233)
                ·
                  rfl

theorem cell19_134173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_134173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134173 prefixEnd_134173 := by exact prefixLift 134173
  have htrace : WordTrace (prefixWord ++ tailWord_134173) baseStart_134173 baseEnd_134173 := by
    simpa [prefixWord, tailWord_134173, baseEnd_134173] using wordTrace_append hprefix tailTrace_134173
  have hstable : (prefixWord ++ tailWord_134173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134173).length < 2 ^ (prefixWord ++ tailWord_134173).sum := by decide
  have hdescent : baseEnd_134173 < baseStart_134173 := by decide
  rcases family_descends (prefixWord ++ tailWord_134173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134175 : List Nat := [1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_134175 : Nat := 118140960795 + 134175 * 2 ^ 59
def prefixEnd_134175 : Nat := 4983230072969 + 3 ^ 40 * 134175 * 2
def baseEnd_134175 : Nat := 40827417373106828678783

theorem tailTrace_134175 : CollatzResearch.WordTrace tailWord_134175 prefixEnd_134175 40827417373106828678783 := by
  unfold tailWord_134175
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893764288914365110731979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3262509525942910073821319 4893764288914365110731979)
  ·
    refine ⟨7340646433371547666097969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4893764288914365110731979 7340646433371547666097969)
    ·
      refine ⟨5505484825028660749573477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7340646433371547666097969 5505484825028660749573477)
      ·
        refine ⟨1032278404692873890545027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5505484825028660749573477 1032278404692873890545027)
        ·
          refine ⟨1548417607039310835817541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032278404692873890545027 1548417607039310835817541)
          ·
            refine ⟨290328301319870781715789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1548417607039310835817541 290328301319870781715789)
            ·
              refine ⟨108873112994951543143421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290328301319870781715789 108873112994951543143421)
              ·
                refine ⟨40827417373106828678783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108873112994951543143421 40827417373106828678783)
                ·
                  rfl

theorem cell19_134175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_134175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134175 prefixEnd_134175 := by exact prefixLift 134175
  have htrace : WordTrace (prefixWord ++ tailWord_134175) baseStart_134175 baseEnd_134175 := by
    simpa [prefixWord, tailWord_134175, baseEnd_134175] using wordTrace_append hprefix tailTrace_134175
  have hstable : (prefixWord ++ tailWord_134175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134175).length < 2 ^ (prefixWord ++ tailWord_134175).sum := by decide
  have hdescent : baseEnd_134175 < baseStart_134175 := by decide
  rcases family_descends (prefixWord ++ tailWord_134175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134253 : List Nat := [1, 5, 1, 1, 2, 2, 7]
def baseStart_134253 : Nat := 118140960795 + 134253 * 2 ^ 59
def prefixEnd_134253 : Nat := 4983230072969 + 3 ^ 40 * 134253 * 2
def baseEnd_134253 : Nat := 13617050530008586315079

theorem tailTrace_134253 : CollatzResearch.WordTrace tailWord_134253 prefixEnd_134253 13617050530008586315079 := by
  unfold tailWord_134253
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896609182631784432071413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3264406121754522954714275 4896609182631784432071413)
  ·
    refine ⟨459057110871729790506695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4896609182631784432071413 459057110871729790506695)
    ·
      refine ⟨688585666307594685760043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459057110871729790506695 688585666307594685760043)
      ·
        refine ⟨1032878499461392028640065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688585666307594685760043 1032878499461392028640065)
        ·
          refine ⟨774658874596044021480049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032878499461392028640065 774658874596044021480049)
          ·
            refine ⟨580994155947033016110037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774658874596044021480049 580994155947033016110037)
            ·
              refine ⟨13617050530008586315079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 580994155947033016110037 13617050530008586315079)
              ·
                rfl

theorem cell19_134253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_134253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134253 prefixEnd_134253 := by exact prefixLift 134253
  have htrace : WordTrace (prefixWord ++ tailWord_134253) baseStart_134253 baseEnd_134253 := by
    simpa [prefixWord, tailWord_134253, baseEnd_134253] using wordTrace_append hprefix tailTrace_134253
  have hstable : (prefixWord ++ tailWord_134253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134253).length < 2 ^ (prefixWord ++ tailWord_134253).sum := by decide
  have hdescent : baseEnd_134253 < baseStart_134253 := by decide
  rcases family_descends (prefixWord ++ tailWord_134253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134312 : List Nat := [2, 1, 16]
def baseStart_134312 : Nat := 118140960795 + 134312 * 2 ^ 59
def prefixEnd_134312 : Nat := 4983230072969 + 3 ^ 40 * 134312 * 2
def baseEnd_134312 : Nat := 168185614794778204255

theorem tailTrace_134312 : CollatzResearch.WordTrace tailWord_134312 prefixEnd_134312 168185614794778204255 := by
  unfold tailWord_134312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2449380544709018754234595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3265840726278691672312793 2449380544709018754234595)
  ·
    refine ⟨3674070817063528131351893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2449380544709018754234595 3674070817063528131351893)
    ·
      refine ⟨168185614794778204255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 3674070817063528131351893 168185614794778204255)
      ·
        rfl

theorem cell19_134312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 16].length) (baseStart_134312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134312 prefixEnd_134312 := by exact prefixLift 134312
  have htrace : WordTrace (prefixWord ++ tailWord_134312) baseStart_134312 baseEnd_134312 := by
    simpa [prefixWord, tailWord_134312, baseEnd_134312] using wordTrace_append hprefix tailTrace_134312
  have hstable : (prefixWord ++ tailWord_134312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134312).length < 2 ^ (prefixWord ++ tailWord_134312).sum := by decide
  have hdescent : baseEnd_134312 < baseStart_134312 := by decide
  rcases family_descends (prefixWord ++ tailWord_134312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134329 : List Nat := [1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_134329 : Nat := 118140960795 + 134329 * 2 ^ 59
def prefixEnd_134329 : Nat := 4983230072969 + 3 ^ 40 * 134329 * 2
def baseEnd_134329 : Nat := 40874277237280101256141

theorem tailTrace_134329 : CollatzResearch.WordTrace tailWord_134329 prefixEnd_134329 40874277237280101256141 := by
  unfold tailWord_134329
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899381130356449411838041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3266254086904299607892027 4899381130356449411838041)
  ·
    refine ⟨3674535847767337058878531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4899381130356449411838041 3674535847767337058878531)
    ·
      refine ⟨5511803771651005588317797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3674535847767337058878531 5511803771651005588317797)
      ·
        refine ⟨1033463207184563547809587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5511803771651005588317797 1033463207184563547809587)
        ·
          refine ⟨1550194810776845321714381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033463207184563547809587 1550194810776845321714381)
          ·
            refine ⟨581323054041316995642893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1550194810776845321714381 581323054041316995642893)
            ·
              refine ⟨217996145265493873366085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 581323054041316995642893 217996145265493873366085)
              ·
                refine ⟨40874277237280101256141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217996145265493873366085 40874277237280101256141)
                ·
                  rfl

theorem cell19_134329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_134329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134329 prefixEnd_134329 := by exact prefixLift 134329
  have htrace : WordTrace (prefixWord ++ tailWord_134329) baseStart_134329 baseEnd_134329 := by
    simpa [prefixWord, tailWord_134329, baseEnd_134329] using wordTrace_append hprefix tailTrace_134329
  have hstable : (prefixWord ++ tailWord_134329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134329).length < 2 ^ (prefixWord ++ tailWord_134329).sum := by decide
  have hdescent : baseEnd_134329 < baseStart_134329 := by decide
  rcases family_descends (prefixWord ++ tailWord_134329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134331 : List Nat := [1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_134331 : Nat := 118140960795 + 134331 * 2 ^ 59
def prefixEnd_134331 : Nat := 4983230072969 + 3 ^ 40 * 134331 * 2
def baseEnd_134331 : Nat := 40874885806944689211691

theorem tailTrace_134331 : CollatzResearch.WordTrace tailWord_134331 prefixEnd_134331 40874885806944689211691 := by
  unfold tailWord_134331
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899454076349203753410847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3266302717566135835607231 4899454076349203753410847)
  ·
    refine ⟨7349181114523805630116271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4899454076349203753410847 7349181114523805630116271)
    ·
      refine ⟨11023771671785708445174407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7349181114523805630116271 11023771671785708445174407)
      ·
        refine ⟨16535657507678562667761611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11023771671785708445174407 16535657507678562667761611)
        ·
          refine ⟨24803486261517844001642417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16535657507678562667761611 24803486261517844001642417)
          ·
            refine ⟨18602614696138383001231813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24803486261517844001642417 18602614696138383001231813)
            ·
              refine ⟨3487990255525946812730965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18602614696138383001231813 3487990255525946812730965)
              ·
                refine ⟨40874885806944689211691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3487990255525946812730965 40874885806944689211691)
                ·
                  rfl

theorem cell19_134331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_134331 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134331 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134331 prefixEnd_134331 := by exact prefixLift 134331
  have htrace : WordTrace (prefixWord ++ tailWord_134331) baseStart_134331 baseEnd_134331 := by
    simpa [prefixWord, tailWord_134331, baseEnd_134331] using wordTrace_append hprefix tailTrace_134331
  have hstable : (prefixWord ++ tailWord_134331).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134331).length < 2 ^ (prefixWord ++ tailWord_134331).sum := by decide
  have hdescent : baseEnd_134331 < baseStart_134331 := by decide
  rcases family_descends (prefixWord ++ tailWord_134331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134346 : List Nat := [3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_134346 : Nat := 118140960795 + 134346 * 2 ^ 59
def prefixEnd_134346 : Nat := 4983230072969 + 3 ^ 40 * 134346 * 2
def baseEnd_134346 : Nat := 40879450079429098878317

theorem tailTrace_134346 : CollatzResearch.WordTrace tailWord_134346 prefixEnd_134346 40879450079429098878317 := by
  unfold tailWord_134346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225000292823715328801723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3266667447529907543471261 1225000292823715328801723)
  ·
    refine ⟨1837500439235572993202585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1225000292823715328801723 1837500439235572993202585)
    ·
      refine ⟨1378125329426679744901939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1837500439235572993202585 1378125329426679744901939)
      ·
        refine ⟨2067187994140019617352909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378125329426679744901939 2067187994140019617352909)
        ·
          refine ⟨775195497802507356507341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2067187994140019617352909 775195497802507356507341)
          ·
            refine ⟨290698311675940258690253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 775195497802507356507341 290698311675940258690253)
            ·
              refine ⟨109011866878477597008845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290698311675940258690253 109011866878477597008845)
              ·
                refine ⟨40879450079429098878317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109011866878477597008845 40879450079429098878317)
                ·
                  rfl

theorem cell19_134346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_134346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134346 prefixEnd_134346 := by exact prefixLift 134346
  have htrace : WordTrace (prefixWord ++ tailWord_134346) baseStart_134346 baseEnd_134346 := by
    simpa [prefixWord, tailWord_134346, baseEnd_134346] using wordTrace_append hprefix tailTrace_134346
  have hstable : (prefixWord ++ tailWord_134346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134346).length < 2 ^ (prefixWord ++ tailWord_134346).sum := by decide
  have hdescent : baseEnd_134346 < baseStart_134346 := by decide
  rcases family_descends (prefixWord ++ tailWord_134346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134365 : List Nat := [1, 4, 3, 2, 2, 1, 6]
def baseStart_134365 : Nat := 118140960795 + 134365 * 2 ^ 59
def prefixEnd_134365 : Nat := 4983230072969 + 3 ^ 40 * 134365 * 2
def baseEnd_134365 : Nat := 13628410497080894818681

theorem tailTrace_134365 : CollatzResearch.WordTrace tailWord_134365 prefixEnd_134365 13628410497080894818681 := by
  unfold tailWord_134365
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900694158226027560148549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3267129438817351706765699 4900694158226027560148549)
  ·
    refine ⟨918880154667380167527853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4900694158226027560148549 918880154667380167527853)
    ·
      refine ⟨344580058000267562822945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 918880154667380167527853 344580058000267562822945)
      ·
        refine ⟨258435043500200672117209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344580058000267562822945 258435043500200672117209)
        ·
          refine ⟨193826282625150504087907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258435043500200672117209 193826282625150504087907)
          ·
            refine ⟨290739423937725756131861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193826282625150504087907 290739423937725756131861)
            ·
              refine ⟨13628410497080894818681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 290739423937725756131861 13628410497080894818681)
              ·
                rfl

theorem cell19_134365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_134365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134365 prefixEnd_134365 := by exact prefixLift 134365
  have htrace : WordTrace (prefixWord ++ tailWord_134365) baseStart_134365 baseEnd_134365 := by
    simpa [prefixWord, tailWord_134365, baseEnd_134365] using wordTrace_append hprefix tailTrace_134365
  have hstable : (prefixWord ++ tailWord_134365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134365).length < 2 ^ (prefixWord ++ tailWord_134365).sum := by decide
  have hdescent : baseEnd_134365 < baseStart_134365 := by decide
  rcases family_descends (prefixWord ++ tailWord_134365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134403 : List Nat := [1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_134403 : Nat := 118140960795 + 134403 * 2 ^ 59
def prefixEnd_134403 : Nat := 4983230072969 + 3 ^ 40 * 134403 * 2
def baseEnd_134403 : Nat := 40896794314869855611495

theorem tailTrace_134403 : CollatzResearch.WordTrace tailWord_134403 prefixEnd_134403 40896794314869855611495 := by
  unfold tailWord_134403
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902080132088360050031863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3268053421392240033354575 4902080132088360050031863)
  ·
    refine ⟨7353120198132540075047795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4902080132088360050031863 7353120198132540075047795)
    ·
      refine ⟨11029680297198810112571693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7353120198132540075047795 11029680297198810112571693)
      ·
        refine ⟨4136130111449553792214385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11029680297198810112571693 4136130111449553792214385)
        ·
          refine ⟨3102097583587165344160789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4136130111449553792214385 3102097583587165344160789)
          ·
            refine ⟨145410824230648375507537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3102097583587165344160789 145410824230648375507537)
            ·
              refine ⟨109058118172986281630653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145410824230648375507537 109058118172986281630653)
              ·
                refine ⟨40896794314869855611495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109058118172986281630653 40896794314869855611495)
                ·
                  rfl

theorem cell19_134403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_134403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134403 prefixEnd_134403 := by exact prefixLift 134403
  have htrace : WordTrace (prefixWord ++ tailWord_134403) baseStart_134403 baseEnd_134403 := by
    simpa [prefixWord, tailWord_134403, baseEnd_134403] using wordTrace_append hprefix tailTrace_134403
  have hstable : (prefixWord ++ tailWord_134403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134403).length < 2 ^ (prefixWord ++ tailWord_134403).sum := by decide
  have hdescent : baseEnd_134403 < baseStart_134403 := by decide
  rcases family_descends (prefixWord ++ tailWord_134403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134418 : List Nat := [3, 2, 4, 2, 2, 1, 5]
def baseStart_134418 : Nat := 118140960795 + 134418 * 2 ^ 59
def prefixEnd_134418 : Nat := 4983230072969 + 3 ^ 40 * 134418 * 2
def baseEnd_134418 : Nat := 13633786195784755092707

theorem tailTrace_134418 : CollatzResearch.WordTrace tailWord_134418 prefixEnd_134418 13633786195784755092707 := by
  unfold tailWord_134418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225656806758504402956977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3268418151356011741218605 1225656806758504402956977)
  ·
    refine ⟨919242605068878302217733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1225656806758504402956977 919242605068878302217733)
    ·
      refine ⟨172357988450414681665825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 919242605068878302217733 172357988450414681665825)
      ·
        refine ⟨129268491337811011249369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172357988450414681665825 129268491337811011249369)
        ·
          refine ⟨96951368503358258437027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129268491337811011249369 96951368503358258437027)
          ·
            refine ⟨145427052755037387655541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96951368503358258437027 145427052755037387655541)
            ·
              refine ⟨13633786195784755092707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145427052755037387655541 13633786195784755092707)
              ·
                rfl

theorem cell19_134418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_134418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134418 prefixEnd_134418 := by exact prefixLift 134418
  have htrace : WordTrace (prefixWord ++ tailWord_134418) baseStart_134418 baseEnd_134418 := by
    simpa [prefixWord, tailWord_134418, baseEnd_134418] using wordTrace_append hprefix tailTrace_134418
  have hstable : (prefixWord ++ tailWord_134418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134418).length < 2 ^ (prefixWord ++ tailWord_134418).sum := by decide
  have hdescent : baseEnd_134418 < baseStart_134418 := by decide
  rcases family_descends (prefixWord ++ tailWord_134418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134424 : List Nat := [2, 1, 2, 3, 1, 5, 5]
def baseStart_134424 : Nat := 118140960795 + 134424 * 2 ^ 59
def prefixEnd_134424 : Nat := 4983230072969 + 3 ^ 40 * 134424 * 2
def baseEnd_134424 : Nat := 13634394765449343048257

theorem tailTrace_134424 : CollatzResearch.WordTrace tailWord_134424 prefixEnd_134424 13634394765449343048257 := by
  unfold tailWord_134424
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451423032506140318273163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3268564043341520424364217 2451423032506140318273163)
  ·
    refine ⟨3677134548759210477409745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451423032506140318273163 3677134548759210477409745)
    ·
      refine ⟨2757850911569407858057309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3677134548759210477409745 2757850911569407858057309)
      ·
        refine ⟨1034194091838527946771491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2757850911569407858057309 1034194091838527946771491)
        ·
          refine ⟨1551291137757791920157237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034194091838527946771491 1551291137757791920157237)
          ·
            refine ⟨145433544164792992514741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1551291137757791920157237 145433544164792992514741)
            ·
              refine ⟨13634394765449343048257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145433544164792992514741 13634394765449343048257)
              ·
                rfl

theorem cell19_134424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_134424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134424 prefixEnd_134424 := by exact prefixLift 134424
  have htrace : WordTrace (prefixWord ++ tailWord_134424) baseStart_134424 baseEnd_134424 := by
    simpa [prefixWord, tailWord_134424, baseEnd_134424] using wordTrace_append hprefix tailTrace_134424
  have hstable : (prefixWord ++ tailWord_134424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134424).length < 2 ^ (prefixWord ++ tailWord_134424).sum := by decide
  have hdescent : baseEnd_134424 < baseStart_134424 := by decide
  rcases family_descends (prefixWord ++ tailWord_134424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134462 : List Nat := [4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_134462 : Nat := 118140960795 + 134462 * 2 ^ 59
def prefixEnd_134462 : Nat := 4983230072969 + 3 ^ 40 * 134462 * 2
def baseEnd_134462 : Nat := 40914747119975200300223

theorem tailTrace_134462 : CollatzResearch.WordTrace tailWord_134462 prefixEnd_134462 40914747119975200300223 := by
  unfold tailWord_134462
  simp only [CollatzResearch.WordTrace]
  refine ⟨613029004859326640803705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3269488025916408750953093 613029004859326640803705)
  ·
    refine ⟨459771753644494980602779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 613029004859326640803705 459771753644494980602779)
    ·
      refine ⟨689657630466742470904169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459771753644494980602779 689657630466742470904169)
      ·
        refine ⟨517243222850056853178127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689657630466742470904169 517243222850056853178127)
        ·
          refine ⟨775864834275085279767191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517243222850056853178127 775864834275085279767191)
          ·
            refine ⟨1163797251412627919650787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775864834275085279767191 1163797251412627919650787)
            ·
              refine ⟨1745695877118941879476181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163797251412627919650787 1745695877118941879476181)
              ·
                refine ⟨40914747119975200300223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1745695877118941879476181 40914747119975200300223)
                ·
                  rfl

theorem cell19_134462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_134462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134462 prefixEnd_134462 := by exact prefixLift 134462
  have htrace : WordTrace (prefixWord ++ tailWord_134462) baseStart_134462 baseEnd_134462 := by
    simpa [prefixWord, tailWord_134462, baseEnd_134462] using wordTrace_append hprefix tailTrace_134462
  have hstable : (prefixWord ++ tailWord_134462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134462).length < 2 ^ (prefixWord ++ tailWord_134462).sum := by decide
  have hdescent : baseEnd_134462 < baseStart_134462 := by decide
  rcases family_descends (prefixWord ++ tailWord_134462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134464 : List Nat := [2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_134464 : Nat := 118140960795 + 134464 * 2 ^ 59
def prefixEnd_134464 : Nat := 4983230072969 + 3 ^ 40 * 134464 * 2
def baseEnd_134464 : Nat := 40915355689639788255773

theorem tailTrace_134464 : CollatzResearch.WordTrace tailWord_134464 prefixEnd_134464 40915355689639788255773 := by
  unfold tailWord_134464
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452152492433683734001223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3269536656578244978668297 2452152492433683734001223)
  ·
    refine ⟨3678228738650525601001835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2452152492433683734001223 3678228738650525601001835)
    ·
      refine ⟨5517343107975788401502753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3678228738650525601001835 5517343107975788401502753)
      ·
        refine ⟨4138007330981841301127065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5517343107975788401502753 4138007330981841301127065)
        ·
          refine ⟨3103505498236380975845299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4138007330981841301127065 3103505498236380975845299)
          ·
            refine ⟨4655258247354571463767949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103505498236380975845299 4655258247354571463767949)
            ·
              refine ⟨1745721842757964298912981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4655258247354571463767949 1745721842757964298912981)
              ·
                refine ⟨40915355689639788255773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1745721842757964298912981 40915355689639788255773)
                ·
                  rfl

theorem cell19_134464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_134464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134464 prefixEnd_134464 := by exact prefixLift 134464
  have htrace : WordTrace (prefixWord ++ tailWord_134464) baseStart_134464 baseEnd_134464 := by
    simpa [prefixWord, tailWord_134464, baseEnd_134464] using wordTrace_append hprefix tailTrace_134464
  have hstable : (prefixWord ++ tailWord_134464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134464).length < 2 ^ (prefixWord ++ tailWord_134464).sum := by decide
  have hdescent : baseEnd_134464 < baseStart_134464 := by decide
  rcases family_descends (prefixWord ++ tailWord_134464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134477 : List Nat := [1, 6, 1, 3, 2, 6]
def baseStart_134477 : Nat := 118140960795 + 134477 * 2 ^ 59
def prefixEnd_134477 : Nat := 4983230072969 + 3 ^ 40 * 134477 * 2
def baseEnd_134477 : Nat := 4546590154717734440761

theorem tailTrace_134477 : CollatzResearch.WordTrace tailWord_134477 prefixEnd_134477 4546590154717734440761 := by
  unfold tailWord_134477
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904779133820270688225685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3269852755880180458817123 4904779133820270688225685)
  ·
    refine ⟨229911521897825188510579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4904779133820270688225685 229911521897825188510579)
    ·
      refine ⟨344867282846737782765869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229911521897825188510579 344867282846737782765869)
      ·
        refine ⟨129325231067526668537201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344867282846737782765869 129325231067526668537201)
        ·
          refine ⟨96993923300645001402901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129325231067526668537201 96993923300645001402901)
          ·
            refine ⟨4546590154717734440761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96993923300645001402901 4546590154717734440761)
            ·
              rfl

theorem cell19_134477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_134477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134477 prefixEnd_134477 := by exact prefixLift 134477
  have htrace : WordTrace (prefixWord ++ tailWord_134477) baseStart_134477 baseEnd_134477 := by
    simpa [prefixWord, tailWord_134477, baseEnd_134477] using wordTrace_append hprefix tailTrace_134477
  have hstable : (prefixWord ++ tailWord_134477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134477).length < 2 ^ (prefixWord ++ tailWord_134477).sum := by decide
  have hdescent : baseEnd_134477 < baseStart_134477 := by decide
  rcases family_descends (prefixWord ++ tailWord_134477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134500 : List Nat := [2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_134500 : Nat := 118140960795 + 134500 * 2 ^ 59
def prefixEnd_134500 : Nat := 4983230072969 + 3 ^ 40 * 134500 * 2
def baseEnd_134500 : Nat := 40926309943602371455675

theorem tailTrace_134500 : CollatzResearch.WordTrace tailWord_134500 prefixEnd_134500 40926309943602371455675 := by
  unfold tailWord_134500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452809006368472808156477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3270412008491297077541969 2452809006368472808156477)
  ·
    refine ⟨919803377388177303058679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2452809006368472808156477 919803377388177303058679)
    ·
      refine ⟨1379705066082265954588019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919803377388177303058679 1379705066082265954588019)
      ·
        refine ⟨2069557599123398931882029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379705066082265954588019 2069557599123398931882029)
        ·
          refine ⟨776084099671274599455761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2069557599123398931882029 776084099671274599455761)
          ·
            refine ⟨582063074753455949591821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776084099671274599455761 582063074753455949591821)
            ·
              refine ⟨218273653032545981096933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 582063074753455949591821 218273653032545981096933)
              ·
                refine ⟨40926309943602371455675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218273653032545981096933 40926309943602371455675)
                ·
                  rfl

theorem cell19_134500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_134500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134500 prefixEnd_134500 := by exact prefixLift 134500
  have htrace : WordTrace (prefixWord ++ tailWord_134500) baseStart_134500 baseEnd_134500 := by
    simpa [prefixWord, tailWord_134500, baseEnd_134500] using wordTrace_append hprefix tailTrace_134500
  have hstable : (prefixWord ++ tailWord_134500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134500).length < 2 ^ (prefixWord ++ tailWord_134500).sum := by decide
  have hdescent : baseEnd_134500 < baseStart_134500 := by decide
  rcases family_descends (prefixWord ++ tailWord_134500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134519 : List Nat := [1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_134519 : Nat := 118140960795 + 134519 * 2 ^ 59
def prefixEnd_134519 : Nat := 4983230072969 + 3 ^ 40 * 134519 * 2
def baseEnd_134519 : Nat := 40932091355415957033401

theorem tailTrace_134519 : CollatzResearch.WordTrace tailWord_134519 prefixEnd_134519 40932091355415957033401 := by
  unfold tailWord_134519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4906310999668111861254611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3270873999778741240836407 4906310999668111861254611)
  ·
    refine ⟨7359466499502167791881917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4906310999668111861254611 7359466499502167791881917)
    ·
      refine ⟨2759799937313312921955719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7359466499502167791881917 2759799937313312921955719)
      ·
        refine ⟨4139699905969969382933579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2759799937313312921955719 4139699905969969382933579)
        ·
          refine ⟨6209549858954954074400369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4139699905969969382933579 6209549858954954074400369)
          ·
            refine ⟨4657162394216215555800277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6209549858954954074400369 4657162394216215555800277)
            ·
              refine ⟨109152243614442552089069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4657162394216215555800277 109152243614442552089069)
              ·
                refine ⟨40932091355415957033401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109152243614442552089069 40932091355415957033401)
                ·
                  rfl

theorem cell19_134519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_134519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134519 prefixEnd_134519 := by exact prefixLift 134519
  have htrace : WordTrace (prefixWord ++ tailWord_134519) baseStart_134519 baseEnd_134519 := by
    simpa [prefixWord, tailWord_134519, baseEnd_134519] using wordTrace_append hprefix tailTrace_134519
  have hstable : (prefixWord ++ tailWord_134519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134519).length < 2 ^ (prefixWord ++ tailWord_134519).sum := by decide
  have hdescent : baseEnd_134519 < baseStart_134519 := by decide
  rcases family_descends (prefixWord ++ tailWord_134519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134521 : List Nat := [1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_134521 : Nat := 118140960795 + 134521 * 2 ^ 59
def prefixEnd_134521 : Nat := 4983230072969 + 3 ^ 40 * 134521 * 2
def baseEnd_134521 : Nat := 40932699925080544988951

theorem tailTrace_134521 : CollatzResearch.WordTrace tailWord_134521 prefixEnd_134521 40932699925080544988951 := by
  unfold tailWord_134521
  simp only [CollatzResearch.WordTrace]
  refine ⟨4906383945660866202827417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3270922630440577468551611 4906383945660866202827417)
  ·
    refine ⟨3679787959245649652120563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4906383945660866202827417 3679787959245649652120563)
    ·
      refine ⟨5519681938868474478180845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679787959245649652120563 5519681938868474478180845)
      ·
        refine ⟨2069880727075677929317817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5519681938868474478180845 2069880727075677929317817)
        ·
          refine ⟨1552410545306758446988363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2069880727075677929317817 1552410545306758446988363)
          ·
            refine ⟨2328615817960137670482545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552410545306758446988363 2328615817960137670482545)
            ·
              refine ⟨1746461863470103252861909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328615817960137670482545 1746461863470103252861909)
              ·
                refine ⟨40932699925080544988951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1746461863470103252861909 40932699925080544988951)
                ·
                  rfl

theorem cell19_134521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_134521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134521 prefixEnd_134521 := by exact prefixLift 134521
  have htrace : WordTrace (prefixWord ++ tailWord_134521) baseStart_134521 baseEnd_134521 := by
    simpa [prefixWord, tailWord_134521, baseEnd_134521] using wordTrace_append hprefix tailTrace_134521
  have hstable : (prefixWord ++ tailWord_134521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134521).length < 2 ^ (prefixWord ++ tailWord_134521).sum := by decide
  have hdescent : baseEnd_134521 < baseStart_134521 := by decide
  rcases family_descends (prefixWord ++ tailWord_134521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134540 : List Nat := [2, 2, 1, 2, 1, 3, 8]
def baseStart_134540 : Nat := 118140960795 + 134540 * 2 ^ 59
def prefixEnd_134540 : Nat := 4983230072969 + 3 ^ 40 * 134540 * 2
def baseEnd_134540 : Nat := 13646160445631376855559

theorem tailTrace_134540 : CollatzResearch.WordTrace tailWord_134540 prefixEnd_134540 13646160445631376855559 := by
  unfold tailWord_134540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453538466296016223884537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3271384621728021631846049 2453538466296016223884537)
  ·
    refine ⟨1840153849722012167913403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2453538466296016223884537 1840153849722012167913403)
    ·
      refine ⟨2760230774583018251870105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840153849722012167913403 2760230774583018251870105)
      ·
        refine ⟨2070173080937263688902579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2760230774583018251870105 2070173080937263688902579)
        ·
          refine ⟨3105259621405895533353869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070173080937263688902579 3105259621405895533353869)
          ·
            refine ⟨1164472358027210825007701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3105259621405895533353869 1164472358027210825007701)
            ·
              refine ⟨13646160445631376855559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1164472358027210825007701 13646160445631376855559)
              ·
                rfl

theorem cell19_134540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_134540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134540 prefixEnd_134540 := by exact prefixLift 134540
  have htrace : WordTrace (prefixWord ++ tailWord_134540) baseStart_134540 baseEnd_134540 := by
    simpa [prefixWord, tailWord_134540, baseEnd_134540] using wordTrace_append hprefix tailTrace_134540
  have hstable : (prefixWord ++ tailWord_134540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134540).length < 2 ^ (prefixWord ++ tailWord_134540).sum := by decide
  have hdescent : baseEnd_134540 < baseStart_134540 := by decide
  rcases family_descends (prefixWord ++ tailWord_134540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134612 : List Nat := [2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_134612 : Nat := 118140960795 + 134612 * 2 ^ 59
def prefixEnd_134612 : Nat := 4983230072969 + 3 ^ 40 * 134612 * 2
def baseEnd_134612 : Nat := 40960389844819296966481

theorem tailTrace_134612 : CollatzResearch.WordTrace tailWord_134612 prefixEnd_134612 40960389844819296966481 := by
  unfold tailWord_134612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454851494165594372195045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3273135325554125829593393 2454851494165594372195045)
  ·
    refine ⟨460284655156048944786571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2454851494165594372195045 460284655156048944786571)
    ·
      refine ⟨690426982734073417179857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460284655156048944786571 690426982734073417179857)
      ·
        refine ⟨517820237050555062884893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690426982734073417179857 517820237050555062884893)
        ·
          refine ⟨194182588893958148581835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517820237050555062884893 194182588893958148581835)
          ·
            refine ⟨291273883340937222872753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194182588893958148581835 291273883340937222872753)
            ·
              refine ⟨218455412505702917154565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291273883340937222872753 218455412505702917154565)
              ·
                refine ⟨40960389844819296966481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218455412505702917154565 40960389844819296966481)
                ·
                  rfl

theorem cell19_134612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_134612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134612 prefixEnd_134612 := by exact prefixLift 134612
  have htrace : WordTrace (prefixWord ++ tailWord_134612) baseStart_134612 baseEnd_134612 := by
    simpa [prefixWord, tailWord_134612, baseEnd_134612] using wordTrace_append hprefix tailTrace_134612
  have hstable : (prefixWord ++ tailWord_134612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134612).length < 2 ^ (prefixWord ++ tailWord_134612).sum := by decide
  have hdescent : baseEnd_134612 < baseStart_134612 := by decide
  rcases family_descends (prefixWord ++ tailWord_134612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134616 : List Nat := [2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_134616 : Nat := 118140960795 + 134616 * 2 ^ 59
def prefixEnd_134616 : Nat := 4983230072969 + 3 ^ 40 * 134616 * 2
def baseEnd_134616 : Nat := 40961606984148472877581

theorem tailTrace_134616 : CollatzResearch.WordTrace tailWord_134616 prefixEnd_134616 40961606984148472877581 := by
  unfold tailWord_134616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454924440158348713767851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3273232586877798285023801 2454924440158348713767851)
  ·
    refine ⟨3682386660237523070651777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2454924440158348713767851 3682386660237523070651777)
    ·
      refine ⟨2761789995178142302988833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3682386660237523070651777 2761789995178142302988833)
      ·
        refine ⟨2071342496383606727241625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2761789995178142302988833 2071342496383606727241625)
        ·
          refine ⟨1553506872287705045431219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2071342496383606727241625 1553506872287705045431219)
          ·
            refine ⟨2330260308431557568146829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553506872287705045431219 2330260308431557568146829)
            ·
              refine ⟨873847615661834088055061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2330260308431557568146829 873847615661834088055061)
              ·
                refine ⟨40961606984148472877581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 873847615661834088055061 40961606984148472877581)
                ·
                  rfl

theorem cell19_134616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_134616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134616 prefixEnd_134616 := by exact prefixLift 134616
  have htrace : WordTrace (prefixWord ++ tailWord_134616) baseStart_134616 baseEnd_134616 := by
    simpa [prefixWord, tailWord_134616, baseEnd_134616] using wordTrace_append hprefix tailTrace_134616
  have hstable : (prefixWord ++ tailWord_134616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134616).length < 2 ^ (prefixWord ++ tailWord_134616).sum := by decide
  have hdescent : baseEnd_134616 < baseStart_134616 := by decide
  rcases family_descends (prefixWord ++ tailWord_134616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134688 : List Nat := [2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_134688 : Nat := 118140960795 + 134688 * 2 ^ 59
def prefixEnd_134688 : Nat := 4983230072969 + 3 ^ 40 * 134688 * 2
def baseEnd_134688 : Nat := 40983515492073639277385

theorem tailTrace_134688 : CollatzResearch.WordTrace tailWord_134688 prefixEnd_134688 40983515492073639277385 := by
  unfold tailWord_134688
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456237468027926862078359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3274983290703902482771145 2456237468027926862078359)
  ·
    refine ⟨3684356202041890293117539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2456237468027926862078359 3684356202041890293117539)
    ·
      refine ⟨5526534303062835439676309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3684356202041890293117539 5526534303062835439676309)
      ·
        refine ⟨259056295456070411234827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5526534303062835439676309 259056295456070411234827)
        ·
          refine ⟨388584443184105616852241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259056295456070411234827 388584443184105616852241)
          ·
            refine ⟨291438332388079212639181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388584443184105616852241 291438332388079212639181)
            ·
              refine ⟨109289374645529704739693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291438332388079212639181 109289374645529704739693)
              ·
                refine ⟨40983515492073639277385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109289374645529704739693 40983515492073639277385)
                ·
                  rfl

theorem cell19_134688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_134688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134688 prefixEnd_134688 := by exact prefixLift 134688
  have htrace : WordTrace (prefixWord ++ tailWord_134688) baseStart_134688 baseEnd_134688 := by
    simpa [prefixWord, tailWord_134688, baseEnd_134688] using wordTrace_append hprefix tailTrace_134688
  have hstable : (prefixWord ++ tailWord_134688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134688).length < 2 ^ (prefixWord ++ tailWord_134688).sum := by decide
  have hdescent : baseEnd_134688 < baseStart_134688 := by decide
  rcases family_descends (prefixWord ++ tailWord_134688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134711 : List Nat := [1, 1, 3, 1, 2, 5, 6]
def baseStart_134711 : Nat := 118140960795 + 134711 * 2 ^ 59
def prefixEnd_134711 : Nat := 4983230072969 + 3 ^ 40 * 134711 * 2
def baseEnd_134711 : Nat := 13663504681072133588737

theorem tailTrace_134711 : CollatzResearch.WordTrace tailWord_134711 prefixEnd_134711 13663504681072133588737 := by
  unfold tailWord_134711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913313814972528652243987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3275542543315019101495991 4913313814972528652243987)
  ·
    refine ⟨7369970722458792978365981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4913313814972528652243987 7369970722458792978365981)
    ·
      refine ⟨2763739020922047366887243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7369970722458792978365981 2763739020922047366887243)
      ·
        refine ⟨4145608531383071050330865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763739020922047366887243 4145608531383071050330865)
        ·
          refine ⟨3109206398537303287748149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4145608531383071050330865 3109206398537303287748149)
          ·
            refine ⟨291488099862872183226389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3109206398537303287748149 291488099862872183226389)
            ·
              refine ⟨13663504681072133588737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 291488099862872183226389 13663504681072133588737)
              ·
                rfl

theorem cell19_134711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_134711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134711 prefixEnd_134711 := by exact prefixLift 134711
  have htrace : WordTrace (prefixWord ++ tailWord_134711) baseStart_134711 baseEnd_134711 := by
    simpa [prefixWord, tailWord_134711, baseEnd_134711] using wordTrace_append hprefix tailTrace_134711
  have hstable : (prefixWord ++ tailWord_134711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134711).length < 2 ^ (prefixWord ++ tailWord_134711).sum := by decide
  have hdescent : baseEnd_134711 < baseStart_134711 := by decide
  rcases family_descends (prefixWord ++ tailWord_134711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134730 : List Nat := [3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_134730 : Nat := 118140960795 + 134730 * 2 ^ 59
def prefixEnd_134730 : Nat := 4983230072969 + 3 ^ 40 * 134730 * 2
def baseEnd_134730 : Nat := 40996295455029986343937

theorem tailTrace_134730 : CollatzResearch.WordTrace tailWord_134730 prefixEnd_134730 40996295455029986343937 := by
  unfold tailWord_134730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228501700475923724296411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3276004534602463264790429 1228501700475923724296411)
  ·
    refine ⟨1842752550713885586444617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1228501700475923724296411 1842752550713885586444617)
    ·
      refine ⟨1382064413035414189833463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1842752550713885586444617 1382064413035414189833463)
      ·
        refine ⟨2073096619553121284750195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382064413035414189833463 2073096619553121284750195)
        ·
          refine ⟨3109644929329681927125293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073096619553121284750195 3109644929329681927125293)
          ·
            refine ⟨1166116848498630722671985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3109644929329681927125293 1166116848498630722671985)
            ·
              refine ⟨874587636373973042003989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166116848498630722671985 874587636373973042003989)
              ·
                refine ⟨40996295455029986343937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 874587636373973042003989 40996295455029986343937)
                ·
                  rfl

theorem cell19_134730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_134730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134730 prefixEnd_134730 := by exact prefixLift 134730
  have htrace : WordTrace (prefixWord ++ tailWord_134730) baseStart_134730 baseEnd_134730 := by
    simpa [prefixWord, tailWord_134730, baseEnd_134730] using wordTrace_append hprefix tailTrace_134730
  have hstable : (prefixWord ++ tailWord_134730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134730).length < 2 ^ (prefixWord ++ tailWord_134730).sum := by decide
  have hdescent : baseEnd_134730 < baseStart_134730 := by decide
  rcases family_descends (prefixWord ++ tailWord_134730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134768 : List Nat := [2, 1, 1, 1, 6, 1, 7]
def baseStart_134768 : Nat := 118140960795 + 134768 * 2 ^ 59
def prefixEnd_134768 : Nat := 4983230072969 + 3 ^ 40 * 134768 * 2
def baseEnd_134768 : Nat := 13669286092885719166463

theorem tailTrace_134768 : CollatzResearch.WordTrace tailWord_134768 prefixEnd_134768 13669286092885719166463 := by
  unfold tailWord_134768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457696387883013693534479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3276928517177351591379305 2457696387883013693534479)
  ·
    refine ⟨3686544581824520540301719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2457696387883013693534479 3686544581824520540301719)
    ·
      refine ⟨5529816872736780810452579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686544581824520540301719 5529816872736780810452579)
      ·
        refine ⟨8294725309105171215678869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5529816872736780810452579 8294725309105171215678869)
        ·
          refine ⟨388815248864304900734947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8294725309105171215678869 388815248864304900734947)
          ·
            refine ⟨583222873296457351102421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388815248864304900734947 583222873296457351102421)
            ·
              refine ⟨13669286092885719166463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 583222873296457351102421 13669286092885719166463)
              ·
                rfl

theorem cell19_134768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_134768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134768 prefixEnd_134768 := by exact prefixLift 134768
  have htrace : WordTrace (prefixWord ++ tailWord_134768) baseStart_134768 baseEnd_134768 := by
    simpa [prefixWord, tailWord_134768, baseEnd_134768] using wordTrace_append hprefix tailTrace_134768
  have hstable : (prefixWord ++ tailWord_134768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134768).length < 2 ^ (prefixWord ++ tailWord_134768).sum := by decide
  have hdescent : baseEnd_134768 < baseStart_134768 := by decide
  rcases family_descends (prefixWord ++ tailWord_134768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134785 : List Nat := [1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_134785 : Nat := 118140960795 + 134785 * 2 ^ 59
def prefixEnd_134785 : Nat := 4983230072969 + 3 ^ 40 * 134785 * 2
def baseEnd_134785 : Nat := 41013031120806155121565

theorem tailTrace_134785 : CollatzResearch.WordTrace tailWord_134785 prefixEnd_134785 41013031120806155121565 := by
  unfold tailWord_134785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916012816704439290437809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3277341877802959526958539 4916012816704439290437809)
  ·
    refine ⟨3687009612528329467828357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4916012816704439290437809 3687009612528329467828357)
    ·
      refine ⟨691314302349061775217817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3687009612528329467828357 691314302349061775217817)
      ·
        refine ⟨518485726761796331413363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691314302349061775217817 518485726761796331413363)
        ·
          refine ⟨777728590142694497120045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518485726761796331413363 777728590142694497120045)
          ·
            refine ⟨291648221303510436420017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 777728590142694497120045 291648221303510436420017)
            ·
              refine ⟨218736165977632827315013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291648221303510436420017 218736165977632827315013)
              ·
                refine ⟨41013031120806155121565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218736165977632827315013 41013031120806155121565)
                ·
                  rfl

theorem cell19_134785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_134785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134785 prefixEnd_134785 := by exact prefixLift 134785
  have htrace : WordTrace (prefixWord ++ tailWord_134785) baseStart_134785 baseEnd_134785 := by
    simpa [prefixWord, tailWord_134785, baseEnd_134785] using wordTrace_append hprefix tailTrace_134785
  have hstable : (prefixWord ++ tailWord_134785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134785).length < 2 ^ (prefixWord ++ tailWord_134785).sum := by decide
  have hdescent : baseEnd_134785 < baseStart_134785 := by decide
  rcases family_descends (prefixWord ++ tailWord_134785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134838 : List Nat := [5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_134838 : Nat := 118140960795 + 134838 * 2 ^ 59
def prefixEnd_134838 : Nat := 4983230072969 + 3 ^ 40 * 134838 * 2
def baseEnd_134838 : Nat := 41029158216917735943643

theorem tailTrace_134838 : CollatzResearch.WordTrace tailWord_134838 prefixEnd_134838 41029158216917735943643 := by
  unfold tailWord_134838
  simp only [CollatzResearch.WordTrace]
  refine ⟨307371617844526833882323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3278630590341619561411445 307371617844526833882323)
  ·
    refine ⟨461057426766790250823485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307371617844526833882323 461057426766790250823485)
    ·
      refine ⟨172896535037546344058807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 461057426766790250823485 172896535037546344058807)
      ·
        refine ⟨259344802556319516088211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172896535037546344058807 259344802556319516088211)
        ·
          refine ⟨389017203834479274132317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259344802556319516088211 389017203834479274132317)
          ·
            refine ⟨145881451437929727799619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389017203834479274132317 145881451437929727799619)
            ·
              refine ⟨218822177156894591699429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145881451437929727799619 218822177156894591699429)
              ·
                refine ⟨41029158216917735943643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218822177156894591699429 41029158216917735943643)
                ·
                  rfl

theorem cell19_134838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_134838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134838 prefixEnd_134838 := by exact prefixLift 134838
  have htrace : WordTrace (prefixWord ++ tailWord_134838) baseStart_134838 baseEnd_134838 := by
    simpa [prefixWord, tailWord_134838, baseEnd_134838] using wordTrace_append hprefix tailTrace_134838
  have hstable : (prefixWord ++ tailWord_134838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134838).length < 2 ^ (prefixWord ++ tailWord_134838).sum := by decide
  have hdescent : baseEnd_134838 < baseStart_134838 := by decide
  rcases family_descends (prefixWord ++ tailWord_134838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134842 : List Nat := [3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_134842 : Nat := 118140960795 + 134842 * 2 ^ 59
def prefixEnd_134842 : Nat := 4983230072969 + 3 ^ 40 * 134842 * 2
def baseEnd_134842 : Nat := 41030375356246911854743

theorem tailTrace_134842 : CollatzResearch.WordTrace tailWord_134842 prefixEnd_134842 41030375356246911854743 := by
  unfold tailWord_134842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1229522944374484506315695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3278727851665292016841853 1229522944374484506315695)
  ·
    refine ⟨1844284416561726759473543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1229522944374484506315695 1844284416561726759473543)
    ·
      refine ⟨2766426624842590139210315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844284416561726759473543 2766426624842590139210315)
      ·
        refine ⟨4149639937263885208815473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766426624842590139210315 4149639937263885208815473)
        ·
          refine ⟨3112229952947913906611605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4149639937263885208815473 3112229952947913906611605)
          ·
            refine ⟨145885779044433464372419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3112229952947913906611605 145885779044433464372419)
            ·
              refine ⟨218828668566650196558629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145885779044433464372419 218828668566650196558629)
              ·
                refine ⟨41030375356246911854743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218828668566650196558629 41030375356246911854743)
                ·
                  rfl

theorem cell19_134842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_134842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134842 prefixEnd_134842 := by exact prefixLift 134842
  have htrace : WordTrace (prefixWord ++ tailWord_134842) baseStart_134842 baseEnd_134842 := by
    simpa [prefixWord, tailWord_134842, baseEnd_134842] using wordTrace_append hprefix tailTrace_134842
  have hstable : (prefixWord ++ tailWord_134842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134842).length < 2 ^ (prefixWord ++ tailWord_134842).sum := by decide
  have hdescent : baseEnd_134842 < baseStart_134842 := by decide
  rcases family_descends (prefixWord ++ tailWord_134842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134916 : List Nat := [2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_134916 : Nat := 118140960795 + 134916 * 2 ^ 59
def prefixEnd_134916 : Nat := 4983230072969 + 3 ^ 40 * 134916 * 2
def baseEnd_134916 : Nat := 41052892433836666210097

theorem tailTrace_134916 : CollatzResearch.WordTrace tailWord_134916 prefixEnd_134916 41052892433836666210097 := by
  unfold tailWord_134916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460395389614924331728301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3280527186153232442304401 2460395389614924331728301)
  ·
    refine ⟨922648271105596624398113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2460395389614924331728301 922648271105596624398113)
    ·
      refine ⟨691986203329197468298585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 922648271105596624398113 691986203329197468298585)
      ·
        refine ⟨518989652496898101223939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691986203329197468298585 518989652496898101223939)
        ·
          refine ⟨778484478745347151835909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518989652496898101223939 778484478745347151835909)
          ·
            refine ⟨145965839764752590969233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 778484478745347151835909 145965839764752590969233)
            ·
              refine ⟨109474379823564443226925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145965839764752590969233 109474379823564443226925)
              ·
                refine ⟨41052892433836666210097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109474379823564443226925 41052892433836666210097)
                ·
                  rfl

theorem cell19_134916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_134916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134916 prefixEnd_134916 := by exact prefixLift 134916
  have htrace : WordTrace (prefixWord ++ tailWord_134916) baseStart_134916 baseEnd_134916 := by
    simpa [prefixWord, tailWord_134916, baseEnd_134916] using wordTrace_append hprefix tailTrace_134916
  have hstable : (prefixWord ++ tailWord_134916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134916).length < 2 ^ (prefixWord ++ tailWord_134916).sum := by decide
  have hdescent : baseEnd_134916 < baseStart_134916 := by decide
  rcases family_descends (prefixWord ++ tailWord_134916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134920 : List Nat := [2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_134920 : Nat := 118140960795 + 134920 * 2 ^ 59
def prefixEnd_134920 : Nat := 4983230072969 + 3 ^ 40 * 134920 * 2
def baseEnd_134920 : Nat := 41054109573165842121197

theorem tailTrace_134920 : CollatzResearch.WordTrace tailWord_134920 prefixEnd_134920 41054109573165842121197 := by
  unfold tailWord_134920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460468335607678673301107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3280624447476904897734809 2460468335607678673301107)
  ·
    refine ⟨3690702503411518009951661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2460468335607678673301107 3690702503411518009951661)
    ·
      refine ⟨1384013438779319253731873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3690702503411518009951661 1384013438779319253731873)
      ·
        refine ⟨1038010079084489440298905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384013438779319253731873 1038010079084489440298905)
        ·
          refine ⟨778507559313367080224179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038010079084489440298905 778507559313367080224179)
          ·
            refine ⟨1167761338970050620336269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778507559313367080224179 1167761338970050620336269)
            ·
              refine ⟨437910502113768982626101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167761338970050620336269 437910502113768982626101)
              ·
                refine ⟨41054109573165842121197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 437910502113768982626101 41054109573165842121197)
                ·
                  rfl

theorem cell19_134920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_134920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134920 prefixEnd_134920 := by exact prefixLift 134920
  have htrace : WordTrace (prefixWord ++ tailWord_134920) baseStart_134920 baseEnd_134920 := by
    simpa [prefixWord, tailWord_134920, baseEnd_134920] using wordTrace_append hprefix tailTrace_134920
  have hstable : (prefixWord ++ tailWord_134920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134920).length < 2 ^ (prefixWord ++ tailWord_134920).sum := by decide
  have hdescent : baseEnd_134920 < baseStart_134920 := by decide
  rcases family_descends (prefixWord ++ tailWord_134920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134996 : List Nat := [2, 4, 1, 1, 3, 8]
def baseStart_134996 : Nat := 118140960795 + 134996 * 2 ^ 59
def prefixEnd_134996 : Nat := 4983230072969 + 3 ^ 40 * 134996 * 2
def baseEnd_134996 : Nat := 4564137246713353825789

theorem tailTrace_134996 : CollatzResearch.WordTrace tailWord_134996 prefixEnd_134996 4564137246713353825789 := by
  unfold tailWord_134996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461854309470011163184421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3282472412626681550912561 2461854309470011163184421)
  ·
    refine ⟨461597683025627093097079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2461854309470011163184421 461597683025627093097079)
    ·
      refine ⟨692396524538440639645619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461597683025627093097079 692396524538440639645619)
      ·
        refine ⟨1038594786807660959468429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692396524538440639645619 1038594786807660959468429)
        ·
          refine ⟨389473045052872859800661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1038594786807660959468429 389473045052872859800661)
          ·
            refine ⟨4564137246713353825789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 389473045052872859800661 4564137246713353825789)
            ·
              rfl

theorem cell19_134996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_134996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_134996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_134996 prefixEnd_134996 := by exact prefixLift 134996
  have htrace : WordTrace (prefixWord ++ tailWord_134996) baseStart_134996 baseEnd_134996 := by
    simpa [prefixWord, tailWord_134996, baseEnd_134996] using wordTrace_append hprefix tailTrace_134996
  have hstable : (prefixWord ++ tailWord_134996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134996).length < 2 ^ (prefixWord ++ tailWord_134996).sum := by decide
  have hdescent : baseEnd_134996 < baseStart_134996 := by decide
  rcases family_descends (prefixWord ++ tailWord_134996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135011 : List Nat := [1, 1, 1, 5, 5, 1, 1, 4]
def baseStart_135011 : Nat := 118140960795 + 135011 * 2 ^ 59
def prefixEnd_135011 : Nat := 4983230072969 + 3 ^ 40 * 135011 * 2
def baseEnd_135011 : Nat := 41081799492904594098727

theorem tailTrace_135011 : CollatzResearch.WordTrace tailWord_135011 prefixEnd_135011 41081799492904594098727 := by
  unfold tailWord_135011
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924255713885679888164887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3282837142590453258776591 4924255713885679888164887)
  ·
    refine ⟨7386383570828519832247331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924255713885679888164887 7386383570828519832247331)
    ·
      refine ⟨11079575356242779748370997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386383570828519832247331 11079575356242779748370997)
      ·
        refine ⟨1038710189647760601409781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11079575356242779748370997 1038710189647760601409781)
        ·
          refine ⟨97379080279477556382167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1038710189647760601409781 97379080279477556382167)
          ·
            refine ⟨146068620419216334573251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97379080279477556382167 146068620419216334573251)
            ·
              refine ⟨219102930628824501859877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146068620419216334573251 219102930628824501859877)
              ·
                refine ⟨41081799492904594098727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219102930628824501859877 41081799492904594098727)
                ·
                  rfl

theorem cell19_135011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_135011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135011 prefixEnd_135011 := by exact prefixLift 135011
  have htrace : WordTrace (prefixWord ++ tailWord_135011) baseStart_135011 baseEnd_135011 := by
    simpa [prefixWord, tailWord_135011, baseEnd_135011] using wordTrace_append hprefix tailTrace_135011
  have hstable : (prefixWord ++ tailWord_135011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135011).length < 2 ^ (prefixWord ++ tailWord_135011).sum := by decide
  have hdescent : baseEnd_135011 < baseStart_135011 := by decide
  rcases family_descends (prefixWord ++ tailWord_135011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135089 : List Nat := [1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_135089 : Nat := 118140960795 + 135089 * 2 ^ 59
def prefixEnd_135089 : Nat := 4983230072969 + 3 ^ 40 * 135089 * 2
def baseEnd_135089 : Nat := 41105533709823524365181

theorem tailTrace_135089 : CollatzResearch.WordTrace tailWord_135089 prefixEnd_135089 41105533709823524365181 := by
  unfold tailWord_135089
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927100607603099209504321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3284733738402066139669547 4927100607603099209504321)
  ·
    refine ⟨3695325455702324407128241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4927100607603099209504321 3695325455702324407128241)
    ·
      refine ⟨2771494091776743305346181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3695325455702324407128241 2771494091776743305346181)
      ·
        refine ⟨519655142208139369752409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2771494091776743305346181 519655142208139369752409)
        ·
          refine ⟨389741356656104527314307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519655142208139369752409 389741356656104527314307)
          ·
            refine ⟨584612034984156790971461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389741356656104527314307 584612034984156790971461)
            ·
              refine ⟨109614756559529398307149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 584612034984156790971461 109614756559529398307149)
              ·
                refine ⟨41105533709823524365181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109614756559529398307149 41105533709823524365181)
                ·
                  rfl

theorem cell19_135089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_135089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135089 prefixEnd_135089 := by exact prefixLift 135089
  have htrace : WordTrace (prefixWord ++ tailWord_135089) baseStart_135089 baseEnd_135089 := by
    simpa [prefixWord, tailWord_135089, baseEnd_135089] using wordTrace_append hprefix tailTrace_135089
  have hstable : (prefixWord ++ tailWord_135089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135089).length < 2 ^ (prefixWord ++ tailWord_135089).sum := by decide
  have hdescent : baseEnd_135089 < baseStart_135089 := by decide
  rcases family_descends (prefixWord ++ tailWord_135089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135224 : List Nat := [2, 1, 2, 1, 6, 1, 6]
def baseStart_135224 : Nat := 118140960795 + 135224 * 2 ^ 59
def prefixEnd_135224 : Nat := 4983230072969 + 3 ^ 40 * 135224 * 2
def baseEnd_135224 : Nat := 13715537387394403788271

theorem tailTrace_135224 : CollatzResearch.WordTrace tailWord_135224 prefixEnd_135224 13715537387394403788271 := by
  unfold tailWord_135224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466012231057008632834363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3288016308076011510445817 2466012231057008632834363)
  ·
    refine ⟨3699018346585512949251545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2466012231057008632834363 3699018346585512949251545)
    ·
      refine ⟨2774263759939134711938659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3699018346585512949251545 2774263759939134711938659)
      ·
        refine ⟨4161395639908702067907989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774263759939134711938659 4161395639908702067907989)
        ·
          refine ⟨195065420620720409433187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4161395639908702067907989 195065420620720409433187)
          ·
            refine ⟨292598130931080614149781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195065420620720409433187 292598130931080614149781)
            ·
              refine ⟨13715537387394403788271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292598130931080614149781 13715537387394403788271)
              ·
                rfl

theorem cell19_135224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_135224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135224 prefixEnd_135224 := by exact prefixLift 135224
  have htrace : WordTrace (prefixWord ++ tailWord_135224) baseStart_135224 baseEnd_135224 := by
    simpa [prefixWord, tailWord_135224, baseEnd_135224] using wordTrace_append hprefix tailTrace_135224
  have hstable : (prefixWord ++ tailWord_135224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135224).length < 2 ^ (prefixWord ++ tailWord_135224).sum := by decide
  have hdescent : baseEnd_135224 < baseStart_135224 := by decide
  rcases family_descends (prefixWord ++ tailWord_135224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135260 : List Nat := [2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_135260 : Nat := 118140960795 + 135260 * 2 ^ 59
def prefixEnd_135260 : Nat := 4983230072969 + 3 ^ 40 * 135260 * 2
def baseEnd_135260 : Nat := 41157566416145794564715

theorem tailTrace_135260 : CollatzResearch.WordTrace tailWord_135260 prefixEnd_135260 41157566416145794564715 := by
  unfold tailWord_135260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466668744991797706989617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3288891659989063609319489 2466668744991797706989617)
  ·
    refine ⟨1850001558743848280242213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2466668744991797706989617 1850001558743848280242213)
    ·
      refine ⟨346875292264471552545415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1850001558743848280242213 346875292264471552545415)
      ·
        refine ⟨520312938396707328818123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346875292264471552545415 520312938396707328818123)
        ·
          refine ⟨780469407595060993227185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520312938396707328818123 780469407595060993227185)
          ·
            refine ⟨585352055696295744920389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 780469407595060993227185 585352055696295744920389)
            ·
              refine ⟨109753510443055452172573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 585352055696295744920389 109753510443055452172573)
              ·
                refine ⟨41157566416145794564715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109753510443055452172573 41157566416145794564715)
                ·
                  rfl

theorem cell19_135260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_135260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135260 prefixEnd_135260 := by exact prefixLift 135260
  have htrace : WordTrace (prefixWord ++ tailWord_135260) baseStart_135260 baseEnd_135260 := by
    simpa [prefixWord, tailWord_135260, baseEnd_135260] using wordTrace_append hprefix tailTrace_135260
  have hstable : (prefixWord ++ tailWord_135260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135260).length < 2 ^ (prefixWord ++ tailWord_135260).sum := by decide
  have hdescent : baseEnd_135260 < baseStart_135260 := by decide
  rcases family_descends (prefixWord ++ tailWord_135260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135300 : List Nat := [2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_135300 : Nat := 118140960795 + 135300 * 2 ^ 59
def prefixEnd_135300 : Nat := 4983230072969 + 3 ^ 40 * 135300 * 2
def baseEnd_135300 : Nat := 41169737809437553675717

theorem tailTrace_135300 : CollatzResearch.WordTrace tailWord_135300 prefixEnd_135300 41169737809437553675717 := by
  unfold tailWord_135300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467398204919341122717677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3289864273225788163623569 2467398204919341122717677)
  ·
    refine ⟨925274326844752921019129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2467398204919341122717677 925274326844752921019129)
    ·
      refine ⟨693955745133564690764347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 925274326844752921019129 693955745133564690764347)
      ·
        refine ⟨1040933617700347036146521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693955745133564690764347 1040933617700347036146521)
        ·
          refine ⟨780700213275260277109891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040933617700347036146521 780700213275260277109891)
          ·
            refine ⟨1171050319912890415664837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780700213275260277109891 1171050319912890415664837)
            ·
              refine ⟨219571934983666952937157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1171050319912890415664837 219571934983666952937157)
              ·
                refine ⟨41169737809437553675717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219571934983666952937157 41169737809437553675717)
                ·
                  rfl

theorem cell19_135300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_135300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135300 prefixEnd_135300 := by exact prefixLift 135300
  have htrace : WordTrace (prefixWord ++ tailWord_135300) baseStart_135300 baseEnd_135300 := by
    simpa [prefixWord, tailWord_135300, baseEnd_135300] using wordTrace_append hprefix tailTrace_135300
  have hstable : (prefixWord ++ tailWord_135300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135300).length < 2 ^ (prefixWord ++ tailWord_135300).sum := by decide
  have hdescent : baseEnd_135300 < baseStart_135300 := by decide
  rcases family_descends (prefixWord ++ tailWord_135300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135338 : List Nat := [3, 1, 5, 1, 9]
def baseStart_135338 : Nat := 118140960795 + 135338 * 2 ^ 59
def prefixEnd_135338 : Nat := 4983230072969 + 3 ^ 40 * 135338 * 2
def baseEnd_135338 : Nat := 1525233356780174993747

theorem tailTrace_135338 : CollatzResearch.WordTrace tailWord_135338 prefixEnd_135338 1525233356780174993747 := by
  unfold tailWord_135338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234045595925253683829667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3290788255800676490212445 1234045595925253683829667)
  ·
    refine ⟨1851068393887880525744501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234045595925253683829667 1851068393887880525744501)
    ·
      refine ⟨173537661926988799288547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1851068393887880525744501 173537661926988799288547)
      ·
        refine ⟨260306492890483198932821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173537661926988799288547 260306492890483198932821)
        ·
          refine ⟨1525233356780174993747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 260306492890483198932821 1525233356780174993747)
          ·
            rfl

theorem cell19_135338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 9].length) (baseStart_135338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135338 prefixEnd_135338 := by exact prefixLift 135338
  have htrace : WordTrace (prefixWord ++ tailWord_135338) baseStart_135338 baseEnd_135338 := by
    simpa [prefixWord, tailWord_135338, baseEnd_135338] using wordTrace_append hprefix tailTrace_135338
  have hstable : (prefixWord ++ tailWord_135338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135338).length < 2 ^ (prefixWord ++ tailWord_135338).sum := by decide
  have hdescent : baseEnd_135338 < baseStart_135338 := by decide
  rcases family_descends (prefixWord ++ tailWord_135338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135372 : List Nat := [2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_135372 : Nat := 118140960795 + 135372 * 2 ^ 59
def prefixEnd_135372 : Nat := 4983230072969 + 3 ^ 40 * 135372 * 2
def baseEnd_135372 : Nat := 41191646317362720075521

theorem tailTrace_135372 : CollatzResearch.WordTrace tailWord_135372 prefixEnd_135372 41191646317362720075521 := by
  unfold tailWord_135372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468711232788919271028185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3291614977051892361370913 2468711232788919271028185)
  ·
    refine ⟨1851533424591689453271139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2468711232788919271028185 1851533424591689453271139)
    ·
      refine ⟨2777300136887534179906709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851533424591689453271139 2777300136887534179906709)
      ·
        refine ⟨130185943916603164683127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2777300136887534179906709 130185943916603164683127)
        ·
          refine ⟨195278915874904747024691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130185943916603164683127 195278915874904747024691)
          ·
            refine ⟨292918373812357120537037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195278915874904747024691 292918373812357120537037)
            ·
              refine ⟨109844390179633920201389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292918373812357120537037 109844390179633920201389)
              ·
                refine ⟨41191646317362720075521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109844390179633920201389 41191646317362720075521)
                ·
                  rfl

theorem cell19_135372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_135372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135372 prefixEnd_135372 := by exact prefixLift 135372
  have htrace : WordTrace (prefixWord ++ tailWord_135372) baseStart_135372 baseEnd_135372 := by
    simpa [prefixWord, tailWord_135372, baseEnd_135372] using wordTrace_append hprefix tailTrace_135372
  have hstable : (prefixWord ++ tailWord_135372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135372).length < 2 ^ (prefixWord ++ tailWord_135372).sum := by decide
  have hdescent : baseEnd_135372 < baseStart_135372 := by decide
  rcases family_descends (prefixWord ++ tailWord_135372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135374 : List Nat := [4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_135374 : Nat := 118140960795 + 135374 * 2 ^ 59
def prefixEnd_135374 : Nat := 4983230072969 + 3 ^ 40 * 135374 * 2
def baseEnd_135374 : Nat := 41192254887027308031071

theorem tailTrace_135374 : CollatzResearch.WordTrace tailWord_135374 prefixEnd_135374 41192254887027308031071 := by
  unfold tailWord_135374
  simp only [CollatzResearch.WordTrace]
  refine ⟨617186926446324110453647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3291663607713728589086117 617186926446324110453647)
  ·
    refine ⟨925780389669486165680471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 617186926446324110453647 925780389669486165680471)
    ·
      refine ⟨1388670584504229248520707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925780389669486165680471 1388670584504229248520707)
      ·
        refine ⟨2083005876756343872781061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388670584504229248520707 2083005876756343872781061)
        ·
          refine ⟨390563601891814476146449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2083005876756343872781061 390563601891814476146449)
          ·
            refine ⟨292922701418860857109837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390563601891814476146449 292922701418860857109837)
            ·
              refine ⟨109846013032072821416189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292922701418860857109837 109846013032072821416189)
              ·
                refine ⟨41192254887027308031071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109846013032072821416189 41192254887027308031071)
                ·
                  rfl

theorem cell19_135374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_135374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135374 prefixEnd_135374 := by exact prefixLift 135374
  have htrace : WordTrace (prefixWord ++ tailWord_135374) baseStart_135374 baseEnd_135374 := by
    simpa [prefixWord, tailWord_135374, baseEnd_135374] using wordTrace_append hprefix tailTrace_135374
  have hstable : (prefixWord ++ tailWord_135374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135374).length < 2 ^ (prefixWord ++ tailWord_135374).sum := by decide
  have hdescent : baseEnd_135374 < baseStart_135374 := by decide
  rcases family_descends (prefixWord ++ tailWord_135374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135431 : List Nat := [1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_135431 : Nat := 118140960795 + 135431 * 2 ^ 59
def prefixEnd_135431 : Nat := 4983230072969 + 3 ^ 40 * 135431 * 2
def baseEnd_135431 : Nat := 41209599122468064764249

theorem tailTrace_135431 : CollatzResearch.WordTrace tailWord_135431 prefixEnd_135431 41209599122468064764249 := by
  unfold tailWord_135431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939574372364091618454147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3293049581576061078969431 4939574372364091618454147)
  ·
    refine ⟨7409361558546137427681221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4939574372364091618454147 7409361558546137427681221)
    ·
      refine ⟨1389255292227400767690229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7409361558546137427681221 1389255292227400767690229)
      ·
        refine ⟨130242683646318821970959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1389255292227400767690229 130242683646318821970959)
        ·
          refine ⟨195364025469478232956439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130242683646318821970959 195364025469478232956439)
          ·
            refine ⟨293046038204217349434659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195364025469478232956439 293046038204217349434659)
            ·
              refine ⟨439569057306326024151989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293046038204217349434659 439569057306326024151989)
              ·
                refine ⟨41209599122468064764249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439569057306326024151989 41209599122468064764249)
                ·
                  rfl

theorem cell19_135431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_135431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135431 prefixEnd_135431 := by exact prefixLift 135431
  have htrace : WordTrace (prefixWord ++ tailWord_135431) baseStart_135431 baseEnd_135431 := by
    simpa [prefixWord, tailWord_135431, baseEnd_135431] using wordTrace_append hprefix tailTrace_135431
  have hstable : (prefixWord ++ tailWord_135431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135431).length < 2 ^ (prefixWord ++ tailWord_135431).sum := by decide
  have hdescent : baseEnd_135431 < baseStart_135431 := by decide
  rcases family_descends (prefixWord ++ tailWord_135431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135433 : List Nat := [1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_135433 : Nat := 118140960795 + 135433 * 2 ^ 59
def prefixEnd_135433 : Nat := 4983230072969 + 3 ^ 40 * 135433 * 2
def baseEnd_135433 : Nat := 41210207692132652719799

theorem tailTrace_135433 : CollatzResearch.WordTrace tailWord_135433 prefixEnd_135433 41210207692132652719799 := by
  unfold tailWord_135433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939647318356845960026953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3293098212237897306684635 4939647318356845960026953)
  ·
    refine ⟨3704735488767634470020215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4939647318356845960026953 3704735488767634470020215)
    ·
      refine ⟨5557103233151451705030323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3704735488767634470020215 5557103233151451705030323)
      ·
        refine ⟨8335654849727177557545485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5557103233151451705030323 8335654849727177557545485)
        ·
          refine ⟨3125870568647691584079557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8335654849727177557545485 3125870568647691584079557)
          ·
            refine ⟨586100731621442172014917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3125870568647691584079557 586100731621442172014917)
            ·
              refine ⟨109893887179020407252797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 586100731621442172014917 109893887179020407252797)
              ·
                refine ⟨41210207692132652719799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109893887179020407252797 41210207692132652719799)
                ·
                  rfl

theorem cell19_135433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_135433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135433 prefixEnd_135433 := by exact prefixLift 135433
  have htrace : WordTrace (prefixWord ++ tailWord_135433) baseStart_135433 baseEnd_135433 := by
    simpa [prefixWord, tailWord_135433, baseEnd_135433] using wordTrace_append hprefix tailTrace_135433
  have hstable : (prefixWord ++ tailWord_135433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135433).length < 2 ^ (prefixWord ++ tailWord_135433).sum := by decide
  have hdescent : baseEnd_135433 < baseStart_135433 := by decide
  rcases family_descends (prefixWord ++ tailWord_135433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135435 : List Nat := [1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_135435 : Nat := 118140960795 + 135435 * 2 ^ 59
def prefixEnd_135435 : Nat := 4983230072969 + 3 ^ 40 * 135435 * 2
def baseEnd_135435 : Nat := 41210816261797240675349

theorem tailTrace_135435 : CollatzResearch.WordTrace tailWord_135435 prefixEnd_135435 41210816261797240675349 := by
  unfold tailWord_135435
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939720264349600301599759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3293146842899733534399839 4939720264349600301599759)
  ·
    refine ⟨7409580396524400452399639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4939720264349600301599759 7409580396524400452399639)
    ·
      refine ⟨11114370594786600678599459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409580396524400452399639 11114370594786600678599459)
      ·
        refine ⟨16671555892179901017899189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11114370594786600678599459 16671555892179901017899189)
        ·
          refine ⟨1562958364891865720428049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16671555892179901017899189 1562958364891865720428049)
          ·
            refine ⟨1172218773668899290321037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562958364891865720428049 1172218773668899290321037)
            ·
              refine ⟨439582040125837233870389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172218773668899290321037 439582040125837233870389)
              ·
                refine ⟨41210816261797240675349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439582040125837233870389 41210816261797240675349)
                ·
                  rfl

theorem cell19_135435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_135435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135435 prefixEnd_135435 := by exact prefixLift 135435
  have htrace : WordTrace (prefixWord ++ tailWord_135435) baseStart_135435 baseEnd_135435 := by
    simpa [prefixWord, tailWord_135435, baseEnd_135435] using wordTrace_append hprefix tailTrace_135435
  have hstable : (prefixWord ++ tailWord_135435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135435).length < 2 ^ (prefixWord ++ tailWord_135435).sum := by decide
  have hdescent : baseEnd_135435 < baseStart_135435 := by decide
  rcases family_descends (prefixWord ++ tailWord_135435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135450 : List Nat := [3, 1, 1, 3, 5, 1, 5]
def baseStart_135450 : Nat := 118140960795 + 135450 * 2 ^ 59
def prefixEnd_135450 : Nat := 4983230072969 + 3 ^ 40 * 135450 * 2
def baseEnd_135450 : Nat := 13738460178093883447325

theorem tailTrace_135450 : CollatzResearch.WordTrace tailWord_135450 prefixEnd_135450 13738460178093883447325 := by
  unfold tailWord_135450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235066839823814465848951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3293511572863505242263869 1235066839823814465848951)
  ·
    refine ⟨1852600259735721698773427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235066839823814465848951 1852600259735721698773427)
    ·
      refine ⟨2778900389603582548160141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852600259735721698773427 2778900389603582548160141)
      ·
        refine ⟨1042087646101343455560053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2778900389603582548160141 1042087646101343455560053)
        ·
          refine ⟨97695716822000948958755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1042087646101343455560053 97695716822000948958755)
          ·
            refine ⟨146543575233001423438133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97695716822000948958755 146543575233001423438133)
            ·
              refine ⟨13738460178093883447325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146543575233001423438133 13738460178093883447325)
              ·
                rfl

theorem cell19_135450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_135450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135450 prefixEnd_135450 := by exact prefixLift 135450
  have htrace : WordTrace (prefixWord ++ tailWord_135450) baseStart_135450 baseEnd_135450 := by
    simpa [prefixWord, tailWord_135450, baseEnd_135450] using wordTrace_append hprefix tailTrace_135450
  have hstable : (prefixWord ++ tailWord_135450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135450).length < 2 ^ (prefixWord ++ tailWord_135450).sum := by decide
  have hdescent : baseEnd_135450 < baseStart_135450 := by decide
  rcases family_descends (prefixWord ++ tailWord_135450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135509 : List Nat := [1, 3, 2, 2, 5, 6]
def baseStart_135509 : Nat := 118140960795 + 135509 * 2 ^ 59
def prefixEnd_135509 : Nat := 4983230072969 + 3 ^ 40 * 135509 * 2
def baseEnd_135509 : Nat := 4581481482154110558967

theorem tailTrace_135509 : CollatzResearch.WordTrace tailWord_135509 prefixEnd_135509 4581481482154110558967 := by
  unfold tailWord_135509
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942419266081510939793581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3294946177387673959862387 4942419266081510939793581)
  ·
    refine ⟨1853407224780566602422593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4942419266081510939793581 1853407224780566602422593)
    ·
      refine ⟨1390055418585424951816945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1853407224780566602422593 1390055418585424951816945)
      ·
        refine ⟨1042541563939068713862709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1390055418585424951816945 1042541563939068713862709)
        ·
          refine ⟨97738271619287691924629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1042541563939068713862709 97738271619287691924629)
          ·
            refine ⟨4581481482154110558967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97738271619287691924629 4581481482154110558967)
            ·
              rfl

theorem cell19_135509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_135509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135509 prefixEnd_135509 := by exact prefixLift 135509
  have htrace : WordTrace (prefixWord ++ tailWord_135509) baseStart_135509 baseEnd_135509 := by
    simpa [prefixWord, tailWord_135509, baseEnd_135509] using wordTrace_append hprefix tailTrace_135509
  have hstable : (prefixWord ++ tailWord_135509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135509).length < 2 ^ (prefixWord ++ tailWord_135509).sum := by decide
  have hdescent : baseEnd_135509 < baseStart_135509 := by decide
  rcases family_descends (prefixWord ++ tailWord_135509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135518 : List Nat := [4, 4, 2, 1, 2, 1, 1, 4]
def baseStart_135518 : Nat := 118140960795 + 135518 * 2 ^ 59
def prefixEnd_135518 : Nat := 4983230072969 + 3 ^ 40 * 135518 * 2
def baseEnd_135518 : Nat := 41236071902877640830679

theorem tailTrace_135518 : CollatzResearch.WordTrace tailWord_135518 prefixEnd_135518 41236071902877640830679 := by
  unfold tailWord_135518
  simp only [CollatzResearch.WordTrace]
  refine ⟨617843440381113184608901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3295165015365936984580805 617843440381113184608901)
  ·
    refine ⟨115845645071458722114169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 617843440381113184608901 115845645071458722114169)
    ·
      refine ⟨86884233803594041585627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115845645071458722114169 86884233803594041585627)
      ·
        refine ⟨130326350705391062378441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86884233803594041585627 130326350705391062378441)
        ·
          refine ⟨97744763029043296783831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130326350705391062378441 97744763029043296783831)
          ·
            refine ⟨146617144543564945175747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97744763029043296783831 146617144543564945175747)
            ·
              refine ⟨219925716815347417763621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146617144543564945175747 219925716815347417763621)
              ·
                refine ⟨41236071902877640830679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219925716815347417763621 41236071902877640830679)
                ·
                  rfl

theorem cell19_135518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_135518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135518 prefixEnd_135518 := by exact prefixLift 135518
  have htrace : WordTrace (prefixWord ++ tailWord_135518) baseStart_135518 baseEnd_135518 := by
    simpa [prefixWord, tailWord_135518, baseEnd_135518] using wordTrace_append hprefix tailTrace_135518
  have hstable : (prefixWord ++ tailWord_135518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135518).length < 2 ^ (prefixWord ++ tailWord_135518).sum := by decide
  have hdescent : baseEnd_135518 < baseStart_135518 := by decide
  rcases family_descends (prefixWord ++ tailWord_135518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135528 : List Nat := [2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_135528 : Nat := 118140960795 + 135528 * 2 ^ 59
def prefixEnd_135528 : Nat := 4983230072969 + 3 ^ 40 * 135528 * 2
def baseEnd_135528 : Nat := 41239114751200580608429

theorem tailTrace_135528 : CollatzResearch.WordTrace tailWord_135528 prefixEnd_135528 41239114751200580608429 := by
  unfold tailWord_135528
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471556126506338592367619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3295408168675118123156825 2471556126506338592367619)
  ·
    refine ⟨3707334189759507888551429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2471556126506338592367619 3707334189759507888551429)
    ·
      refine ⟨695125160579907729103393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3707334189759507888551429 695125160579907729103393)
      ·
        refine ⟨521343870434930796827545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 695125160579907729103393 521343870434930796827545)
        ·
          refine ⟨391007902826198097620659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521343870434930796827545 391007902826198097620659)
          ·
            refine ⟨586511854239297146430989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391007902826198097620659 586511854239297146430989)
            ·
              refine ⟨219941945339736429911621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 586511854239297146430989 219941945339736429911621)
              ·
                refine ⟨41239114751200580608429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219941945339736429911621 41239114751200580608429)
                ·
                  rfl

theorem cell19_135528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_135528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135528 prefixEnd_135528 := by exact prefixLift 135528
  have htrace : WordTrace (prefixWord ++ tailWord_135528) baseStart_135528 baseEnd_135528 := by
    simpa [prefixWord, tailWord_135528, baseEnd_135528] using wordTrace_append hprefix tailTrace_135528
  have hstable : (prefixWord ++ tailWord_135528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135528).length < 2 ^ (prefixWord ++ tailWord_135528).sum := by decide
  have hdescent : baseEnd_135528 < baseStart_135528 := by decide
  rcases family_descends (prefixWord ++ tailWord_135528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135547 : List Nat := [1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_135547 : Nat := 118140960795 + 135547 * 2 ^ 59
def prefixEnd_135547 : Nat := 4983230072969 + 3 ^ 40 * 135547 * 2
def baseEnd_135547 : Nat := 41244896163014166186155

theorem tailTrace_135547 : CollatzResearch.WordTrace tailWord_135547 prefixEnd_135547 41244896163014166186155 := by
  unfold tailWord_135547
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943805239943843429676895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3295870159962562286451263 4943805239943843429676895)
  ·
    refine ⟨7415707859915765144515343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4943805239943843429676895 7415707859915765144515343)
    ·
      refine ⟨11123561789873647716773015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7415707859915765144515343 11123561789873647716773015)
      ·
        refine ⟨16685342684810471575159523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11123561789873647716773015 16685342684810471575159523)
        ·
          refine ⟨25028014027215707362739285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16685342684810471575159523 25028014027215707362739285)
          ·
            refine ⟨293297039381434070657101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 25028014027215707362739285 293297039381434070657101)
            ·
              refine ⟨109986389768037776496413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293297039381434070657101 109986389768037776496413)
              ·
                refine ⟨41244896163014166186155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109986389768037776496413 41244896163014166186155)
                ·
                  rfl

theorem cell19_135547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_135547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135547 prefixEnd_135547 := by exact prefixLift 135547
  have htrace : WordTrace (prefixWord ++ tailWord_135547) baseStart_135547 baseEnd_135547 := by
    simpa [prefixWord, tailWord_135547, baseEnd_135547] using wordTrace_append hprefix tailTrace_135547
  have hstable : (prefixWord ++ tailWord_135547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135547).length < 2 ^ (prefixWord ++ tailWord_135547).sum := by decide
  have hdescent : baseEnd_135547 < baseStart_135547 := by decide
  rcases family_descends (prefixWord ++ tailWord_135547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135566 : List Nat := [4, 1, 1, 4, 1, 2, 6]
def baseStart_135566 : Nat := 118140960795 + 135566 * 2 ^ 59
def prefixEnd_135566 : Nat := 4983230072969 + 3 ^ 40 * 135566 * 2
def baseEnd_135566 : Nat := 13750225858275917254627

theorem tailTrace_135566 : CollatzResearch.WordTrace tailWord_135566 prefixEnd_135566 13750225858275917254627 := by
  unfold tailWord_135566
  simp only [CollatzResearch.WordTrace]
  refine ⟨618062278359376209327319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3296332151250006449745701 618062278359376209327319)
  ·
    refine ⟨927093417539064313990979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618062278359376209327319 927093417539064313990979)
    ·
      refine ⟨1390640126308596470986469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927093417539064313990979 1390640126308596470986469)
      ·
        refine ⟨260745023682861838309963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1390640126308596470986469 260745023682861838309963)
        ·
          refine ⟨391117535524292757464945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260745023682861838309963 391117535524292757464945)
          ·
            refine ⟨293338151643219568098709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391117535524292757464945 293338151643219568098709)
            ·
              refine ⟨13750225858275917254627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 293338151643219568098709 13750225858275917254627)
              ·
                rfl

theorem cell19_135566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_135566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135566 prefixEnd_135566 := by exact prefixLift 135566
  have htrace : WordTrace (prefixWord ++ tailWord_135566) baseStart_135566 baseEnd_135566 := by
    simpa [prefixWord, tailWord_135566, baseEnd_135566] using wordTrace_append hprefix tailTrace_135566
  have hstable : (prefixWord ++ tailWord_135566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135566).length < 2 ^ (prefixWord ++ tailWord_135566).sum := by decide
  have hdescent : baseEnd_135566 < baseStart_135566 := by decide
  rcases family_descends (prefixWord ++ tailWord_135566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135617 : List Nat := [1, 2, 7, 1, 2, 1, 5]
def baseStart_135617 : Nat := 118140960795 + 135617 * 2 ^ 59
def prefixEnd_135617 : Nat := 4983230072969 + 3 ^ 40 * 135617 * 2
def baseEnd_135617 : Nat := 13755398700424914876803

theorem tailTrace_135617 : CollatzResearch.WordTrace tailWord_135617 prefixEnd_135617 13755398700424914876803 := by
  unfold tailWord_135617
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946358349690245384725105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3297572233126830256483403 4946358349690245384725105)
  ·
    refine ⟨3709768762267684038543829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4946358349690245384725105 3709768762267684038543829)
    ·
      refine ⟨86947705365648844653371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3709768762267684038543829 86947705365648844653371)
      ·
        refine ⟨130421558048473266980057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86947705365648844653371 130421558048473266980057)
        ·
          refine ⟨97816168536354950235043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130421558048473266980057 97816168536354950235043)
          ·
            refine ⟨146724252804532425352565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97816168536354950235043 146724252804532425352565)
            ·
              refine ⟨13755398700424914876803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146724252804532425352565 13755398700424914876803)
              ·
                rfl

theorem cell19_135617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_135617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135617 prefixEnd_135617 := by exact prefixLift 135617
  have htrace : WordTrace (prefixWord ++ tailWord_135617) baseStart_135617 baseEnd_135617 := by
    simpa [prefixWord, tailWord_135617, baseEnd_135617] using wordTrace_append hprefix tailTrace_135617
  have hstable : (prefixWord ++ tailWord_135617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135617).length < 2 ^ (prefixWord ++ tailWord_135617).sum := by decide
  have hdescent : baseEnd_135617 < baseStart_135617 := by decide
  rcases family_descends (prefixWord ++ tailWord_135617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135661 : List Nat := [1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_135661 : Nat := 118140960795 + 135661 * 2 ^ 59
def prefixEnd_135661 : Nat := 4983230072969 + 3 ^ 40 * 135661 * 2
def baseEnd_135661 : Nat := 41279584633895679652511

theorem tailTrace_135661 : CollatzResearch.WordTrace tailWord_135661 prefixEnd_135661 41279584633895679652511 := by
  unfold tailWord_135661
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947963161530840899326837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3298642107687227266217891 4947963161530840899326837)
  ·
    refine ⟨463871546393516334311891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4947963161530840899326837 463871546393516334311891)
    ·
      refine ⟨695807319590274501467837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463871546393516334311891 695807319590274501467837)
      ·
        refine ⟨260927744846352938050439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 695807319590274501467837 260927744846352938050439)
        ·
          refine ⟨391391617269529407075659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260927744846352938050439 391391617269529407075659)
          ·
            refine ⟨587087425904294110613489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391391617269529407075659 587087425904294110613489)
            ·
              refine ⟨440315569428220582960117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587087425904294110613489 440315569428220582960117)
              ·
                refine ⟨41279584633895679652511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 440315569428220582960117 41279584633895679652511)
                ·
                  rfl

theorem cell19_135661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_135661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135661 prefixEnd_135661 := by exact prefixLift 135661
  have htrace : WordTrace (prefixWord ++ tailWord_135661) baseStart_135661 baseEnd_135661 := by
    simpa [prefixWord, tailWord_135661, baseEnd_135661] using wordTrace_append hprefix tailTrace_135661
  have hstable : (prefixWord ++ tailWord_135661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135661).length < 2 ^ (prefixWord ++ tailWord_135661).sum := by decide
  have hdescent : baseEnd_135661 < baseStart_135661 := by decide
  rcases family_descends (prefixWord ++ tailWord_135661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135777 : List Nat := [1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_135777 : Nat := 118140960795 + 135777 * 2 ^ 59
def prefixEnd_135777 : Nat := 4983230072969 + 3 ^ 40 * 135777 * 2
def baseEnd_135777 : Nat := 41314881674441781074417

theorem tailTrace_135777 : CollatzResearch.WordTrace tailWord_135777 prefixEnd_135777 41314881674441781074417 := by
  unfold tailWord_135777
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952194029110592710549585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3301462686073728473699723 4952194029110592710549585)
  ·
    refine ⟨3714145521832944532912189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4952194029110592710549585 3714145521832944532912189)
    ·
      refine ⟨1392804570687354199842071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3714145521832944532912189 1392804570687354199842071)
      ·
        refine ⟨2089206856031031299763107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392804570687354199842071 2089206856031031299763107)
        ·
          refine ⟨3133810284046546949644661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089206856031031299763107 3133810284046546949644661)
          ·
            refine ⟨293794714129363776529187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3133810284046546949644661 293794714129363776529187)
            ·
              refine ⟨440692071194045664793781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293794714129363776529187 440692071194045664793781)
              ·
                refine ⟨41314881674441781074417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 440692071194045664793781 41314881674441781074417)
                ·
                  rfl

theorem cell19_135777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_135777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135777 prefixEnd_135777 := by exact prefixLift 135777
  have htrace : WordTrace (prefixWord ++ tailWord_135777) baseStart_135777 baseEnd_135777 := by
    simpa [prefixWord, tailWord_135777, baseEnd_135777] using wordTrace_append hprefix tailTrace_135777
  have hstable : (prefixWord ++ tailWord_135777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135777).length < 2 ^ (prefixWord ++ tailWord_135777).sum := by decide
  have hdescent : baseEnd_135777 < baseStart_135777 := by decide
  rcases family_descends (prefixWord ++ tailWord_135777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135794 : List Nat := [3, 2, 1, 2, 4, 2, 5]
def baseStart_135794 : Nat := 118140960795 + 135794 * 2 ^ 59
def prefixEnd_135794 : Nat := 4983230072969 + 3 ^ 40 * 135794 * 2
def baseEnd_135794 : Nat := 13773351505530259565531

theorem tailTrace_135794 : CollatzResearch.WordTrace tailWord_135794 prefixEnd_135794 13773351505530259565531 := by
  unfold tailWord_135794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238203517512251153479609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3301876046699336409278957 1238203517512251153479609)
  ·
    refine ⟨928652638134188365109707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1238203517512251153479609 928652638134188365109707)
    ·
      refine ⟨1392978957201282547664561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928652638134188365109707 1392978957201282547664561)
      ·
        refine ⟨1044734217900961910748421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392978957201282547664561 1044734217900961910748421)
        ·
          refine ⟨195887665856430358265329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1044734217900961910748421 195887665856430358265329)
          ·
            refine ⟨146915749392322768698997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195887665856430358265329 146915749392322768698997)
            ·
              refine ⟨13773351505530259565531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146915749392322768698997 13773351505530259565531)
              ·
                rfl

theorem cell19_135794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_135794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135794 prefixEnd_135794 := by exact prefixLift 135794
  have htrace : WordTrace (prefixWord ++ tailWord_135794) baseStart_135794 baseEnd_135794 := by
    simpa [prefixWord, tailWord_135794, baseEnd_135794] using wordTrace_append hprefix tailTrace_135794
  have hstable : (prefixWord ++ tailWord_135794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135794).length < 2 ^ (prefixWord ++ tailWord_135794).sum := by decide
  have hdescent : baseEnd_135794 < baseStart_135794 := by decide
  rcases family_descends (prefixWord ++ tailWord_135794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135815 : List Nat := [1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_135815 : Nat := 118140960795 + 135815 * 2 ^ 59
def prefixEnd_135815 : Nat := 4983230072969 + 3 ^ 40 * 135815 * 2
def baseEnd_135815 : Nat := 41326444498068952229869

theorem tailTrace_135815 : CollatzResearch.WordTrace tailWord_135815 prefixEnd_135815 41326444498068952229869 := by
  unfold tailWord_135815
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953580002972925200432899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3302386668648616800288599 4953580002972925200432899)
  ·
    refine ⟨7430370004459387800649349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4953580002972925200432899 7430370004459387800649349)
    ·
      refine ⟨1393194375836135212621753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7430370004459387800649349 1393194375836135212621753)
      ·
        refine ⟨1044895781877101409466315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393194375836135212621753 1044895781877101409466315)
        ·
          refine ⟨1567343672815652114199473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044895781877101409466315 1567343672815652114199473)
          ·
            refine ⟨1175507754611739085649605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1567343672815652114199473 1175507754611739085649605)
            ·
              refine ⟨220407703989701078559301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1175507754611739085649605 220407703989701078559301)
              ·
                refine ⟨41326444498068952229869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220407703989701078559301 41326444498068952229869)
                ·
                  rfl

theorem cell19_135815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_135815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135815 prefixEnd_135815 := by exact prefixLift 135815
  have htrace : WordTrace (prefixWord ++ tailWord_135815) baseStart_135815 baseEnd_135815 := by
    simpa [prefixWord, tailWord_135815, baseEnd_135815] using wordTrace_append hprefix tailTrace_135815
  have hstable : (prefixWord ++ tailWord_135815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135815).length < 2 ^ (prefixWord ++ tailWord_135815).sum := by decide
  have hdescent : baseEnd_135815 < baseStart_135815 := by decide
  rcases family_descends (prefixWord ++ tailWord_135815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135853 : List Nat := [1, 5, 2, 1, 1, 9]
def baseStart_135853 : Nat := 118140960795 + 135853 * 2 ^ 59
def prefixEnd_135853 : Nat := 4983230072969 + 3 ^ 40 * 135853 * 2
def baseEnd_135853 : Nat := 4593111924632902598369

theorem tailTrace_135853 : CollatzResearch.WordTrace tailWord_135853 prefixEnd_135853 4593111924632902598369 := by
  unfold tailWord_135853
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954965976835257690316213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3303310651223505126877475 4954965976835257690316213)
  ·
    refine ⟨464528060328305408467145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4954965976835257690316213 464528060328305408467145)
    ·
      refine ⟨348396045246229056350359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464528060328305408467145 348396045246229056350359)
      ·
        refine ⟨522594067869343584525539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348396045246229056350359 522594067869343584525539)
        ·
          refine ⟨783891101804015376788309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522594067869343584525539 783891101804015376788309)
          ·
            refine ⟨4593111924632902598369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 783891101804015376788309 4593111924632902598369)
            ·
              rfl

theorem cell19_135853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_135853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135853 prefixEnd_135853 := by exact prefixLift 135853
  have htrace : WordTrace (prefixWord ++ tailWord_135853) baseStart_135853 baseEnd_135853 := by
    simpa [prefixWord, tailWord_135853, baseEnd_135853] using wordTrace_append hprefix tailTrace_135853
  have hstable : (prefixWord ++ tailWord_135853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135853).length < 2 ^ (prefixWord ++ tailWord_135853).sum := by decide
  have hdescent : baseEnd_135853 < baseStart_135853 := by decide
  rcases family_descends (prefixWord ++ tailWord_135853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135855 : List Nat := [1, 1, 2, 1, 2, 12]
def baseStart_135855 : Nat := 118140960795 + 135855 * 2 ^ 59
def prefixEnd_135855 : Nat := 4983230072969 + 3 ^ 40 * 135855 * 2
def baseEnd_135855 : Nat := 4593179543484523482319

theorem tailTrace_135855 : CollatzResearch.WordTrace tailWord_135855 prefixEnd_135855 4593179543484523482319 := by
  unfold tailWord_135855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4955038922828012031889019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3303359281885341354592679 4955038922828012031889019)
  ·
    refine ⟨7432558384242018047833529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4955038922828012031889019 7432558384242018047833529)
    ·
      refine ⟨5574418788181513535875147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7432558384242018047833529 5574418788181513535875147)
      ·
        refine ⟨8361628182272270303812721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5574418788181513535875147 8361628182272270303812721)
        ·
          refine ⟨6271221136704202727859541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8361628182272270303812721 6271221136704202727859541)
          ·
            refine ⟨4593179543484523482319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6271221136704202727859541 4593179543484523482319)
            ·
              rfl

theorem cell19_135855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_135855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135855 prefixEnd_135855 := by exact prefixLift 135855
  have htrace : WordTrace (prefixWord ++ tailWord_135855) baseStart_135855 baseEnd_135855 := by
    simpa [prefixWord, tailWord_135855, baseEnd_135855] using wordTrace_append hprefix tailTrace_135855
  have hstable : (prefixWord ++ tailWord_135855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135855).length < 2 ^ (prefixWord ++ tailWord_135855).sum := by decide
  have hdescent : baseEnd_135855 < baseStart_135855 := by decide
  rcases family_descends (prefixWord ++ tailWord_135855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135872 : List Nat := [2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_135872 : Nat := 118140960795 + 135872 * 2 ^ 59
def prefixEnd_135872 : Nat := 4983230072969 + 3 ^ 40 * 135872 * 2
def baseEnd_135872 : Nat := 41343788733509708963047

theorem tailTrace_135872 : CollatzResearch.WordTrace tailWord_135872 prefixEnd_135872 41343788733509708963047 := by
  unfold tailWord_135872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477829481883211967628935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3303772642510949290171913 2477829481883211967628935)
  ·
    refine ⟨3716744222824817951443403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2477829481883211967628935 3716744222824817951443403)
    ·
      refine ⟨5575116334237226927165105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716744222824817951443403 5575116334237226927165105)
      ·
        refine ⟨4181337250677920195373829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5575116334237226927165105 4181337250677920195373829)
        ·
          refine ⟨784000734502110036632593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4181337250677920195373829 784000734502110036632593)
          ·
            refine ⟨588000550876582527474445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784000734502110036632593 588000550876582527474445)
            ·
              refine ⟨220500206578718447802917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 588000550876582527474445 220500206578718447802917)
              ·
                refine ⟨41343788733509708963047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220500206578718447802917 41343788733509708963047)
                ·
                  rfl

theorem cell19_135872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_135872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135872 prefixEnd_135872 := by exact prefixLift 135872
  have htrace : WordTrace (prefixWord ++ tailWord_135872) baseStart_135872 baseEnd_135872 := by
    simpa [prefixWord, tailWord_135872, baseEnd_135872] using wordTrace_append hprefix tailTrace_135872
  have hstable : (prefixWord ++ tailWord_135872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135872).length < 2 ^ (prefixWord ++ tailWord_135872).sum := by decide
  have hdescent : baseEnd_135872 < baseStart_135872 := by decide
  rcases family_descends (prefixWord ++ tailWord_135872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135885 : List Nat := [1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_135885 : Nat := 118140960795 + 135885 * 2 ^ 59
def prefixEnd_135885 : Nat := 4983230072969 + 3 ^ 40 * 135885 * 2
def baseEnd_135885 : Nat := 41347744436329530674123

theorem tailTrace_135885 : CollatzResearch.WordTrace tailWord_135885 prefixEnd_135885 41347744436329530674123 := by
  unfold tailWord_135885
  simp only [CollatzResearch.WordTrace]
  refine ⟨4956133112719327155481109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3304088741812884770320739 4956133112719327155481109)
  ·
    refine ⟨232318739658718460413177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4956133112719327155481109 232318739658718460413177)
    ·
      refine ⟨174239054744038845309883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232318739658718460413177 174239054744038845309883)
      ·
        refine ⟨261358582116058267964825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174239054744038845309883 261358582116058267964825)
        ·
          refine ⟨196018936587043700973619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261358582116058267964825 196018936587043700973619)
          ·
            refine ⟨294028404880565551460429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196018936587043700973619 294028404880565551460429)
            ·
              refine ⟨110260651830212081797661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 294028404880565551460429 110260651830212081797661)
              ·
                refine ⟨41347744436329530674123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110260651830212081797661 41347744436329530674123)
                ·
                  rfl

theorem cell19_135885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_135885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135885 prefixEnd_135885 := by exact prefixLift 135885
  have htrace : WordTrace (prefixWord ++ tailWord_135885) baseStart_135885 baseEnd_135885 := by
    simpa [prefixWord, tailWord_135885, baseEnd_135885] using wordTrace_append hprefix tailTrace_135885
  have hstable : (prefixWord ++ tailWord_135885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135885).length < 2 ^ (prefixWord ++ tailWord_135885).sum := by decide
  have hdescent : baseEnd_135885 < baseStart_135885 := by decide
  rcases family_descends (prefixWord ++ tailWord_135885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135967 : List Nat := [1, 1, 2, 4, 2, 4, 5]
def baseStart_135967 : Nat := 118140960795 + 135967 * 2 ^ 59
def prefixEnd_135967 : Nat := 4983230072969 + 3 ^ 40 * 135967 * 2
def baseEnd_135967 : Nat := 13790898597525878950559

theorem tailTrace_135967 : CollatzResearch.WordTrace tailWord_135967 prefixEnd_135967 13790898597525878950559 := by
  unfold tailWord_135967
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959123898422255159966155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3306082598948170106644103 4959123898422255159966155)
  ·
    refine ⟨7438685847633382739949233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4959123898422255159966155 7438685847633382739949233)
    ·
      refine ⟨5579014385725037054961925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7438685847633382739949233 5579014385725037054961925)
      ·
        refine ⟨1046065197323444447805361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5579014385725037054961925 1046065197323444447805361)
        ·
          refine ⟨784548897992583335854021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046065197323444447805361 784548897992583335854021)
          ·
            refine ⟨147102918373609375472629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 784548897992583335854021 147102918373609375472629)
            ·
              refine ⟨13790898597525878950559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147102918373609375472629 13790898597525878950559)
              ·
                rfl

theorem cell19_135967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_135967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135967 prefixEnd_135967 := by exact prefixLift 135967
  have htrace : WordTrace (prefixWord ++ tailWord_135967) baseStart_135967 baseEnd_135967 := by
    simpa [prefixWord, tailWord_135967, baseEnd_135967] using wordTrace_append hprefix tailTrace_135967
  have hstable : (prefixWord ++ tailWord_135967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135967).length < 2 ^ (prefixWord ++ tailWord_135967).sum := by decide
  have hdescent : baseEnd_135967 < baseStart_135967 := by decide
  rcases family_descends (prefixWord ++ tailWord_135967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135986 : List Nat := [3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_135986 : Nat := 118140960795 + 135986 * 2 ^ 59
def prefixEnd_135986 : Nat := 4983230072969 + 3 ^ 40 * 135986 * 2
def baseEnd_135986 : Nat := 41378477204391222429403

theorem tailTrace_135986 : CollatzResearch.WordTrace tailWord_135986 prefixEnd_135986 41378477204391222429403 := by
  unfold tailWord_135986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239954221338355351226953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3306544590235614269938541 1239954221338355351226953)
  ·
    refine ⟨929965666003766513420215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239954221338355351226953 929965666003766513420215)
    ·
      refine ⟨1394948499005649770130323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929965666003766513420215 1394948499005649770130323)
      ·
        refine ⟨2092422748508474655195485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394948499005649770130323 2092422748508474655195485)
        ·
          refine ⟨784658530690677995698307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2092422748508474655195485 784658530690677995698307)
          ·
            refine ⟨1176987796036016993547461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784658530690677995698307 1176987796036016993547461)
            ·
              refine ⟨220685211756753186290149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1176987796036016993547461 220685211756753186290149)
              ·
                refine ⟨41378477204391222429403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220685211756753186290149 41378477204391222429403)
                ·
                  rfl

theorem cell19_135986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_135986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_135986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_135986 prefixEnd_135986 := by exact prefixLift 135986
  have htrace : WordTrace (prefixWord ++ tailWord_135986) baseStart_135986 baseEnd_135986 := by
    simpa [prefixWord, tailWord_135986, baseEnd_135986] using wordTrace_append hprefix tailTrace_135986
  have hstable : (prefixWord ++ tailWord_135986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135986).length < 2 ^ (prefixWord ++ tailWord_135986).sum := by decide
  have hdescent : baseEnd_135986 < baseStart_135986 := by decide
  rcases family_descends (prefixWord ++ tailWord_135986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136026 : List Nat := [3, 1, 1, 2, 1, 11]
def baseStart_136026 : Nat := 118140960795 + 136026 * 2 ^ 59
def prefixEnd_136026 : Nat := 4983230072969 + 3 ^ 40 * 136026 * 2
def baseEnd_136026 : Nat := 4598960955298109060045

theorem tailTrace_136026 : CollatzResearch.WordTrace tailWord_136026 prefixEnd_136026 4598960955298109060045 := by
  unfold tailWord_136026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240318951302127059090983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3307517203472338824242621 1240318951302127059090983)
  ·
    refine ⟨1860478426953190588636475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1240318951302127059090983 1860478426953190588636475)
    ·
      refine ⟨2790717640429785882954713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860478426953190588636475 2790717640429785882954713)
      ·
        refine ⟨2093038230322339412216035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2790717640429785882954713 2093038230322339412216035)
        ·
          refine ⟨3139557345483509118324053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093038230322339412216035 3139557345483509118324053)
          ·
            refine ⟨4598960955298109060045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3139557345483509118324053 4598960955298109060045)
            ·
              rfl

theorem cell19_136026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_136026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136026 prefixEnd_136026 := by exact prefixLift 136026
  have htrace : WordTrace (prefixWord ++ tailWord_136026) baseStart_136026 baseEnd_136026 := by
    simpa [prefixWord, tailWord_136026, baseEnd_136026] using wordTrace_append hprefix tailTrace_136026
  have hstable : (prefixWord ++ tailWord_136026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136026).length < 2 ^ (prefixWord ++ tailWord_136026).sum := by decide
  have hdescent : baseEnd_136026 < baseStart_136026 := by decide
  rcases family_descends (prefixWord ++ tailWord_136026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136119 : List Nat := [1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_136119 : Nat := 118140960795 + 136119 * 2 ^ 59
def prefixEnd_136119 : Nat := 4983230072969 + 3 ^ 40 * 136119 * 2
def baseEnd_136119 : Nat := 41418947087086321473485

theorem tailTrace_136119 : CollatzResearch.WordTrace tailWord_136119 prefixEnd_136119 41418947087086321473485 := by
  unfold tailWord_136119
  simp only [CollatzResearch.WordTrace]
  refine ⟨4964667793871585119499411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3309778529247723412999607 4964667793871585119499411)
  ·
    refine ⟨7447001690807377679249117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4964667793871585119499411 7447001690807377679249117)
    ·
      refine ⟨2792625634052766629718419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7447001690807377679249117 2792625634052766629718419)
      ·
        refine ⟨4188938451079149944577629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792625634052766629718419 4188938451079149944577629)
        ·
          refine ⟨1570851919154681229216611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4188938451079149944577629 1570851919154681229216611)
          ·
            refine ⟨2356277878732021843824917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570851919154681229216611 2356277878732021843824917)
            ·
              refine ⟨110450525565563523929293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2356277878732021843824917 110450525565563523929293)
              ·
                refine ⟨41418947087086321473485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110450525565563523929293 41418947087086321473485)
                ·
                  rfl

theorem cell19_136119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_136119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136119 prefixEnd_136119 := by exact prefixLift 136119
  have htrace : WordTrace (prefixWord ++ tailWord_136119) baseStart_136119 baseEnd_136119 := by
    simpa [prefixWord, tailWord_136119, baseEnd_136119] using wordTrace_append hprefix tailTrace_136119
  have hstable : (prefixWord ++ tailWord_136119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136119).length < 2 ^ (prefixWord ++ tailWord_136119).sum := by decide
  have hdescent : baseEnd_136119 < baseStart_136119 := by decide
  rcases family_descends (prefixWord ++ tailWord_136119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136136 : List Nat := [2, 1, 3, 1, 6, 1, 5]
def baseStart_136136 : Nat := 118140960795 + 136136 * 2 ^ 59
def prefixEnd_136136 : Nat := 4983230072969 + 3 ^ 40 * 136136 * 2
def baseEnd_136136 : Nat := 13808039976411773031887

theorem tailTrace_136136 : CollatzResearch.WordTrace tailWord_136136 prefixEnd_136136 13808039976411773031887 := by
  unfold tailWord_136136
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482643917404998511434131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3310191889873331348578841 2482643917404998511434131)
  ·
    refine ⟨3723965876107497767151197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2482643917404998511434131 3723965876107497767151197)
    ·
      refine ⟨1396487203540311662681699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3723965876107497767151197 1396487203540311662681699)
      ·
        refine ⟨2094730805310467494022549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396487203540311662681699 2094730805310467494022549)
        ·
          refine ⟨98190506498928163782307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2094730805310467494022549 98190506498928163782307)
          ·
            refine ⟨147285759748392245673461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98190506498928163782307 147285759748392245673461)
            ·
              refine ⟨13808039976411773031887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147285759748392245673461 13808039976411773031887)
              ·
                rfl

theorem cell19_136136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_136136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136136 prefixEnd_136136 := by exact prefixLift 136136
  have htrace : WordTrace (prefixWord ++ tailWord_136136) baseStart_136136 baseEnd_136136 := by
    simpa [prefixWord, tailWord_136136, baseEnd_136136] using wordTrace_append hprefix tailTrace_136136
  have hstable : (prefixWord ++ tailWord_136136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136136).length < 2 ^ (prefixWord ++ tailWord_136136).sum := by decide
  have hdescent : baseEnd_136136 < baseStart_136136 := by decide
  rcases family_descends (prefixWord ++ tailWord_136136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136157 : List Nat := [1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_136157 : Nat := 118140960795 + 136157 * 2 ^ 59
def prefixEnd_136157 : Nat := 4983230072969 + 3 ^ 40 * 136157 * 2
def baseEnd_136157 : Nat := 41430509910713492628937

theorem tailTrace_136157 : CollatzResearch.WordTrace tailWord_136157 prefixEnd_136157 41430509910713492628937 := by
  unfold tailWord_136157
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966053767733917609382725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3310702511822611739588483 4966053767733917609382725)
  ·
    refine ⟨931135081450109551759261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4966053767733917609382725 931135081450109551759261)
    ·
      refine ⟨349175655543791081909723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 931135081450109551759261 349175655543791081909723)
      ·
        refine ⟨523763483315686622864585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349175655543791081909723 523763483315686622864585)
        ·
          refine ⟨392822612486764967148439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523763483315686622864585 392822612486764967148439)
          ·
            refine ⟨589233918730147450722659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392822612486764967148439 589233918730147450722659)
            ·
              refine ⟨883850878095221176083989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589233918730147450722659 883850878095221176083989)
              ·
                refine ⟨41430509910713492628937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 883850878095221176083989 41430509910713492628937)
                ·
                  rfl

theorem cell19_136157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_136157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136157 prefixEnd_136157 := by exact prefixLift 136157
  have htrace : WordTrace (prefixWord ++ tailWord_136157) baseStart_136157 baseEnd_136157 := by
    simpa [prefixWord, tailWord_136157, baseEnd_136157] using wordTrace_append hprefix tailTrace_136157
  have hstable : (prefixWord ++ tailWord_136157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136157).length < 2 ^ (prefixWord ++ tailWord_136157).sum := by decide
  have hdescent : baseEnd_136157 < baseStart_136157 := by decide
  rcases family_descends (prefixWord ++ tailWord_136157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136286 : List Nat := [4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_136286 : Nat := 118140960795 + 136286 * 2 ^ 59
def prefixEnd_136286 : Nat := 4983230072969 + 3 ^ 40 * 136286 * 2
def baseEnd_136286 : Nat := 41469762654079415761919

theorem tailTrace_136286 : CollatzResearch.WordTrace tailWord_136286 prefixEnd_136286 41469762654079415761919 := by
  unfold tailWord_136286
  simp only [CollatzResearch.WordTrace]
  refine ⟨621344848033321580103589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3313839189511048427219141 621344848033321580103589)
  ·
    refine ⟨116502159006247796269423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 621344848033321580103589 116502159006247796269423)
    ·
      refine ⟨174753238509371694404135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116502159006247796269423 174753238509371694404135)
      ·
        refine ⟨262129857764057541606203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174753238509371694404135 262129857764057541606203)
        ·
          refine ⟨393194786646086312409305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262129857764057541606203 393194786646086312409305)
          ·
            refine ⟨294896089984564734306979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393194786646086312409305 294896089984564734306979)
            ·
              refine ⟨442344134976847101460469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294896089984564734306979 442344134976847101460469)
              ·
                refine ⟨41469762654079415761919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 442344134976847101460469 41469762654079415761919)
                ·
                  rfl

theorem cell19_136286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_136286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136286 prefixEnd_136286 := by exact prefixLift 136286
  have htrace : WordTrace (prefixWord ++ tailWord_136286) baseStart_136286 baseEnd_136286 := by
    simpa [prefixWord, tailWord_136286, baseEnd_136286] using wordTrace_append hprefix tailTrace_136286
  have hstable : (prefixWord ++ tailWord_136286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136286).length < 2 ^ (prefixWord ++ tailWord_136286).sum := by decide
  have hdescent : baseEnd_136286 < baseStart_136286 := by decide
  rcases family_descends (prefixWord ++ tailWord_136286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136349 : List Nat := [1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_136349 : Nat := 118140960795 + 136349 * 2 ^ 59
def prefixEnd_136349 : Nat := 4983230072969 + 3 ^ 40 * 136349 * 2
def baseEnd_136349 : Nat := 41488932598513936361747

theorem tailTrace_136349 : CollatzResearch.WordTrace tailWord_136349 prefixEnd_136349 41488932598513936361747 := by
  unfold tailWord_136349
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973056583038334400372101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3315371055358889600248067 4973056583038334400372101)
  ·
    refine ⟨932448109319687700069769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4973056583038334400372101 932448109319687700069769)
    ·
      refine ⟨699336081989765775052327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 932448109319687700069769 699336081989765775052327)
      ·
        refine ⟨1049004122984648662578491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699336081989765775052327 1049004122984648662578491)
        ·
          refine ⟨1573506184476972993867737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049004122984648662578491 1573506184476972993867737)
          ·
            refine ⟨1180129638357729745400803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573506184476972993867737 1180129638357729745400803)
            ·
              refine ⟨1770194457536594618101205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180129638357729745400803 1770194457536594618101205)
              ·
                refine ⟨41488932598513936361747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1770194457536594618101205 41488932598513936361747)
                ·
                  rfl

theorem cell19_136349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_136349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136349 prefixEnd_136349 := by exact prefixLift 136349
  have htrace : WordTrace (prefixWord ++ tailWord_136349) baseStart_136349 baseEnd_136349 := by
    simpa [prefixWord, tailWord_136349, baseEnd_136349] using wordTrace_append hprefix tailTrace_136349
  have hstable : (prefixWord ++ tailWord_136349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136349).length < 2 ^ (prefixWord ++ tailWord_136349).sum := by decide
  have hdescent : baseEnd_136349 < baseStart_136349 := by decide
  rcases family_descends (prefixWord ++ tailWord_136349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136423 : List Nat := [1, 1, 5, 3, 2, 1, 6]
def baseStart_136423 : Nat := 118140960795 + 136423 * 2 ^ 59
def prefixEnd_136423 : Nat := 4983230072969 + 3 ^ 40 * 136423 * 2
def baseEnd_136423 : Nat := 13837149892034563572367

theorem tailTrace_136423 : CollatzResearch.WordTrace tailWord_136423 prefixEnd_136423 13837149892034563572367 := by
  unfold tailWord_136423
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975755584770245038565923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3317170389846830025710615 4975755584770245038565923)
  ·
    refine ⟨7463633377155367557848885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4975755584770245038565923 7463633377155367557848885)
    ·
      refine ⟨699715629108315708548333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7463633377155367557848885 699715629108315708548333)
      ·
        refine ⟨262393360915618390705625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 699715629108315708548333 262393360915618390705625)
        ·
          refine ⟨196795020686713793029219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262393360915618390705625 196795020686713793029219)
          ·
            refine ⟨295192531030070689543829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196795020686713793029219 295192531030070689543829)
            ·
              refine ⟨13837149892034563572367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 295192531030070689543829 13837149892034563572367)
              ·
                rfl

theorem cell19_136423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_136423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136423 prefixEnd_136423 := by exact prefixLift 136423
  have htrace : WordTrace (prefixWord ++ tailWord_136423) baseStart_136423 baseEnd_136423 := by
    simpa [prefixWord, tailWord_136423, baseEnd_136423] using wordTrace_append hprefix tailTrace_136423
  have hstable : (prefixWord ++ tailWord_136423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136423).length < 2 ^ (prefixWord ++ tailWord_136423).sum := by decide
  have hdescent : baseEnd_136423 < baseStart_136423 := by decide
  rcases family_descends (prefixWord ++ tailWord_136423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136480 : List Nat := [2, 1, 1, 5, 3, 2, 5]
def baseStart_136480 : Nat := 118140960795 + 136480 * 2 ^ 59
def prefixEnd_136480 : Nat := 4983230072969 + 3 ^ 40 * 136480 * 2
def baseEnd_136480 : Nat := 13842931303848149150093

theorem tailTrace_136480 : CollatzResearch.WordTrace tailWord_136480 prefixEnd_136480 13842931303848149150093 := by
  unfold tailWord_136480
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488917272781871886695447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3318556363709162515593929 2488917272781871886695447)
  ·
    refine ⟨3733375909172807830043171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2488917272781871886695447 3733375909172807830043171)
    ·
      refine ⟨5600063863759211745064757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3733375909172807830043171 5600063863759211745064757)
      ·
        refine ⟨525005987227426101099821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5600063863759211745064757 525005987227426101099821)
        ·
          refine ⟨196877245210284787912433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 525005987227426101099821 196877245210284787912433)
          ·
            refine ⟨147657933907713590934325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196877245210284787912433 147657933907713590934325)
            ·
              refine ⟨13842931303848149150093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147657933907713590934325 13842931303848149150093)
              ·
                rfl

theorem cell19_136480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_136480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136480 prefixEnd_136480 := by exact prefixLift 136480
  have htrace : WordTrace (prefixWord ++ tailWord_136480) baseStart_136480 baseEnd_136480 := by
    simpa [prefixWord, tailWord_136480, baseEnd_136480] using wordTrace_append hprefix tailTrace_136480
  have hstable : (prefixWord ++ tailWord_136480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136480).length < 2 ^ (prefixWord ++ tailWord_136480).sum := by decide
  have hdescent : baseEnd_136480 < baseStart_136480 := by decide
  rcases family_descends (prefixWord ++ tailWord_136480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136501 : List Nat := [1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_136501 : Nat := 118140960795 + 136501 * 2 ^ 59
def prefixEnd_136501 : Nat := 4983230072969 + 3 ^ 40 * 136501 * 2
def baseEnd_136501 : Nat := 41535183893022620983555

theorem tailTrace_136501 : CollatzResearch.WordTrace tailWord_136501 prefixEnd_136501 41535183893022620983555 := by
  unfold tailWord_136501
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978600478487664359905357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3319066985658442906603571 4978600478487664359905357)
  ·
    refine ⟨1866975179432874134964509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4978600478487664359905357 1866975179432874134964509)
    ·
      refine ⟨700115692287327800611691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1866975179432874134964509 700115692287327800611691)
      ·
        refine ⟨1050173538430991700917537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700115692287327800611691 1050173538430991700917537)
        ·
          refine ⟨787630153823243775688153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1050173538430991700917537 787630153823243775688153)
          ·
            refine ⟨590722615367432831766115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787630153823243775688153 590722615367432831766115)
            ·
              refine ⟨886083923051149247649173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590722615367432831766115 886083923051149247649173)
              ·
                refine ⟨41535183893022620983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 886083923051149247649173 41535183893022620983555)
                ·
                  rfl

theorem cell19_136501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_136501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136501 prefixEnd_136501 := by exact prefixLift 136501
  have htrace : WordTrace (prefixWord ++ tailWord_136501) baseStart_136501 baseEnd_136501 := by
    simpa [prefixWord, tailWord_136501, baseEnd_136501] using wordTrace_append hprefix tailTrace_136501
  have hstable : (prefixWord ++ tailWord_136501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136501).length < 2 ^ (prefixWord ++ tailWord_136501).sum := by decide
  have hdescent : baseEnd_136501 < baseStart_136501 := by decide
  rcases family_descends (prefixWord ++ tailWord_136501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136554 : List Nat := [3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_136554 : Nat := 118140960795 + 136554 * 2 ^ 59
def prefixEnd_136554 : Nat := 4983230072969 + 3 ^ 40 * 136554 * 2
def baseEnd_136554 : Nat := 41551310989134201805633

theorem tailTrace_136554 : CollatzResearch.WordTrace tailWord_136554 prefixEnd_136554 41551310989134201805633 := by
  unfold tailWord_136554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245133386823913602896179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3320355698197102941056477 1245133386823913602896179)
  ·
    refine ⟨1867700080235870404344269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245133386823913602896179 1867700080235870404344269)
    ·
      refine ⟨700387530088451401629101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1867700080235870404344269 700387530088451401629101)
      ·
        refine ⟨262645323783169275610913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 700387530088451401629101 262645323783169275610913)
        ·
          refine ⟨196983992837376956708185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262645323783169275610913 196983992837376956708185)
          ·
            refine ⟨147737994628032717531139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196983992837376956708185 147737994628032717531139)
            ·
              refine ⟨221606991942049076296709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147737994628032717531139 221606991942049076296709)
              ·
                refine ⟨41551310989134201805633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221606991942049076296709 41551310989134201805633)
                ·
                  rfl

theorem cell19_136554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_136554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136554 prefixEnd_136554 := by exact prefixLift 136554
  have htrace : WordTrace (prefixWord ++ tailWord_136554) baseStart_136554 baseEnd_136554 := by
    simpa [prefixWord, tailWord_136554, baseEnd_136554] using wordTrace_append hprefix tailTrace_136554
  have hstable : (prefixWord ++ tailWord_136554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136554).length < 2 ^ (prefixWord ++ tailWord_136554).sum := by decide
  have hdescent : baseEnd_136554 < baseStart_136554 := by decide
  rcases family_descends (prefixWord ++ tailWord_136554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136556 : List Nat := [2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_136556 : Nat := 118140960795 + 136556 * 2 ^ 59
def prefixEnd_136556 : Nat := 4983230072969 + 3 ^ 40 * 136556 * 2
def baseEnd_136556 : Nat := 41551919558798789761183

theorem tailTrace_136556 : CollatzResearch.WordTrace tailWord_136556 prefixEnd_136556 41551919558798789761183 := by
  unfold tailWord_136556
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490303246644204376578761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3320404328858939168771681 2490303246644204376578761)
  ·
    refine ⟨1867727434983153282434071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2490303246644204376578761 1867727434983153282434071)
    ·
      refine ⟨2801591152474729923651107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1867727434983153282434071 2801591152474729923651107)
      ·
        refine ⟨4202386728712094885476661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801591152474729923651107 4202386728712094885476661)
        ·
          refine ⟨393973755816758895513437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4202386728712094885476661 393973755816758895513437)
          ·
            refine ⟨147740158431284585817539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393973755816758895513437 147740158431284585817539)
            ·
              refine ⟨221610237646926878726309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147740158431284585817539 221610237646926878726309)
              ·
                refine ⟨41551919558798789761183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221610237646926878726309 41551919558798789761183)
                ·
                  rfl

theorem cell19_136556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_136556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136556 prefixEnd_136556 := by exact prefixLift 136556
  have htrace : WordTrace (prefixWord ++ tailWord_136556) baseStart_136556 baseEnd_136556 := by
    simpa [prefixWord, tailWord_136556, baseEnd_136556] using wordTrace_append hprefix tailTrace_136556
  have hstable : (prefixWord ++ tailWord_136556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136556).length < 2 ^ (prefixWord ++ tailWord_136556).sum := by decide
  have hdescent : baseEnd_136556 < baseStart_136556 := by decide
  rcases family_descends (prefixWord ++ tailWord_136556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136615 : List Nat := [1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_136615 : Nat := 118140960795 + 136615 * 2 ^ 59
def prefixEnd_136615 : Nat := 4983230072969 + 3 ^ 40 * 136615 * 2
def baseEnd_136615 : Nat := 41569872363904134449911

theorem tailTrace_136615 : CollatzResearch.WordTrace tailWord_136615 prefixEnd_136615 41569872363904134449911 := by
  unfold tailWord_136615
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982758400074661829555299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3321838933383107886370199 4982758400074661829555299)
  ·
    refine ⟨7474137600111992744332949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4982758400074661829555299 7474137600111992744332949)
    ·
      refine ⟨350350200005249659890607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7474137600111992744332949 350350200005249659890607)
      ·
        refine ⟨525525300007874489835911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350350200005249659890607 525525300007874489835911)
        ·
          refine ⟨788287950011811734753867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525525300007874489835911 788287950011811734753867)
          ·
            refine ⟨1182431925017717602130801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788287950011811734753867 1182431925017717602130801)
            ·
              refine ⟨886823943763288201598101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182431925017717602130801 886823943763288201598101)
              ·
                refine ⟨41569872363904134449911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 886823943763288201598101 41569872363904134449911)
                ·
                  rfl

theorem cell19_136615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_136615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136615 prefixEnd_136615 := by exact prefixLift 136615
  have htrace : WordTrace (prefixWord ++ tailWord_136615) baseStart_136615 baseEnd_136615 := by
    simpa [prefixWord, tailWord_136615, baseEnd_136615] using wordTrace_append hprefix tailTrace_136615
  have hstable : (prefixWord ++ tailWord_136615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136615).length < 2 ^ (prefixWord ++ tailWord_136615).sum := by decide
  have hdescent : baseEnd_136615 < baseStart_136615 := by decide
  rcases family_descends (prefixWord ++ tailWord_136615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136655 : List Nat := [1, 1, 2, 1, 1, 4, 9]
def baseStart_136655 : Nat := 118140960795 + 136655 * 2 ^ 59
def prefixEnd_136655 : Nat := 4983230072969 + 3 ^ 40 * 136655 * 2
def baseEnd_136655 : Nat := 13860681252398631186971

theorem tailTrace_136655 : CollatzResearch.WordTrace tailWord_136655 prefixEnd_136655 13860681252398631186971 := by
  unfold tailWord_136655
  simp only [CollatzResearch.WordTrace]
  refine ⟨4984217319929748661011419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3322811546619832440674279 4984217319929748661011419)
  ·
    refine ⟨7476325979894622991517129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4984217319929748661011419 7476325979894622991517129)
    ·
      refine ⟨5607244484920967243637847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7476325979894622991517129 5607244484920967243637847)
      ·
        refine ⟨8410866727381450865456771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5607244484920967243637847 8410866727381450865456771)
        ·
          refine ⟨12616300091072176298185157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8410866727381450865456771 12616300091072176298185157)
          ·
            refine ⟨2365556267076033055909717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12616300091072176298185157 2365556267076033055909717)
            ·
              refine ⟨13860681252398631186971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2365556267076033055909717 13860681252398631186971)
              ·
                rfl

theorem cell19_136655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_136655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136655 prefixEnd_136655 := by exact prefixLift 136655
  have htrace : WordTrace (prefixWord ++ tailWord_136655) baseStart_136655 baseEnd_136655 := by
    simpa [prefixWord, tailWord_136655, baseEnd_136655] using wordTrace_append hprefix tailTrace_136655
  have hstable : (prefixWord ++ tailWord_136655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136655).length < 2 ^ (prefixWord ++ tailWord_136655).sum := by decide
  have hdescent : baseEnd_136655 < baseStart_136655 := by decide
  rcases family_descends (prefixWord ++ tailWord_136655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136708 : List Nat := [2, 3, 2, 3, 3, 6]
def baseStart_136708 : Nat := 118140960795 + 136708 * 2 ^ 59
def prefixEnd_136708 : Nat := 4983230072969 + 3 ^ 40 * 136708 * 2
def baseEnd_136708 : Nat := 4622018983700830486999

theorem tailTrace_136708 : CollatzResearch.WordTrace tailWord_136708 prefixEnd_136708 4622018983700830486999 := by
  unfold tailWord_136708
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493075194368869356345389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3324100259158492475127185 2493075194368869356345389)
  ·
    refine ⟨934903197888326008629521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2493075194368869356345389 934903197888326008629521)
    ·
      refine ⟨701177398416244506472141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 934903197888326008629521 701177398416244506472141)
      ·
        refine ⟨262941524406091689927053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 701177398416244506472141 262941524406091689927053)
        ·
          refine ⟨98603071652284383722645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262941524406091689927053 98603071652284383722645)
          ·
            refine ⟨4622018983700830486999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98603071652284383722645 4622018983700830486999)
            ·
              rfl

theorem cell19_136708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_136708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136708 prefixEnd_136708 := by exact prefixLift 136708
  have htrace : WordTrace (prefixWord ++ tailWord_136708) baseStart_136708 baseEnd_136708 := by
    simpa [prefixWord, tailWord_136708, baseEnd_136708] using wordTrace_append hprefix tailTrace_136708
  have hstable : (prefixWord ++ tailWord_136708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136708).length < 2 ^ (prefixWord ++ tailWord_136708).sum := by decide
  have hdescent : baseEnd_136708 < baseStart_136708 := by decide
  rcases family_descends (prefixWord ++ tailWord_136708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136744 : List Nat := [2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_136744 : Nat := 118140960795 + 136744 * 2 ^ 59
def prefixEnd_136744 : Nat := 4983230072969 + 3 ^ 40 * 136744 * 2
def baseEnd_136744 : Nat := 41609125107270057582893

theorem tailTrace_136744 : CollatzResearch.WordTrace tailWord_136744 prefixEnd_136744 41609125107270057582893 := by
  unfold tailWord_136744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493731708303658430500643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3324975611071544574000857 2493731708303658430500643)
  ·
    refine ⟨3740597562455487645750965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493731708303658430500643 3740597562455487645750965)
    ·
      refine ⟨350681021480201966789153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3740597562455487645750965 350681021480201966789153)
      ·
        refine ⟨263010766110151475091865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350681021480201966789153 263010766110151475091865)
        ·
          refine ⟨197258074582613606318899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263010766110151475091865 197258074582613606318899)
          ·
            refine ⟨295887111873920409478349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197258074582613606318899 295887111873920409478349)
            ·
              refine ⟨110957666952720153554381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295887111873920409478349 110957666952720153554381)
              ·
                refine ⟨41609125107270057582893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110957666952720153554381 41609125107270057582893)
                ·
                  rfl

theorem cell19_136744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_136744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136744 prefixEnd_136744 := by exact prefixLift 136744
  have htrace : WordTrace (prefixWord ++ tailWord_136744) baseStart_136744 baseEnd_136744 := by
    simpa [prefixWord, tailWord_136744, baseEnd_136744] using wordTrace_append hprefix tailTrace_136744
  have hstable : (prefixWord ++ tailWord_136744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136744).length < 2 ^ (prefixWord ++ tailWord_136744).sum := by decide
  have hdescent : baseEnd_136744 < baseStart_136744 := by decide
  rcases family_descends (prefixWord ++ tailWord_136744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136746 : List Nat := [3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_136746 : Nat := 118140960795 + 136746 * 2 ^ 59
def prefixEnd_136746 : Nat := 4983230072969 + 3 ^ 40 * 136746 * 2
def baseEnd_136746 : Nat := 41609733676934645538443

theorem tailTrace_136746 : CollatzResearch.WordTrace tailWord_136746 prefixEnd_136746 41609733676934645538443 := by
  unfold tailWord_136746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246884090650017800643523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3325024241733380801716061 1246884090650017800643523)
  ·
    refine ⟨1870326135975026700965285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246884090650017800643523 1870326135975026700965285)
    ·
      refine ⟨350686150495317506430991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1870326135975026700965285 350686150495317506430991)
      ·
        refine ⟨526029225742976259646487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350686150495317506430991 526029225742976259646487)
        ·
          refine ⟨789043838614464389469731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526029225742976259646487 789043838614464389469731)
          ·
            refine ⟨1183565757921696584204597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789043838614464389469731 1183565757921696584204597)
            ·
              refine ⟨110959289805159054769181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1183565757921696584204597 110959289805159054769181)
              ·
                refine ⟨41609733676934645538443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110959289805159054769181 41609733676934645538443)
                ·
                  rfl

theorem cell19_136746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_136746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136746 prefixEnd_136746 := by exact prefixLift 136746
  have htrace : WordTrace (prefixWord ++ tailWord_136746) baseStart_136746 baseEnd_136746 := by
    simpa [prefixWord, tailWord_136746, baseEnd_136746] using wordTrace_append hprefix tailTrace_136746
  have hstable : (prefixWord ++ tailWord_136746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136746).length < 2 ^ (prefixWord ++ tailWord_136746).sum := by decide
  have hdescent : baseEnd_136746 < baseStart_136746 := by decide
  rcases family_descends (prefixWord ++ tailWord_136746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136797 : List Nat := [1, 4, 4, 2, 2, 1, 2, 3]
def baseStart_136797 : Nat := 118140960795 + 136797 * 2 ^ 59
def prefixEnd_136797 : Nat := 4983230072969 + 3 ^ 40 * 136797 * 2
def baseEnd_136797 : Nat := 41625252203381638404971

theorem tailTrace_136797 : CollatzResearch.WordTrace tailWord_136797 prefixEnd_136797 41625252203381638404971 := by
  unfold tailWord_136797
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989396485415306912680645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3326264323610204608453763 4989396485415306912680645)
  ·
    refine ⟨935511841015370046127621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4989396485415306912680645 935511841015370046127621)
    ·
      refine ⟨175408470190381883648929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 935511841015370046127621 175408470190381883648929)
      ·
        refine ⟨131556352642786412736697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175408470190381883648929 131556352642786412736697)
        ·
          refine ⟨98667264482089809552523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131556352642786412736697 98667264482089809552523)
          ·
            refine ⟨148000896723134714328785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98667264482089809552523 148000896723134714328785)
            ·
              refine ⟨111000672542351035746589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148000896723134714328785 111000672542351035746589)
              ·
                refine ⟨41625252203381638404971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111000672542351035746589 41625252203381638404971)
                ·
                  rfl

theorem cell19_136797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_136797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136797 prefixEnd_136797 := by exact prefixLift 136797
  have htrace : WordTrace (prefixWord ++ tailWord_136797) baseStart_136797 baseEnd_136797 := by
    simpa [prefixWord, tailWord_136797, baseEnd_136797] using wordTrace_append hprefix tailTrace_136797
  have hstable : (prefixWord ++ tailWord_136797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136797).length < 2 ^ (prefixWord ++ tailWord_136797).sum := by decide
  have hdescent : baseEnd_136797 < baseStart_136797 := by decide
  rcases family_descends (prefixWord ++ tailWord_136797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136803 : List Nat := [1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_136803 : Nat := 118140960795 + 136803 * 2 ^ 59
def prefixEnd_136803 : Nat := 4983230072969 + 3 ^ 40 * 136803 * 2
def baseEnd_136803 : Nat := 41627077912375402271621

theorem tailTrace_136803 : CollatzResearch.WordTrace tailWord_136803 prefixEnd_136803 41627077912375402271621 := by
  unfold tailWord_136803
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989615323393569937399063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3326410215595713291599375 4989615323393569937399063)
  ·
    refine ⟨7484422985090354906098595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4989615323393569937399063 7484422985090354906098595)
    ·
      refine ⟨11226634477635532359147893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7484422985090354906098595 11226634477635532359147893)
      ·
        refine ⟨1052496982278331158670115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11226634477635532359147893 1052496982278331158670115)
        ·
          refine ⟨1578745473417496738005173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052496982278331158670115 1578745473417496738005173)
          ·
            refine ⟨148007388132890319187985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1578745473417496738005173 148007388132890319187985)
            ·
              refine ⟨111005541099667739390989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148007388132890319187985 111005541099667739390989)
              ·
                refine ⟨41627077912375402271621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111005541099667739390989 41627077912375402271621)
                ·
                  rfl

theorem cell19_136803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_136803 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136803 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136803 prefixEnd_136803 := by exact prefixLift 136803
  have htrace : WordTrace (prefixWord ++ tailWord_136803) baseStart_136803 baseEnd_136803 := by
    simpa [prefixWord, tailWord_136803, baseEnd_136803] using wordTrace_append hprefix tailTrace_136803
  have hstable : (prefixWord ++ tailWord_136803).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136803).length < 2 ^ (prefixWord ++ tailWord_136803).sum := by decide
  have hdescent : baseEnd_136803 < baseStart_136803 := by decide
  rcases family_descends (prefixWord ++ tailWord_136803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136805 : List Nat := [1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_136805 : Nat := 118140960795 + 136805 * 2 ^ 59
def prefixEnd_136805 : Nat := 4983230072969 + 3 ^ 40 * 136805 * 2
def baseEnd_136805 : Nat := 41627686482039990227171

theorem tailTrace_136805 : CollatzResearch.WordTrace tailWord_136805 prefixEnd_136805 41627686482039990227171 := by
  unfold tailWord_136805
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989688269386324278971869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3326458846257549519314579 4989688269386324278971869)
  ·
    refine ⟨1871133101019871604614451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4989688269386324278971869 1871133101019871604614451)
    ·
      refine ⟨2806699651529807406921677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871133101019871604614451 2806699651529807406921677)
      ·
        refine ⟨1052512369323677777595629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2806699651529807406921677 1052512369323677777595629)
        ·
          refine ⟨394692138496379166598361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1052512369323677777595629 394692138496379166598361)
          ·
            refine ⟨296019103872284374948771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394692138496379166598361 296019103872284374948771)
            ·
              refine ⟨444028655808426562423157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296019103872284374948771 444028655808426562423157)
              ·
                refine ⟨41627686482039990227171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 444028655808426562423157 41627686482039990227171)
                ·
                  rfl

theorem cell19_136805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_136805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136805 prefixEnd_136805 := by exact prefixLift 136805
  have htrace : WordTrace (prefixWord ++ tailWord_136805) baseStart_136805 baseEnd_136805 := by
    simpa [prefixWord, tailWord_136805, baseEnd_136805] using wordTrace_append hprefix tailTrace_136805
  have hstable : (prefixWord ++ tailWord_136805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136805).length < 2 ^ (prefixWord ++ tailWord_136805).sum := by decide
  have hdescent : baseEnd_136805 < baseStart_136805 := by decide
  rcases family_descends (prefixWord ++ tailWord_136805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136822 : List Nat := [5, 1, 1, 2, 2, 3, 5]
def baseStart_136822 : Nat := 118140960795 + 136822 * 2 ^ 59
def prefixEnd_136822 : Nat := 4983230072969 + 3 ^ 40 * 136822 * 2
def baseEnd_136822 : Nat := 13877619774729662616449

theorem tailTrace_136822 : CollatzResearch.WordTrace tailWord_136822 prefixEnd_136822 13877619774729662616449 := by
  unfold tailWord_136822
  simp only [CollatzResearch.WordTrace]
  refine ⟨311894269395296011396295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3326872206883157454893813 311894269395296011396295)
  ·
    refine ⟨467841404092944017094443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 311894269395296011396295 467841404092944017094443)
    ·
      refine ⟨701762106139416025641665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467841404092944017094443 701762106139416025641665)
      ·
        refine ⟨526321579604562019231249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701762106139416025641665 526321579604562019231249)
        ·
          refine ⟨394741184703421514423437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526321579604562019231249 394741184703421514423437)
          ·
            refine ⟨148027944263783067908789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394741184703421514423437 148027944263783067908789)
            ·
              refine ⟨13877619774729662616449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148027944263783067908789 13877619774729662616449)
              ·
                rfl

theorem cell19_136822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_136822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136822 prefixEnd_136822 := by exact prefixLift 136822
  have htrace : WordTrace (prefixWord ++ tailWord_136822) baseStart_136822 baseEnd_136822 := by
    simpa [prefixWord, tailWord_136822, baseEnd_136822] using wordTrace_append hprefix tailTrace_136822
  have hstable : (prefixWord ++ tailWord_136822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136822).length < 2 ^ (prefixWord ++ tailWord_136822).sum := by decide
  have hdescent : baseEnd_136822 < baseStart_136822 := by decide
  rcases family_descends (prefixWord ++ tailWord_136822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136919 : List Nat := [1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_136919 : Nat := 118140960795 + 136919 * 2 ^ 59
def prefixEnd_136919 : Nat := 4983230072969 + 3 ^ 40 * 136919 * 2
def baseEnd_136919 : Nat := 41662374952921503693527

theorem tailTrace_136919 : CollatzResearch.WordTrace tailWord_136919 prefixEnd_136919 41662374952921503693527 := by
  unfold tailWord_136919
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993846190973321748621811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3329230793982214499081207 4993846190973321748621811)
  ·
    refine ⟨7490769286459982622932717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4993846190973321748621811 7490769286459982622932717)
    ·
      refine ⟨2809038482422493483599769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7490769286459982622932717 2809038482422493483599769)
      ·
        refine ⟨2106778861816870112699827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2809038482422493483599769 2106778861816870112699827)
        ·
          refine ⟨3160168292725305169049741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106778861816870112699827 3160168292725305169049741)
          ·
            refine ⟨1185063109771989438393653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3160168292725305169049741 1185063109771989438393653)
            ·
              refine ⟨111099666541124009849405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1185063109771989438393653 111099666541124009849405)
              ·
                refine ⟨41662374952921503693527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111099666541124009849405 41662374952921503693527)
                ·
                  rfl

theorem cell19_136919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_136919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136919 prefixEnd_136919 := by exact prefixLift 136919
  have htrace : WordTrace (prefixWord ++ tailWord_136919) baseStart_136919 baseEnd_136919 := by
    simpa [prefixWord, tailWord_136919, baseEnd_136919] using wordTrace_append hprefix tailTrace_136919
  have hstable : (prefixWord ++ tailWord_136919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136919).length < 2 ^ (prefixWord ++ tailWord_136919).sum := by decide
  have hdescent : baseEnd_136919 < baseStart_136919 := by decide
  rcases family_descends (prefixWord ++ tailWord_136919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136997 : List Nat := [1, 3, 1, 2, 3, 2, 7]
def baseStart_136997 : Nat := 118140960795 + 136997 * 2 ^ 59
def prefixEnd_136997 : Nat := 4983230072969 + 3 ^ 40 * 136997 * 2
def baseEnd_136997 : Nat := 13895369723280144653327

theorem tailTrace_136997 : CollatzResearch.WordTrace tailWord_136997 prefixEnd_136997 13895369723280144653327 := by
  unfold tailWord_136997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4996691084690741069961245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3331127389793827379974163 4996691084690741069961245)
  ·
    refine ⟨1873759156759027901235467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4996691084690741069961245 1873759156759027901235467)
    ·
      refine ⟨2810638735138541851853201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873759156759027901235467 2810638735138541851853201)
      ·
        refine ⟨2107979051353906388889901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2810638735138541851853201 2107979051353906388889901)
        ·
          refine ⟨790492144257714895833713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2107979051353906388889901 790492144257714895833713)
          ·
            refine ⟨592869108193286171875285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790492144257714895833713 592869108193286171875285)
            ·
              refine ⟨13895369723280144653327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 592869108193286171875285 13895369723280144653327)
              ·
                rfl

theorem cell19_136997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_136997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_136997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_136997 prefixEnd_136997 := by exact prefixLift 136997
  have htrace : WordTrace (prefixWord ++ tailWord_136997) baseStart_136997 baseEnd_136997 := by
    simpa [prefixWord, tailWord_136997, baseEnd_136997] using wordTrace_append hprefix tailTrace_136997
  have hstable : (prefixWord ++ tailWord_136997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136997).length < 2 ^ (prefixWord ++ tailWord_136997).sum := by decide
  have hdescent : baseEnd_136997 < baseStart_136997 := by decide
  rcases family_descends (prefixWord ++ tailWord_136997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137012 : List Nat := [2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_137012 : Nat := 118140960795 + 137012 * 2 ^ 59
def prefixEnd_137012 : Nat := 4983230072969 + 3 ^ 40 * 137012 * 2
def baseEnd_137012 : Nat := 41690673442324843626607

theorem tailTrace_137012 : CollatzResearch.WordTrace tailWord_137012 prefixEnd_137012 41690673442324843626607 := by
  unfold tailWord_137012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498619089818199315878645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3331492119757599087838193 2498619089818199315878645)
  ·
    refine ⟨234245539670456185863623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2498619089818199315878645 234245539670456185863623)
    ·
      refine ⟨351368309505684278795435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234245539670456185863623 351368309505684278795435)
      ·
        refine ⟨527052464258526418193153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351368309505684278795435 527052464258526418193153)
        ·
          refine ⟨395289348193894813644865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527052464258526418193153 395289348193894813644865)
          ·
            refine ⟨296467011145421110233649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395289348193894813644865 296467011145421110233649)
            ·
              refine ⟨222350258359065832675237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296467011145421110233649 222350258359065832675237)
              ·
                refine ⟨41690673442324843626607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222350258359065832675237 41690673442324843626607)
                ·
                  rfl

theorem cell19_137012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_137012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137012 prefixEnd_137012 := by exact prefixLift 137012
  have htrace : WordTrace (prefixWord ++ tailWord_137012) baseStart_137012 baseEnd_137012 := by
    simpa [prefixWord, tailWord_137012, baseEnd_137012] using wordTrace_append hprefix tailTrace_137012
  have hstable : (prefixWord ++ tailWord_137012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137012).length < 2 ^ (prefixWord ++ tailWord_137012).sum := by decide
  have hdescent : baseEnd_137012 < baseStart_137012 := by decide
  rcases family_descends (prefixWord ++ tailWord_137012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137016 : List Nat := [2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_137016 : Nat := 118140960795 + 137016 * 2 ^ 59
def prefixEnd_137016 : Nat := 4983230072969 + 3 ^ 40 * 137016 * 2
def baseEnd_137016 : Nat := 41691890581654019537707

theorem tailTrace_137016 : CollatzResearch.WordTrace tailWord_137016 prefixEnd_137016 41691890581654019537707 := by
  unfold tailWord_137016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498692035810953657451451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3331589381081271543268601 2498692035810953657451451)
  ·
    refine ⟨3748038053716430486177177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2498692035810953657451451 3748038053716430486177177)
    ·
      refine ⟨2811028540287322864632883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3748038053716430486177177 2811028540287322864632883)
      ·
        refine ⟨4216542810430984296949325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811028540287322864632883 4216542810430984296949325)
        ·
          refine ⟨1581203553911619111355997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4216542810430984296949325 1581203553911619111355997)
          ·
            refine ⟨592951332716857166758499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1581203553911619111355997 592951332716857166758499)
            ·
              refine ⟨889426999075285750137749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592951332716857166758499 889426999075285750137749)
              ·
                refine ⟨41691890581654019537707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 889426999075285750137749 41691890581654019537707)
                ·
                  rfl

theorem cell19_137016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_137016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137016 prefixEnd_137016 := by exact prefixLift 137016
  have htrace : WordTrace (prefixWord ++ tailWord_137016) baseStart_137016 baseEnd_137016 := by
    simpa [prefixWord, tailWord_137016, baseEnd_137016] using wordTrace_append hprefix tailTrace_137016
  have hstable : (prefixWord ++ tailWord_137016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137016).length < 2 ^ (prefixWord ++ tailWord_137016).sum := by decide
  have hdescent : baseEnd_137016 < baseStart_137016 := by decide
  rcases family_descends (prefixWord ++ tailWord_137016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137052 : List Nat := [2, 2, 4, 2, 2, 7]
def baseStart_137052 : Nat := 118140960795 + 137052 * 2 ^ 59
def prefixEnd_137052 : Nat := 4983230072969 + 3 ^ 40 * 137052 * 2
def baseEnd_137052 : Nat := 4633649426179622526401

theorem tailTrace_137052 : CollatzResearch.WordTrace tailWord_137052 prefixEnd_137052 4633649426179622526401 := by
  unfold tailWord_137052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499348549745742731606705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3332464732994323642142273 2499348549745742731606705)
  ·
    refine ⟨1874511412309307048705029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2499348549745742731606705 1874511412309307048705029)
    ·
      refine ⟨351470889807995071632193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1874511412309307048705029 351470889807995071632193)
      ·
        refine ⟨263603167355996303724145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351470889807995071632193 263603167355996303724145)
        ·
          refine ⟨197702375516997227793109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263603167355996303724145 197702375516997227793109)
          ·
            refine ⟨4633649426179622526401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 197702375516997227793109 4633649426179622526401)
            ·
              rfl

theorem cell19_137052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_137052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137052 prefixEnd_137052 := by exact prefixLift 137052
  have htrace : WordTrace (prefixWord ++ tailWord_137052) baseStart_137052 baseEnd_137052 := by
    simpa [prefixWord, tailWord_137052, baseEnd_137052] using wordTrace_append hprefix tailTrace_137052
  have hstable : (prefixWord ++ tailWord_137052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137052).length < 2 ^ (prefixWord ++ tailWord_137052).sum := by decide
  have hdescent : baseEnd_137052 < baseStart_137052 := by decide
  rcases family_descends (prefixWord ++ tailWord_137052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137086 : List Nat := [4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_137086 : Nat := 118140960795 + 137086 * 2 ^ 59
def prefixEnd_137086 : Nat := 4983230072969 + 3 ^ 40 * 137086 * 2
def baseEnd_137086 : Nat := 41713190519914597981961

theorem tailTrace_137086 : CollatzResearch.WordTrace tailWord_137086 prefixEnd_137086 41713190519914597981961 := by
  unfold tailWord_137086
  simp only [CollatzResearch.WordTrace]
  refine ⟨624992147671038658743889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3333291454245539513300741 624992147671038658743889)
  ·
    refine ⟨468744110753278994057917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 624992147671038658743889 468744110753278994057917)
    ·
      refine ⟨175779041532479622771719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 468744110753278994057917 175779041532479622771719)
      ·
        refine ⟨263668562298719434157579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175779041532479622771719 263668562298719434157579)
        ·
          refine ⟨395502843448079151236369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263668562298719434157579 395502843448079151236369)
          ·
            refine ⟨296627132586059363427277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395502843448079151236369 296627132586059363427277)
            ·
              refine ⟨111235174719772261285229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296627132586059363427277 111235174719772261285229)
              ·
                refine ⟨41713190519914597981961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111235174719772261285229 41713190519914597981961)
                ·
                  rfl

theorem cell19_137086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_137086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137086 prefixEnd_137086 := by exact prefixLift 137086
  have htrace : WordTrace (prefixWord ++ tailWord_137086) baseStart_137086 baseEnd_137086 := by
    simpa [prefixWord, tailWord_137086, baseEnd_137086] using wordTrace_append hprefix tailTrace_137086
  have hstable : (prefixWord ++ tailWord_137086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137086).length < 2 ^ (prefixWord ++ tailWord_137086).sum := by decide
  have hdescent : baseEnd_137086 < baseStart_137086 := by decide
  rcases family_descends (prefixWord ++ tailWord_137086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137092 : List Nat := [2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_137092 : Nat := 118140960795 + 137092 * 2 ^ 59
def prefixEnd_137092 : Nat := 4983230072969 + 3 ^ 40 * 137092 * 2
def baseEnd_137092 : Nat := 41715016228908361848611

theorem tailTrace_137092 : CollatzResearch.WordTrace tailWord_137092 prefixEnd_137092 41715016228908361848611 := by
  unfold tailWord_137092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500078009673286147334765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3333437346231048196446353 2500078009673286147334765)
  ·
    refine ⟨937529253627482305250537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2500078009673286147334765 937529253627482305250537)
    ·
      refine ⟨703146940220611728937903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937529253627482305250537 703146940220611728937903)
      ·
        refine ⟨1054720410330917593406855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703146940220611728937903 1054720410330917593406855)
        ·
          refine ⟨1582080615496376390110283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054720410330917593406855 1582080615496376390110283)
          ·
            refine ⟨2373120923244564585165425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582080615496376390110283 2373120923244564585165425)
            ·
              refine ⟨1779840692433423438874069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373120923244564585165425 1779840692433423438874069)
              ·
                refine ⟨41715016228908361848611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1779840692433423438874069 41715016228908361848611)
                ·
                  rfl

theorem cell19_137092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_137092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137092 prefixEnd_137092 := by exact prefixLift 137092
  have htrace : WordTrace (prefixWord ++ tailWord_137092) baseStart_137092 baseEnd_137092 := by
    simpa [prefixWord, tailWord_137092, baseEnd_137092] using wordTrace_append hprefix tailTrace_137092
  have hstable : (prefixWord ++ tailWord_137092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137092).length < 2 ^ (prefixWord ++ tailWord_137092).sum := by decide
  have hdescent : baseEnd_137092 < baseStart_137092 := by decide
  rcases family_descends (prefixWord ++ tailWord_137092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137111 : List Nat := [1, 1, 3, 3, 1, 4, 6]
def baseStart_137111 : Nat := 118140960795 + 137111 * 2 ^ 59
def prefixEnd_137111 : Nat := 4983230072969 + 3 ^ 40 * 137111 * 2
def baseEnd_137111 : Nat := 13906932546907315808779

theorem tailTrace_137111 : CollatzResearch.WordTrace tailWord_137111 prefixEnd_137111 13906932546907315808779 := by
  unfold tailWord_137111
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000849006277738539611187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3333899337518492359740791 5000849006277738539611187)
  ·
    refine ⟨7501273509416607809416781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000849006277738539611187 7501273509416607809416781)
    ·
      refine ⟨2812977566031227928531293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7501273509416607809416781 2812977566031227928531293)
      ·
        refine ⟨1054866587261710473199235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2812977566031227928531293 1054866587261710473199235)
        ·
          refine ⟨1582299880892565709798853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054866587261710473199235 1582299880892565709798853)
          ·
            refine ⟨296681227667356070587285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1582299880892565709798853 296681227667356070587285)
            ·
              refine ⟨13906932546907315808779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 296681227667356070587285 13906932546907315808779)
              ·
                rfl

theorem cell19_137111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_137111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137111 prefixEnd_137111 := by exact prefixLift 137111
  have htrace : WordTrace (prefixWord ++ tailWord_137111) baseStart_137111 baseEnd_137111 := by
    simpa [prefixWord, tailWord_137111, baseEnd_137111] using wordTrace_append hprefix tailTrace_137111
  have hstable : (prefixWord ++ tailWord_137111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137111).length < 2 ^ (prefixWord ++ tailWord_137111).sum := by decide
  have hdescent : baseEnd_137111 < baseStart_137111 := by decide
  rcases family_descends (prefixWord ++ tailWord_137111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137187 : List Nat := [1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_137187 : Nat := 118140960795 + 137187 * 2 ^ 59
def prefixEnd_137187 : Nat := 4983230072969 + 3 ^ 40 * 137187 * 2
def baseEnd_137187 : Nat := 41743923287976289737241

theorem tailTrace_137187 : CollatzResearch.WordTrace tailWord_137187 prefixEnd_137187 41743923287976289737241 := by
  unfold tailWord_137187
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003620954002403519377815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3335747302668269012918543 5003620954002403519377815)
  ·
    refine ⟨7505431431003605279066723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5003620954002403519377815 7505431431003605279066723)
    ·
      refine ⟨11258147146505407918600085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7505431431003605279066723 11258147146505407918600085)
      ·
        refine ⟨527725647492440996184379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11258147146505407918600085 527725647492440996184379)
        ·
          refine ⟨791588471238661494276569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527725647492440996184379 791588471238661494276569)
          ·
            refine ⟨593691353428996120707427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791588471238661494276569 593691353428996120707427)
            ·
              refine ⟨890537030143494181061141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593691353428996120707427 890537030143494181061141)
              ·
                refine ⟨41743923287976289737241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 890537030143494181061141 41743923287976289737241)
                ·
                  rfl

theorem cell19_137187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_137187 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137187 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137187 prefixEnd_137187 := by exact prefixLift 137187
  have htrace : WordTrace (prefixWord ++ tailWord_137187) baseStart_137187 baseEnd_137187 := by
    simpa [prefixWord, tailWord_137187, baseEnd_137187] using wordTrace_append hprefix tailTrace_137187
  have hstable : (prefixWord ++ tailWord_137187).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137187).length < 2 ^ (prefixWord ++ tailWord_137187).sum := by decide
  have hdescent : baseEnd_137187 < baseStart_137187 := by decide
  rcases family_descends (prefixWord ++ tailWord_137187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137236 : List Nat := [2, 4, 3, 2, 2, 1, 1, 4]
def baseStart_137236 : Nat := 118140960795 + 137236 * 2 ^ 59
def prefixEnd_137236 : Nat := 4983230072969 + 3 ^ 40 * 137236 * 2
def baseEnd_137236 : Nat := 41758833244758694648219

theorem tailTrace_137236 : CollatzResearch.WordTrace tailWord_137236 prefixEnd_137236 41758833244758694648219 := by
  unfold tailWord_137236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502704065412442443955781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3336938753883256591941041 2502704065412442443955781)
  ·
    refine ⟨469257012264832958241709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2502704065412442443955781 469257012264832958241709)
    ·
      refine ⟨175971379599312359340641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 469257012264832958241709 175971379599312359340641)
      ·
        refine ⟨131978534699484269505481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175971379599312359340641 131978534699484269505481)
        ·
          refine ⟨98983901024613202129111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131978534699484269505481 98983901024613202129111)
          ·
            refine ⟨148475851536919803193667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98983901024613202129111 148475851536919803193667)
            ·
              refine ⟨222713777305379704790501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148475851536919803193667 222713777305379704790501)
              ·
                refine ⟨41758833244758694648219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222713777305379704790501 41758833244758694648219)
                ·
                  rfl

theorem cell19_137236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_137236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137236 prefixEnd_137236 := by exact prefixLift 137236
  have htrace : WordTrace (prefixWord ++ tailWord_137236) baseStart_137236 baseEnd_137236 := by
    simpa [prefixWord, tailWord_137236, baseEnd_137236] using wordTrace_append hprefix tailTrace_137236
  have hstable : (prefixWord ++ tailWord_137236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137236).length < 2 ^ (prefixWord ++ tailWord_137236).sum := by decide
  have hdescent : baseEnd_137236 < baseStart_137236 := by decide
  rcases family_descends (prefixWord ++ tailWord_137236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137242 : List Nat := [3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_137242 : Nat := 118140960795 + 137242 * 2 ^ 59
def prefixEnd_137242 : Nat := 4983230072969 + 3 ^ 40 * 137242 * 2
def baseEnd_137242 : Nat := 41760658953752458514869

theorem tailTrace_137242 : CollatzResearch.WordTrace tailWord_137242 prefixEnd_137242 41760658953752458514869 := by
  unfold tailWord_137242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251406742200786978157495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3337084645868765275086653 1251406742200786978157495)
  ·
    refine ⟨1877110113301180467236243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251406742200786978157495 1877110113301180467236243)
    ·
      refine ⟨2815665169951770700854365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877110113301180467236243 2815665169951770700854365)
      ·
        refine ⟨1055874438731914012820387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2815665169951770700854365 1055874438731914012820387)
        ·
          refine ⟨1583811658097871019230581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055874438731914012820387 1583811658097871019230581)
          ·
            refine ⟨148482342946675408052867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1583811658097871019230581 148482342946675408052867)
            ·
              refine ⟨222723514420013112079301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148482342946675408052867 222723514420013112079301)
              ·
                refine ⟨41760658953752458514869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222723514420013112079301 41760658953752458514869)
                ·
                  rfl

theorem cell19_137242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_137242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137242 prefixEnd_137242 := by exact prefixLift 137242
  have htrace : WordTrace (prefixWord ++ tailWord_137242) baseStart_137242 baseEnd_137242 := by
    simpa [prefixWord, tailWord_137242, baseEnd_137242] using wordTrace_append hprefix tailTrace_137242
  have hstable : (prefixWord ++ tailWord_137242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137242).length < 2 ^ (prefixWord ++ tailWord_137242).sum := by decide
  have hdescent : baseEnd_137242 < baseStart_137242 := by decide
  rcases family_descends (prefixWord ++ tailWord_137242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137310 : List Nat := [4, 4, 1, 1, 3, 1, 2, 3]
def baseStart_137310 : Nat := 118140960795 + 137310 * 2 ^ 59
def prefixEnd_137310 : Nat := 4983230072969 + 3 ^ 40 * 137310 * 2
def baseEnd_137310 : Nat := 41781350322348449003573

theorem tailTrace_137310 : CollatzResearch.WordTrace tailWord_137310 prefixEnd_137310 41781350322348449003573 := by
  unfold tailWord_137310
  simp only [CollatzResearch.WordTrace]
  refine ⟨626013391569599440763173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3338738088371197017403589 626013391569599440763173)
  ·
    refine ⟨117377510919299895143095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 626013391569599440763173 117377510919299895143095)
    ·
      refine ⟨176066266378949842714643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117377510919299895143095 176066266378949842714643)
      ·
        refine ⟨264099399568424764071965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176066266378949842714643 264099399568424764071965)
        ·
          refine ⟨99037274838159286526987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264099399568424764071965 99037274838159286526987)
          ·
            refine ⟨148555912257238929790481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99037274838159286526987 148555912257238929790481)
            ·
              refine ⟨111416934192929197342861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148555912257238929790481 111416934192929197342861)
              ·
                refine ⟨41781350322348449003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111416934192929197342861 41781350322348449003573)
                ·
                  rfl

theorem cell19_137310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_137310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137310 prefixEnd_137310 := by exact prefixLift 137310
  have htrace : WordTrace (prefixWord ++ tailWord_137310) baseStart_137310 baseEnd_137310 := by
    simpa [prefixWord, tailWord_137310, baseEnd_137310] using wordTrace_append hprefix tailTrace_137310
  have hstable : (prefixWord ++ tailWord_137310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137310).length < 2 ^ (prefixWord ++ tailWord_137310).sum := by decide
  have hdescent : baseEnd_137310 < baseStart_137310 := by decide
  rcases family_descends (prefixWord ++ tailWord_137310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137314 : List Nat := [3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_137314 : Nat := 118140960795 + 137314 * 2 ^ 59
def prefixEnd_137314 : Nat := 4983230072969 + 3 ^ 40 * 137314 * 2
def baseEnd_137314 : Nat := 41782567461677624914673

theorem tailTrace_137314 : CollatzResearch.WordTrace tailWord_137314 prefixEnd_137314 41782567461677624914673 := by
  unfold tailWord_137314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252063256135576052312749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3338835349694869472833997 1252063256135576052312749)
  ·
    refine ⟨469523721050841019617281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1252063256135576052312749 469523721050841019617281)
    ·
      refine ⟨352142790788130764712961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 469523721050841019617281 352142790788130764712961)
      ·
        refine ⟨264107093091098073534721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352142790788130764712961 264107093091098073534721)
        ·
          refine ⟨198080319818323555151041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264107093091098073534721 198080319818323555151041)
          ·
            refine ⟨148560239863742666363281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198080319818323555151041 148560239863742666363281)
            ·
              refine ⟨111420179897806999772461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148560239863742666363281 111420179897806999772461)
              ·
                refine ⟨41782567461677624914673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111420179897806999772461 41782567461677624914673)
                ·
                  rfl

theorem cell19_137314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_137314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137314 prefixEnd_137314 := by exact prefixLift 137314
  have htrace : WordTrace (prefixWord ++ tailWord_137314) baseStart_137314 baseEnd_137314 := by
    simpa [prefixWord, tailWord_137314, baseEnd_137314] using wordTrace_append hprefix tailTrace_137314
  have hstable : (prefixWord ++ tailWord_137314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137314).length < 2 ^ (prefixWord ++ tailWord_137314).sum := by decide
  have hdescent : baseEnd_137314 < baseStart_137314 := by decide
  rcases family_descends (prefixWord ++ tailWord_137314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137377 : List Nat := [1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_137377 : Nat := 118140960795 + 137377 * 2 ^ 59
def prefixEnd_137377 : Nat := 4983230072969 + 3 ^ 40 * 137377 * 2
def baseEnd_137377 : Nat := 41801737406112145514501

theorem tailTrace_137377 : CollatzResearch.WordTrace tailWord_137377 prefixEnd_137377 41801737406112145514501 := by
  unfold tailWord_137377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010550823314065968794385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3340367215542710645862923 5010550823314065968794385)
  ·
    refine ⟨3757913117485549476595789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5010550823314065968794385 3757913117485549476595789)
    ·
      refine ⟨1409217419057081053723421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3757913117485549476595789 1409217419057081053723421)
      ·
        refine ⟨528456532146405395146283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1409217419057081053723421 528456532146405395146283)
        ·
          refine ⟨792684798219608092719425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528456532146405395146283 792684798219608092719425)
          ·
            refine ⟨594513598664706069539569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792684798219608092719425 594513598664706069539569)
            ·
              refine ⟨445885198998529552154677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594513598664706069539569 445885198998529552154677)
              ·
                refine ⟨41801737406112145514501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 445885198998529552154677 41801737406112145514501)
                ·
                  rfl

theorem cell19_137377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_137377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137377 prefixEnd_137377 := by exact prefixLift 137377
  have htrace : WordTrace (prefixWord ++ tailWord_137377) baseStart_137377 baseEnd_137377 := by
    simpa [prefixWord, tailWord_137377, baseEnd_137377] using wordTrace_append hprefix tailTrace_137377
  have hstable : (prefixWord ++ tailWord_137377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137377).length < 2 ^ (prefixWord ++ tailWord_137377).sum := by decide
  have hdescent : baseEnd_137377 < baseStart_137377 := by decide
  rcases family_descends (prefixWord ++ tailWord_137377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137409 : List Nat := [1, 2, 6, 1, 3, 1, 1, 4]
def baseStart_137409 : Nat := 118140960795 + 137409 * 2 ^ 59
def prefixEnd_137409 : Nat := 4983230072969 + 3 ^ 40 * 137409 * 2
def baseEnd_137409 : Nat := 41811474520745552803303

theorem tailTrace_137409 : CollatzResearch.WordTrace tailWord_137409 prefixEnd_137409 41811474520745552803303 := by
  unfold tailWord_137409
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011717959198135433959281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3341145306132090289306187 5011717959198135433959281)
  ·
    refine ⟨3758788469398601575469461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5011717959198135433959281 3758788469398601575469461)
    ·
      refine ⟨176193209503059448850131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3758788469398601575469461 176193209503059448850131)
      ·
        refine ⟨264289814254589173275197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176193209503059448850131 264289814254589173275197)
        ·
          refine ⟨99108680345470939978199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264289814254589173275197 99108680345470939978199)
          ·
            refine ⟨148663020518206409967299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99108680345470939978199 148663020518206409967299)
            ·
              refine ⟨222994530777309614950949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148663020518206409967299 222994530777309614950949)
              ·
                refine ⟨41811474520745552803303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222994530777309614950949 41811474520745552803303)
                ·
                  rfl

theorem cell19_137409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_137409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137409 prefixEnd_137409 := by exact prefixLift 137409
  have htrace : WordTrace (prefixWord ++ tailWord_137409) baseStart_137409 baseEnd_137409 := by
    simpa [prefixWord, tailWord_137409, baseEnd_137409] using wordTrace_append hprefix tailTrace_137409
  have hstable : (prefixWord ++ tailWord_137409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137409).length < 2 ^ (prefixWord ++ tailWord_137409).sum := by decide
  have hdescent : baseEnd_137409 < baseStart_137409 := by decide
  rcases family_descends (prefixWord ++ tailWord_137409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137417 : List Nat := [1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_137417 : Nat := 118140960795 + 137417 * 2 ^ 59
def prefixEnd_137417 : Nat := 4983230072969 + 3 ^ 40 * 137417 * 2
def baseEnd_137417 : Nat := 41813908799403904625503

theorem tailTrace_137417 : CollatzResearch.WordTrace tailWord_137417 prefixEnd_137417 41813908799403904625503 := by
  unfold tailWord_137417
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012009743169152800250505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3341339828779435200167003 5012009743169152800250505)
  ·
    refine ⟨3759007307376864600187879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5012009743169152800250505 3759007307376864600187879)
    ·
      refine ⟨5638510961065296900281819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3759007307376864600187879 5638510961065296900281819)
      ·
        refine ⟨8457766441597945350422729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5638510961065296900281819 8457766441597945350422729)
        ·
          refine ⟨6343324831198459012817047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8457766441597945350422729 6343324831198459012817047)
          ·
            refine ⟨9514987246797688519225571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343324831198459012817047 9514987246797688519225571)
            ·
              refine ⟨14272480870196532778838357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9514987246797688519225571 14272480870196532778838357)
              ·
                refine ⟨41813908799403904625503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14272480870196532778838357 41813908799403904625503)
                ·
                  rfl

theorem cell19_137417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_137417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137417 prefixEnd_137417 := by exact prefixLift 137417
  have htrace : WordTrace (prefixWord ++ tailWord_137417) baseStart_137417 baseEnd_137417 := by
    simpa [prefixWord, tailWord_137417, baseEnd_137417] using wordTrace_append hprefix tailTrace_137417
  have hstable : (prefixWord ++ tailWord_137417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137417).length < 2 ^ (prefixWord ++ tailWord_137417).sum := by decide
  have hdescent : baseEnd_137417 < baseStart_137417 := by decide
  rcases family_descends (prefixWord ++ tailWord_137417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137432 : List Nat := [2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_137432 : Nat := 118140960795 + 137432 * 2 ^ 59
def prefixEnd_137432 : Nat := 4983230072969 + 3 ^ 40 * 137432 * 2
def baseEnd_137432 : Nat := 41818473071888314292129

theorem tailTrace_137432 : CollatzResearch.WordTrace tailWord_137432 prefixEnd_137432 41818473071888314292129 := by
  unfold tailWord_137432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506278419057405181023275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3341704558743206908031033 2506278419057405181023275)
  ·
    refine ⟨3759417628586107771534913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2506278419057405181023275 3759417628586107771534913)
    ·
      refine ⟨2819563221439580828651185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3759417628586107771534913 2819563221439580828651185)
      ·
        refine ⟨2114672416079685621488389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2819563221439580828651185 2114672416079685621488389)
        ·
          refine ⟨396501078014941054029073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2114672416079685621488389 396501078014941054029073)
          ·
            refine ⟨297375808511205790521805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396501078014941054029073 297375808511205790521805)
            ·
              refine ⟨111515928191702171445677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297375808511205790521805 111515928191702171445677)
              ·
                refine ⟨41818473071888314292129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111515928191702171445677 41818473071888314292129)
                ·
                  rfl

theorem cell19_137432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_137432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137432 prefixEnd_137432 := by exact prefixLift 137432
  have htrace : WordTrace (prefixWord ++ tailWord_137432) baseStart_137432 baseEnd_137432 := by
    simpa [prefixWord, tailWord_137432, baseEnd_137432] using wordTrace_append hprefix tailTrace_137432
  have hstable : (prefixWord ++ tailWord_137432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137432).length < 2 ^ (prefixWord ++ tailWord_137432).sum := by decide
  have hdescent : baseEnd_137432 < baseStart_137432 := by decide
  rcases family_descends (prefixWord ++ tailWord_137432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137489 : List Nat := [1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_137489 : Nat := 118140960795 + 137489 * 2 ^ 59
def prefixEnd_137489 : Nat := 4983230072969 + 3 ^ 40 * 137489 * 2
def baseEnd_137489 : Nat := 41835817307329071025307

theorem tailTrace_137489 : CollatzResearch.WordTrace tailWord_137489 prefixEnd_137489 41835817307329071025307 := by
  unfold tailWord_137489
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014635798908309096871521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3343090532605539397914347 5014635798908309096871521)
  ·
    refine ⟨3760976849181231822653641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5014635798908309096871521 3760976849181231822653641)
    ·
      refine ⟨2820732636885923866990231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3760976849181231822653641 2820732636885923866990231)
      ·
        refine ⟨4231098955328885800485347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820732636885923866990231 4231098955328885800485347)
        ·
          refine ⟨6346648432993328700728021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231098955328885800485347 6346648432993328700728021)
          ·
            refine ⟨148749572648281141423313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6346648432993328700728021 148749572648281141423313)
            ·
              refine ⟨111562179486210856067485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148749572648281141423313 111562179486210856067485)
              ·
                refine ⟨41835817307329071025307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111562179486210856067485 41835817307329071025307)
                ·
                  rfl

theorem cell19_137489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_137489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137489 prefixEnd_137489 := by exact prefixLift 137489
  have htrace : WordTrace (prefixWord ++ tailWord_137489) baseStart_137489 baseEnd_137489 := by
    simpa [prefixWord, tailWord_137489, baseEnd_137489] using wordTrace_append hprefix tailTrace_137489
  have hstable : (prefixWord ++ tailWord_137489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137489).length < 2 ^ (prefixWord ++ tailWord_137489).sum := by decide
  have hdescent : baseEnd_137489 < baseStart_137489 := by decide
  rcases family_descends (prefixWord ++ tailWord_137489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137529 : List Nat := [1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_137529 : Nat := 118140960795 + 137529 * 2 ^ 59
def prefixEnd_137529 : Nat := 4983230072969 + 3 ^ 40 * 137529 * 2
def baseEnd_137529 : Nat := 41847988700620830136309

theorem tailTrace_137529 : CollatzResearch.WordTrace tailWord_137529 prefixEnd_137529 41847988700620830136309 := by
  unfold tailWord_137529
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016094718763395928327641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3344063145842263952218427 5016094718763395928327641)
  ·
    refine ⟨3762071039072546946245731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5016094718763395928327641 3762071039072546946245731)
    ·
      refine ⟨5643106558608820419368597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3762071039072546946245731 5643106558608820419368597)
      ·
        refine ⟨264520619934788457157903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5643106558608820419368597 264520619934788457157903)
        ·
          refine ⟨396780929902182685736855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264520619934788457157903 396780929902182685736855)
          ·
            refine ⟨595171394853274028605283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396780929902182685736855 595171394853274028605283)
            ·
              refine ⟨892757092279911042907925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595171394853274028605283 892757092279911042907925)
              ·
                refine ⟨41847988700620830136309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 892757092279911042907925 41847988700620830136309)
                ·
                  rfl

theorem cell19_137529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_137529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137529 prefixEnd_137529 := by exact prefixLift 137529
  have htrace : WordTrace (prefixWord ++ tailWord_137529) baseStart_137529 baseEnd_137529 := by
    simpa [prefixWord, tailWord_137529, baseEnd_137529] using wordTrace_append hprefix tailTrace_137529
  have hstable : (prefixWord ++ tailWord_137529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137529).length < 2 ^ (prefixWord ++ tailWord_137529).sum := by decide
  have hdescent : baseEnd_137529 < baseStart_137529 := by decide
  rcases family_descends (prefixWord ++ tailWord_137529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137586 : List Nat := [3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_137586 : Nat := 118140960795 + 137586 * 2 ^ 59
def prefixEnd_137586 : Nat := 4983230072969 + 3 ^ 40 * 137586 * 2
def baseEnd_137586 : Nat := 41865332936061586869487

theorem tailTrace_137586 : CollatzResearch.WordTrace tailWord_137586 prefixEnd_137586 41865332936061586869487 := by
  unfold tailWord_137586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254543419889223665788153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3345449119704596442101741 1254543419889223665788153)
  ·
    refine ⟨940907564916917749341115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1254543419889223665788153 940907564916917749341115)
    ·
      refine ⟨1411361347375376624011673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 940907564916917749341115 1411361347375376624011673)
      ·
        refine ⟨1058521010531532468008755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1411361347375376624011673 1058521010531532468008755)
        ·
          refine ⟨1587781515797298702013133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058521010531532468008755 1587781515797298702013133)
          ·
            refine ⟨595418068423987013254925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1587781515797298702013133 595418068423987013254925)
            ·
              refine ⟨223281775658995129970597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 595418068423987013254925 223281775658995129970597)
              ·
                refine ⟨41865332936061586869487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223281775658995129970597 41865332936061586869487)
                ·
                  rfl

theorem cell19_137586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_137586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137586 prefixEnd_137586 := by exact prefixLift 137586
  have htrace : WordTrace (prefixWord ++ tailWord_137586) baseStart_137586 baseEnd_137586 := by
    simpa [prefixWord, tailWord_137586, baseEnd_137586] using wordTrace_append hprefix tailTrace_137586
  have hstable : (prefixWord ++ tailWord_137586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137586).length < 2 ^ (prefixWord ++ tailWord_137586).sum := by decide
  have hdescent : baseEnd_137586 < baseStart_137586 := by decide
  rcases family_descends (prefixWord ++ tailWord_137586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137603 : List Nat := [1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_137603 : Nat := 118140960795 + 137603 * 2 ^ 59
def prefixEnd_137603 : Nat := 4983230072969 + 3 ^ 40 * 137603 * 2
def baseEnd_137603 : Nat := 41870505778210584491663

theorem tailTrace_137603 : CollatzResearch.WordTrace tailWord_137603 prefixEnd_137603 41870505778210584491663 := by
  unfold tailWord_137603
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018793720495306566521463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3345862480330204377680975 5018793720495306566521463)
  ·
    refine ⟨7528190580742959849782195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5018793720495306566521463 7528190580742959849782195)
    ·
      refine ⟨11292285871114439774673293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7528190580742959849782195 11292285871114439774673293)
      ·
        refine ⟨4234607201667914915502485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11292285871114439774673293 4234607201667914915502485)
        ·
          refine ⟨198497212578183511664179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4234607201667914915502485 198497212578183511664179)
          ·
            refine ⟨297745818867275267496269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198497212578183511664179 297745818867275267496269)
            ·
              refine ⟨111654682075228225311101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297745818867275267496269 111654682075228225311101)
              ·
                refine ⟨41870505778210584491663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111654682075228225311101 41870505778210584491663)
                ·
                  rfl

theorem cell19_137603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_137603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137603 prefixEnd_137603 := by exact prefixLift 137603
  have htrace : WordTrace (prefixWord ++ tailWord_137603) baseStart_137603 baseEnd_137603 := by
    simpa [prefixWord, tailWord_137603, baseEnd_137603] using wordTrace_append hprefix tailTrace_137603
  have hstable : (prefixWord ++ tailWord_137603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137603).length < 2 ^ (prefixWord ++ tailWord_137603).sum := by decide
  have hdescent : baseEnd_137603 < baseStart_137603 := by decide
  rcases family_descends (prefixWord ++ tailWord_137603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137624 : List Nat := [2, 1, 2, 5, 1, 2, 6]
def baseStart_137624 : Nat := 118140960795 + 137624 * 2 ^ 59
def prefixEnd_137624 : Nat := 4983230072969 + 3 ^ 40 * 137624 * 2
def baseEnd_137624 : Nat := 13958965253229586008313

theorem tailTrace_137624 : CollatzResearch.WordTrace tailWord_137624 prefixEnd_137624 13958965253229586008313 := by
  unfold tailWord_137624
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509779826709613576517963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3346373102279484768690617 2509779826709613576517963)
  ·
    refine ⟨3764669740064420364776945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2509779826709613576517963 3764669740064420364776945)
    ·
      refine ⟨2823502305048315273582709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3764669740064420364776945 2823502305048315273582709)
      ·
        refine ⟨264703341098279556898379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2823502305048315273582709 264703341098279556898379)
        ·
          refine ⟨397055011647419335347569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264703341098279556898379 397055011647419335347569)
          ·
            refine ⟨297791258735564501510677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397055011647419335347569 297791258735564501510677)
            ·
              refine ⟨13958965253229586008313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 297791258735564501510677 13958965253229586008313)
              ·
                rfl

theorem cell19_137624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_137624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137624 prefixEnd_137624 := by exact prefixLift 137624
  have htrace : WordTrace (prefixWord ++ tailWord_137624) baseStart_137624 baseEnd_137624 := by
    simpa [prefixWord, tailWord_137624, baseEnd_137624] using wordTrace_append hprefix tailTrace_137624
  have hstable : (prefixWord ++ tailWord_137624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137624).length < 2 ^ (prefixWord ++ tailWord_137624).sum := by decide
  have hdescent : baseEnd_137624 < baseStart_137624 := by decide
  rcases family_descends (prefixWord ++ tailWord_137624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137660 : List Nat := [2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_137660 : Nat := 118140960795 + 137660 * 2 ^ 59
def prefixEnd_137660 : Nat := 4983230072969 + 3 ^ 40 * 137660 * 2
def baseEnd_137660 : Nat := 41887850013651341224841

theorem tailTrace_137660 : CollatzResearch.WordTrace tailWord_137660 prefixEnd_137660 41887850013651341224841 := by
  unfold tailWord_137660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510436340644402650673217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3347248454192536867564289 2510436340644402650673217)
  ·
    refine ⟨1882827255483301988004913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2510436340644402650673217 1882827255483301988004913)
    ·
      refine ⟨1412120441612476491003685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1882827255483301988004913 1412120441612476491003685)
      ·
        refine ⟨264772582802339342063191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1412120441612476491003685 264772582802339342063191)
        ·
          refine ⟨397158874203509013094787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264772582802339342063191 397158874203509013094787)
          ·
            refine ⟨595738311305263519642181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397158874203509013094787 595738311305263519642181)
            ·
              refine ⟨111700933369736909932909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 595738311305263519642181 111700933369736909932909)
              ·
                refine ⟨41887850013651341224841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111700933369736909932909 41887850013651341224841)
                ·
                  rfl

theorem cell19_137660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_137660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137660 prefixEnd_137660 := by exact prefixLift 137660
  have htrace : WordTrace (prefixWord ++ tailWord_137660) baseStart_137660 baseEnd_137660 := by
    simpa [prefixWord, tailWord_137660, baseEnd_137660] using wordTrace_append hprefix tailTrace_137660
  have hstable : (prefixWord ++ tailWord_137660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137660).length < 2 ^ (prefixWord ++ tailWord_137660).sum := by decide
  have hdescent : baseEnd_137660 < baseStart_137660 := by decide
  rcases family_descends (prefixWord ++ tailWord_137660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137721 : List Nat := [1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_137721 : Nat := 118140960795 + 137721 * 2 ^ 59
def prefixEnd_137721 : Nat := 4983230072969 + 3 ^ 40 * 137721 * 2
def baseEnd_137721 : Nat := 41906411388421273869119

theorem tailTrace_137721 : CollatzResearch.WordTrace tailWord_137721 prefixEnd_137721 41906411388421273869119 := by
  unfold tailWord_137721
  simp only [CollatzResearch.WordTrace]
  refine ⟨5023097534067812719317017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3348731689378541812878011 5023097534067812719317017)
  ·
    refine ⟨3767323150550859539487763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5023097534067812719317017 3767323150550859539487763)
    ·
      refine ⟨5650984725826289309231645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767323150550859539487763 5650984725826289309231645)
      ·
        refine ⟨2119119272184858490961867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5650984725826289309231645 2119119272184858490961867)
        ·
          refine ⟨3178678908277287736442801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119119272184858490961867 3178678908277287736442801)
          ·
            refine ⟨2384009181207965802332101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178678908277287736442801 2384009181207965802332101)
            ·
              refine ⟨447001721476493587937269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2384009181207965802332101 447001721476493587937269)
              ·
                refine ⟨41906411388421273869119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 447001721476493587937269 41906411388421273869119)
                ·
                  rfl

theorem cell19_137721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_137721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137721 prefixEnd_137721 := by exact prefixLift 137721
  have htrace : WordTrace (prefixWord ++ tailWord_137721) baseStart_137721 baseEnd_137721 := by
    simpa [prefixWord, tailWord_137721, baseEnd_137721] using wordTrace_append hprefix tailTrace_137721
  have hstable : (prefixWord ++ tailWord_137721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137721).length < 2 ^ (prefixWord ++ tailWord_137721).sum := by decide
  have hdescent : baseEnd_137721 < baseStart_137721 := by decide
  rcases family_descends (prefixWord ++ tailWord_137721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137734 : List Nat := [6, 2, 1, 1, 1, 8]
def baseStart_137734 : Nat := 118140960795 + 137734 * 2 ^ 59
def prefixEnd_137734 : Nat := 4983230072969 + 3 ^ 40 * 137734 * 2
def baseEnd_137734 : Nat := 4656707454582343953355

theorem tailTrace_137734 : CollatzResearch.WordTrace tailWord_137734 prefixEnd_137734 4656707454582343953355 := by
  unfold tailWord_137734
  simp only [CollatzResearch.WordTrace]
  refine ⟨156986615094397373110633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3349047788680477293026837 156986615094397373110633)
  ·
    refine ⟨117739961320798029832975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156986615094397373110633 117739961320798029832975)
    ·
      refine ⟨176609941981197044749463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117739961320798029832975 176609941981197044749463)
      ·
        refine ⟨264914912971795567124195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176609941981197044749463 264914912971795567124195)
        ·
          refine ⟨397372369457693350686293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264914912971795567124195 397372369457693350686293)
          ·
            refine ⟨4656707454582343953355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 397372369457693350686293 4656707454582343953355)
            ·
              rfl

theorem cell19_137734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_137734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137734 prefixEnd_137734 := by exact prefixLift 137734
  have htrace : WordTrace (prefixWord ++ tailWord_137734) baseStart_137734 baseEnd_137734 := by
    simpa [prefixWord, tailWord_137734, baseEnd_137734] using wordTrace_append hprefix tailTrace_137734
  have hstable : (prefixWord ++ tailWord_137734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137734).length < 2 ^ (prefixWord ++ tailWord_137734).sum := by decide
  have hdescent : baseEnd_137734 < baseStart_137734 := by decide
  rcases family_descends (prefixWord ++ tailWord_137734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137740 : List Nat := [2, 2, 1, 2, 4, 8]
def baseStart_137740 : Nat := 118140960795 + 137740 * 2 ^ 59
def prefixEnd_137740 : Nat := 4983230072969 + 3 ^ 40 * 137740 * 2
def baseEnd_137740 : Nat := 4656910311137206605205

theorem tailTrace_137740 : CollatzResearch.WordTrace tailWord_137740 prefixEnd_137740 4656910311137206605205 := by
  unfold tailWord_137740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511895260499489482129337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3349193680665985976172449 2511895260499489482129337)
  ·
    refine ⟨1883921445374617111597003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2511895260499489482129337 1883921445374617111597003)
    ·
      refine ⟨2825882168061925667395505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1883921445374617111597003 2825882168061925667395505)
      ·
        refine ⟨2119411626046444250546629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2825882168061925667395505 2119411626046444250546629)
        ·
          refine ⟨397389679883708296977493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2119411626046444250546629 397389679883708296977493)
          ·
            refine ⟨4656910311137206605205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 397389679883708296977493 4656910311137206605205)
            ·
              rfl

theorem cell19_137740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_137740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137740 prefixEnd_137740 := by exact prefixLift 137740
  have htrace : WordTrace (prefixWord ++ tailWord_137740) baseStart_137740 baseEnd_137740 := by
    simpa [prefixWord, tailWord_137740, baseEnd_137740] using wordTrace_append hprefix tailTrace_137740
  have hstable : (prefixWord ++ tailWord_137740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137740).length < 2 ^ (prefixWord ++ tailWord_137740).sum := by decide
  have hdescent : baseEnd_137740 < baseStart_137740 := by decide
  rcases family_descends (prefixWord ++ tailWord_137740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137757 : List Nat := [1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_137757 : Nat := 118140960795 + 137757 * 2 ^ 59
def prefixEnd_137757 : Nat := 4983230072969 + 3 ^ 40 * 137757 * 2
def baseEnd_137757 : Nat := 41917365642383857069021

theorem tailTrace_137757 : CollatzResearch.WordTrace tailWord_137757 prefixEnd_137757 41917365642383857069021 := by
  unfold tailWord_137757
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024410561937390867627525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3349607041291593911751683 5024410561937390867627525)
  ·
    refine ⟨942076980363260787680161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5024410561937390867627525 942076980363260787680161)
    ·
      refine ⟨706557735272445590760121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 942076980363260787680161 706557735272445590760121)
      ·
        refine ⟨529918301454334193070091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706557735272445590760121 529918301454334193070091)
        ·
          refine ⟨794877452181501289605137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529918301454334193070091 794877452181501289605137)
          ·
            refine ⟨596158089136125967203853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794877452181501289605137 596158089136125967203853)
            ·
              refine ⟨223559283426047237701445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 596158089136125967203853 223559283426047237701445)
              ·
                refine ⟨41917365642383857069021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223559283426047237701445 41917365642383857069021)
                ·
                  rfl

theorem cell19_137757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_137757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137757 prefixEnd_137757 := by exact prefixLift 137757
  have htrace : WordTrace (prefixWord ++ tailWord_137757) baseStart_137757 baseEnd_137757 := by
    simpa [prefixWord, tailWord_137757, baseEnd_137757] using wordTrace_append hprefix tailTrace_137757
  have hstable : (prefixWord ++ tailWord_137757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137757).length < 2 ^ (prefixWord ++ tailWord_137757).sum := by decide
  have hdescent : baseEnd_137757 < baseStart_137757 := by decide
  rcases family_descends (prefixWord ++ tailWord_137757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137778 : List Nat := [3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_137778 : Nat := 118140960795 + 137778 * 2 ^ 59
def prefixEnd_137778 : Nat := 4983230072969 + 3 ^ 40 * 137778 * 2
def baseEnd_137778 : Nat := 41923755623862030602297

theorem tailTrace_137778 : CollatzResearch.WordTrace tailWord_137778 prefixEnd_137778 41923755623862030602297 := by
  unfold tailWord_137778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256294123715327863535497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3350117663240874302761325 1256294123715327863535497)
  ·
    refine ⟨942220592786495897651623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1256294123715327863535497 942220592786495897651623)
    ·
      refine ⟨1413330889179743846477435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942220592786495897651623 1413330889179743846477435)
      ·
        refine ⟨2119996333769615769716153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413330889179743846477435 2119996333769615769716153)
        ·
          refine ⟨1589997250327211827287115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119996333769615769716153 1589997250327211827287115)
          ·
            refine ⟨2384995875490817740930673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589997250327211827287115 2384995875490817740930673)
            ·
              refine ⟨1788746906618113305698005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384995875490817740930673 1788746906618113305698005)
              ·
                refine ⟨41923755623862030602297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1788746906618113305698005 41923755623862030602297)
                ·
                  rfl

theorem cell19_137778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_137778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137778 prefixEnd_137778 := by exact prefixLift 137778
  have htrace : WordTrace (prefixWord ++ tailWord_137778) baseStart_137778 baseEnd_137778 := by
    simpa [prefixWord, tailWord_137778, baseEnd_137778] using wordTrace_append hprefix tailTrace_137778
  have hstable : (prefixWord ++ tailWord_137778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137778).length < 2 ^ (prefixWord ++ tailWord_137778).sum := by decide
  have hdescent : baseEnd_137778 < baseStart_137778 := by decide
  rcases family_descends (prefixWord ++ tailWord_137778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137797 : List Nat := [1, 3, 1, 1, 1, 6, 6]
def baseStart_137797 : Nat := 118140960795 + 137797 * 2 ^ 59
def prefixEnd_137797 : Nat := 4983230072969 + 3 ^ 40 * 137797 * 2
def baseEnd_137797 : Nat := 13976512345225205393341

theorem tailTrace_137797 : CollatzResearch.WordTrace tailWord_137797 prefixEnd_137797 13976512345225205393341 := by
  unfold tailWord_137797
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025869481792477699083645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3350579654528318466055763 5025869481792477699083645)
  ·
    refine ⟨1884701055672179137156367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5025869481792477699083645 1884701055672179137156367)
    ·
      refine ⟨2827051583508268705734551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1884701055672179137156367 2827051583508268705734551)
      ·
        refine ⟨4240577375262403058601827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827051583508268705734551 4240577375262403058601827)
        ·
          refine ⟨6360866062893604587902741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240577375262403058601827 6360866062893604587902741)
          ·
            refine ⟨298165596698137715057941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6360866062893604587902741 298165596698137715057941)
            ·
              refine ⟨13976512345225205393341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 298165596698137715057941 13976512345225205393341)
              ·
                rfl

theorem cell19_137797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_137797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137797 prefixEnd_137797 := by exact prefixLift 137797
  have htrace : WordTrace (prefixWord ++ tailWord_137797) baseStart_137797 baseEnd_137797 := by
    simpa [prefixWord, tailWord_137797, baseEnd_137797] using wordTrace_append hprefix tailTrace_137797
  have hstable : (prefixWord ++ tailWord_137797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137797).length < 2 ^ (prefixWord ++ tailWord_137797).sum := by decide
  have hdescent : baseEnd_137797 < baseStart_137797 := by decide
  rcases family_descends (prefixWord ++ tailWord_137797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137829 : List Nat := [1, 3, 1, 3, 5, 1, 2, 3]
def baseStart_137829 : Nat := 118140960795 + 137829 * 2 ^ 59
def prefixEnd_137829 : Nat := 4983230072969 + 3 ^ 40 * 137829 * 2
def baseEnd_137829 : Nat := 41939274150309023468825

theorem tailTrace_137829 : CollatzResearch.WordTrace tailWord_137829 prefixEnd_137829 41939274150309023468825 := by
  unfold tailWord_137829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5027036617676547164248541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3351357745117698109499027 5027036617676547164248541)
  ·
    refine ⟨1885138731628705186593203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5027036617676547164248541 1885138731628705186593203)
    ·
      refine ⟨2827708097443057779889805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885138731628705186593203 2827708097443057779889805)
      ·
        refine ⟨1060390536541146667458677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2827708097443057779889805 1060390536541146667458677)
        ·
          refine ⟨99411612800732500074251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1060390536541146667458677 99411612800732500074251)
          ·
            refine ⟨149117419201098750111377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99411612800732500074251 149117419201098750111377)
            ·
              refine ⟨111838064400824062583533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149117419201098750111377 111838064400824062583533)
              ·
                refine ⟨41939274150309023468825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111838064400824062583533 41939274150309023468825)
                ·
                  rfl

theorem cell19_137829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_137829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137829 prefixEnd_137829 := by exact prefixLift 137829
  have htrace : WordTrace (prefixWord ++ tailWord_137829) baseStart_137829 baseEnd_137829 := by
    simpa [prefixWord, tailWord_137829, baseEnd_137829] using wordTrace_append hprefix tailTrace_137829
  have hstable : (prefixWord ++ tailWord_137829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137829).length < 2 ^ (prefixWord ++ tailWord_137829).sum := by decide
  have hdescent : baseEnd_137829 < baseStart_137829 := by decide
  rcases family_descends (prefixWord ++ tailWord_137829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137892 : List Nat := [2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_137892 : Nat := 118140960795 + 137892 * 2 ^ 59
def prefixEnd_137892 : Nat := 4983230072969 + 3 ^ 40 * 137892 * 2
def baseEnd_137892 : Nat := 41958444094743544068653

theorem tailTrace_137892 : CollatzResearch.WordTrace tailWord_137892 prefixEnd_137892 41958444094743544068653 := by
  unfold tailWord_137892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514667208224154461895965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3352889610965539282527953 2514667208224154461895965)
  ·
    refine ⟨943000203084057923210987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2514667208224154461895965 943000203084057923210987)
    ·
      refine ⟨1414500304626086884816481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943000203084057923210987 1414500304626086884816481)
      ·
        refine ⟨1060875228469565163612361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1414500304626086884816481 1060875228469565163612361)
        ·
          refine ⟨795656421352173872709271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1060875228469565163612361 795656421352173872709271)
          ·
            refine ⟨1193484632028260809063907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795656421352173872709271 1193484632028260809063907)
            ·
              refine ⟨1790226948042391213595861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193484632028260809063907 1790226948042391213595861)
              ·
                refine ⟨41958444094743544068653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1790226948042391213595861 41958444094743544068653)
                ·
                  rfl

theorem cell19_137892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_137892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137892 prefixEnd_137892 := by exact prefixLift 137892
  have htrace : WordTrace (prefixWord ++ tailWord_137892) baseStart_137892 baseEnd_137892 := by
    simpa [prefixWord, tailWord_137892, baseEnd_137892] using wordTrace_append hprefix tailTrace_137892
  have hstable : (prefixWord ++ tailWord_137892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137892).length < 2 ^ (prefixWord ++ tailWord_137892).sum := by decide
  have hdescent : baseEnd_137892 < baseStart_137892 := by decide
  rcases family_descends (prefixWord ++ tailWord_137892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137911 : List Nat := [1, 1, 3, 1, 6, 7]
def baseStart_137911 : Nat := 118140960795 + 137911 * 2 ^ 59
def prefixEnd_137911 : Nat := 4983230072969 + 3 ^ 40 * 137911 * 2
def baseEnd_137911 : Nat := 4662691722950792182931

theorem tailTrace_137911 : CollatzResearch.WordTrace tailWord_137911 prefixEnd_137911 4662691722950792182931 := by
  unfold tailWord_137911
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030027403379475168733587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3353351602252983445822391 5030027403379475168733587)
  ·
    refine ⟨7545041105069212753100381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5030027403379475168733587 7545041105069212753100381)
    ·
      refine ⟨2829390414400954782412643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7545041105069212753100381 2829390414400954782412643)
      ·
        refine ⟨4244085621601432173618965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829390414400954782412643 4244085621601432173618965)
        ·
          refine ⟨198941513512567133138389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4244085621601432173618965 198941513512567133138389)
          ·
            refine ⟨4662691722950792182931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 198941513512567133138389 4662691722950792182931)
            ·
              rfl

theorem cell19_137911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_137911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137911 prefixEnd_137911 := by exact prefixLift 137911
  have htrace : WordTrace (prefixWord ++ tailWord_137911) baseStart_137911 baseEnd_137911 := by
    simpa [prefixWord, tailWord_137911, baseEnd_137911] using wordTrace_append hprefix tailTrace_137911
  have hstable : (prefixWord ++ tailWord_137911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137911).length < 2 ^ (prefixWord ++ tailWord_137911).sum := by decide
  have hdescent : baseEnd_137911 < baseStart_137911 := by decide
  rcases family_descends (prefixWord ++ tailWord_137911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137928 : List Nat := [2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_137928 : Nat := 118140960795 + 137928 * 2 ^ 59
def prefixEnd_137928 : Nat := 4983230072969 + 3 ^ 40 * 137928 * 2
def baseEnd_137928 : Nat := 41969398348706127268555

theorem tailTrace_137928 : CollatzResearch.WordTrace tailWord_137928 prefixEnd_137928 41969398348706127268555 := by
  unfold tailWord_137928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515323722158943536051219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3353764962878591381401625 2515323722158943536051219)
  ·
    refine ⟨3772985583238415304076829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515323722158943536051219 3772985583238415304076829)
    ·
      refine ⟨1414869593714405739028811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3772985583238415304076829 1414869593714405739028811)
      ·
        refine ⟨2122304390571608608543217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414869593714405739028811 2122304390571608608543217)
        ·
          refine ⟨1591728292928706456407413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2122304390571608608543217 1591728292928706456407413)
          ·
            refine ⟨149224527462066230288195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1591728292928706456407413 149224527462066230288195)
            ·
              refine ⟨223836791193099345432293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149224527462066230288195 223836791193099345432293)
              ·
                refine ⟨41969398348706127268555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223836791193099345432293 41969398348706127268555)
                ·
                  rfl

theorem cell19_137928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_137928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_137928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_137928 prefixEnd_137928 := by exact prefixLift 137928
  have htrace : WordTrace (prefixWord ++ tailWord_137928) baseStart_137928 baseEnd_137928 := by
    simpa [prefixWord, tailWord_137928, baseEnd_137928] using wordTrace_append hprefix tailTrace_137928
  have hstable : (prefixWord ++ tailWord_137928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137928).length < 2 ^ (prefixWord ++ tailWord_137928).sum := by decide
  have hdescent : baseEnd_137928 < baseStart_137928 := by decide
  rcases family_descends (prefixWord ++ tailWord_137928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138002 : List Nat := [3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_138002 : Nat := 118140960795 + 138002 * 2 ^ 59
def prefixEnd_138002 : Nat := 4983230072969 + 3 ^ 40 * 138002 * 2
def baseEnd_138002 : Nat := 41991915426295881623909

theorem tailTrace_138002 : CollatzResearch.WordTrace tailWord_138002 prefixEnd_138002 41991915426295881623909 := by
  unfold tailWord_138002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258336611512449427574065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3355564297366531806864173 1258336611512449427574065)
  ·
    refine ⟨943752458634337070680549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1258336611512449427574065 943752458634337070680549)
    ·
      refine ⟨176953585993938200752603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 943752458634337070680549 176953585993938200752603)
      ·
        refine ⟨265430378990907301128905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176953585993938200752603 265430378990907301128905)
        ·
          refine ⟨199072784243180475846679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265430378990907301128905 199072784243180475846679)
          ·
            refine ⟨298609176364770713770019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199072784243180475846679 298609176364770713770019)
            ·
              refine ⟨447913764547156070655029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298609176364770713770019 447913764547156070655029)
              ·
                refine ⟨41991915426295881623909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 447913764547156070655029 41991915426295881623909)
                ·
                  rfl

theorem cell19_138002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_138002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138002 prefixEnd_138002 := by exact prefixLift 138002
  have htrace : WordTrace (prefixWord ++ tailWord_138002) baseStart_138002 baseEnd_138002 := by
    simpa [prefixWord, tailWord_138002, baseEnd_138002] using wordTrace_append hprefix tailTrace_138002
  have hstable : (prefixWord ++ tailWord_138002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138002).length < 2 ^ (prefixWord ++ tailWord_138002).sum := by decide
  have hdescent : baseEnd_138002 < baseStart_138002 := by decide
  rcases family_descends (prefixWord ++ tailWord_138002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138042 : List Nat := [3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_138042 : Nat := 118140960795 + 138042 * 2 ^ 59
def prefixEnd_138042 : Nat := 4983230072969 + 3 ^ 40 * 138042 * 2
def baseEnd_138042 : Nat := 42004086819587640734911

theorem tailTrace_138042 : CollatzResearch.WordTrace tailWord_138042 prefixEnd_138042 42004086819587640734911 := by
  unfold tailWord_138042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258701341476221135438095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3356536910603256361168253 1258701341476221135438095)
  ·
    refine ⟨1888052012214331703157143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258701341476221135438095 1888052012214331703157143)
    ·
      refine ⟨2832078018321497554735715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1888052012214331703157143 2832078018321497554735715)
      ·
        refine ⟨4248117027482246332103573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832078018321497554735715 4248117027482246332103573)
        ·
          refine ⟨199130485663230296817355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4248117027482246332103573 199130485663230296817355)
          ·
            refine ⟨298695728494845445226033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199130485663230296817355 298695728494845445226033)
            ·
              refine ⟨224021796371134083919525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298695728494845445226033 224021796371134083919525)
              ·
                refine ⟨42004086819587640734911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224021796371134083919525 42004086819587640734911)
                ·
                  rfl

theorem cell19_138042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_138042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138042 prefixEnd_138042 := by exact prefixLift 138042
  have htrace : WordTrace (prefixWord ++ tailWord_138042) baseStart_138042 baseEnd_138042 := by
    simpa [prefixWord, tailWord_138042, baseEnd_138042] using wordTrace_append hprefix tailTrace_138042
  have hstable : (prefixWord ++ tailWord_138042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138042).length < 2 ^ (prefixWord ++ tailWord_138042).sum := by decide
  have hdescent : baseEnd_138042 < baseStart_138042 := by decide
  rcases family_descends (prefixWord ++ tailWord_138042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138082 : List Nat := [3, 3, 2, 1, 10]
def baseStart_138082 : Nat := 118140960795 + 138082 * 2 ^ 59
def prefixEnd_138082 : Nat := 4983230072969 + 3 ^ 40 * 138082 * 2
def baseEnd_138082 : Nat := 1556157711588125920219

theorem tailTrace_138082 : CollatzResearch.WordTrace tailWord_138082 prefixEnd_138082 1556157711588125920219 := by
  unfold tailWord_138082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259066071439992843302125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3357509523839980915472333 1259066071439992843302125)
  ·
    refine ⟨472149776789997316238297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1259066071439992843302125 472149776789997316238297)
    ·
      refine ⟨354112332592497987178723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 472149776789997316238297 354112332592497987178723)
      ·
        refine ⟨531168498888746980768085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354112332592497987178723 531168498888746980768085)
        ·
          refine ⟨1556157711588125920219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 531168498888746980768085 1556157711588125920219)
          ·
            rfl

theorem cell19_138082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 10].length) (baseStart_138082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138082 prefixEnd_138082 := by exact prefixLift 138082
  have htrace : WordTrace (prefixWord ++ tailWord_138082) baseStart_138082 baseEnd_138082 := by
    simpa [prefixWord, tailWord_138082, baseEnd_138082] using wordTrace_append hprefix tailTrace_138082
  have hstable : (prefixWord ++ tailWord_138082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138082).length < 2 ^ (prefixWord ++ tailWord_138082).sum := by decide
  have hdescent : baseEnd_138082 < baseStart_138082 := by decide
  rcases family_descends (prefixWord ++ tailWord_138082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138173 : List Nat := [1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_138173 : Nat := 118140960795 + 138173 * 2 ^ 59
def prefixEnd_138173 : Nat := 4983230072969 + 3 ^ 40 * 138173 * 2
def baseEnd_138173 : Nat := 42043948132618151823443

theorem tailTrace_138173 : CollatzResearch.WordTrace tailWord_138173 prefixEnd_138173 42043948132618151823443 := by
  unfold tailWord_138173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5039583328430293914771173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3359722218953529276514115 5039583328430293914771173)
  ·
    refine ⟨944921874080680109019595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5039583328430293914771173 944921874080680109019595)
    ·
      refine ⟨1417382811121020163529393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944921874080680109019595 1417382811121020163529393)
      ·
        refine ⟨1063037108340765122647045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417382811121020163529393 1063037108340765122647045)
        ·
          refine ⟨199319457813893460496321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1063037108340765122647045 199319457813893460496321)
          ·
            refine ⟨149489593360420095372241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199319457813893460496321 149489593360420095372241)
            ·
              refine ⟨112117195020315071529181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149489593360420095372241 112117195020315071529181)
              ·
                refine ⟨42043948132618151823443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112117195020315071529181 42043948132618151823443)
                ·
                  rfl

theorem cell19_138173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_138173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138173 prefixEnd_138173 := by exact prefixLift 138173
  have htrace : WordTrace (prefixWord ++ tailWord_138173) baseStart_138173 baseEnd_138173 := by
    simpa [prefixWord, tailWord_138173, baseEnd_138173] using wordTrace_append hprefix tailTrace_138173
  have hstable : (prefixWord ++ tailWord_138173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138173).length < 2 ^ (prefixWord ++ tailWord_138173).sum := by decide
  have hdescent : baseEnd_138173 < baseStart_138173 := by decide
  rcases family_descends (prefixWord ++ tailWord_138173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138179 : List Nat := [1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_138179 : Nat := 118140960795 + 138179 * 2 ^ 59
def prefixEnd_138179 : Nat := 4983230072969 + 3 ^ 40 * 138179 * 2
def baseEnd_138179 : Nat := 42045773841611915690093

theorem tailTrace_138179 : CollatzResearch.WordTrace tailWord_138179 prefixEnd_138179 42045773841611915690093 := by
  unfold tailWord_138179
  simp only [CollatzResearch.WordTrace]
  refine ⟨5039802166408556939489591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3359868110939037959659727 5039802166408556939489591)
  ·
    refine ⟨7559703249612835409234387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5039802166408556939489591 7559703249612835409234387)
    ·
      refine ⟨11339554874419253113851581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7559703249612835409234387 11339554874419253113851581)
      ·
        refine ⟨4252333077907219917694343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11339554874419253113851581 4252333077907219917694343)
        ·
          refine ⟨6378499616860829876541515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4252333077907219917694343 6378499616860829876541515)
          ·
            refine ⟨9567749425291244814812273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6378499616860829876541515 9567749425291244814812273)
            ·
              refine ⟨7175812068968433611109205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9567749425291244814812273 7175812068968433611109205)
              ·
                refine ⟨42045773841611915690093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7175812068968433611109205 42045773841611915690093)
                ·
                  rfl

theorem cell19_138179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_138179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138179 prefixEnd_138179 := by exact prefixLift 138179
  have htrace : WordTrace (prefixWord ++ tailWord_138179) baseStart_138179 baseEnd_138179 := by
    simpa [prefixWord, tailWord_138179, baseEnd_138179] using wordTrace_append hprefix tailTrace_138179
  have hstable : (prefixWord ++ tailWord_138179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138179).length < 2 ^ (prefixWord ++ tailWord_138179).sum := by decide
  have hdescent : baseEnd_138179 < baseStart_138179 := by decide
  rcases family_descends (prefixWord ++ tailWord_138179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138194 : List Nat := [3, 2, 2, 3, 1, 3, 5]
def baseStart_138194 : Nat := 118140960795 + 138194 * 2 ^ 59
def prefixEnd_138194 : Nat := 4983230072969 + 3 ^ 40 * 138194 * 2
def baseEnd_138194 : Nat := 14016779371365441785573

theorem tailTrace_138194 : CollatzResearch.WordTrace tailWord_138194 prefixEnd_138194 14016779371365441785573 := by
  unfold tailWord_138194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260087315338553625321409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3360232840902809667523757 1260087315338553625321409)
  ·
    refine ⟨945065486503915218991057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1260087315338553625321409 945065486503915218991057)
    ·
      refine ⟨708799114877936414243293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945065486503915218991057 708799114877936414243293)
      ·
        refine ⟨265799668079226155341235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 708799114877936414243293 265799668079226155341235)
        ·
          refine ⟨398699502118839233011853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265799668079226155341235 398699502118839233011853)
          ·
            refine ⟨149512313294564712379445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398699502118839233011853 149512313294564712379445)
            ·
              refine ⟨14016779371365441785573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149512313294564712379445 14016779371365441785573)
              ·
                rfl

theorem cell19_138194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_138194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138194 prefixEnd_138194 := by exact prefixLift 138194
  have htrace : WordTrace (prefixWord ++ tailWord_138194) baseStart_138194 baseEnd_138194 := by
    simpa [prefixWord, tailWord_138194, baseEnd_138194] using wordTrace_append hprefix tailTrace_138194
  have hstable : (prefixWord ++ tailWord_138194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138194).length < 2 ^ (prefixWord ++ tailWord_138194).sum := by decide
  have hdescent : baseEnd_138194 < baseStart_138194 := by decide
  rcases family_descends (prefixWord ++ tailWord_138194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138196 : List Nat := [2, 4, 1, 2, 1, 2, 7]
def baseStart_138196 : Nat := 118140960795 + 138196 * 2 ^ 59
def prefixEnd_138196 : Nat := 4983230072969 + 3 ^ 40 * 138196 * 2
def baseEnd_138196 : Nat := 14016982227920304437423

theorem tailTrace_138196 : CollatzResearch.WordTrace tailWord_138196 prefixEnd_138196 14016982227920304437423 := by
  unfold tailWord_138196
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520211103673484421429221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3360281471564645895238961 2520211103673484421429221)
  ·
    refine ⟨472539581938778329017979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2520211103673484421429221 472539581938778329017979)
    ·
      refine ⟨708809372908167493526969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472539581938778329017979 708809372908167493526969)
      ·
        refine ⟨531607029681125620145227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708809372908167493526969 531607029681125620145227)
        ·
          refine ⟨797410544521688430217841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531607029681125620145227 797410544521688430217841)
          ·
            refine ⟨598057908391266322663381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797410544521688430217841 598057908391266322663381)
            ·
              refine ⟨14016982227920304437423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 598057908391266322663381 14016982227920304437423)
              ·
                rfl

theorem cell19_138196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_138196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138196 prefixEnd_138196 := by exact prefixLift 138196
  have htrace : WordTrace (prefixWord ++ tailWord_138196) baseStart_138196 baseEnd_138196 := by
    simpa [prefixWord, tailWord_138196, baseEnd_138196] using wordTrace_append hprefix tailTrace_138196
  have hstable : (prefixWord ++ tailWord_138196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138196).length < 2 ^ (prefixWord ++ tailWord_138196).sum := by decide
  have hdescent : baseEnd_138196 < baseStart_138196 := by decide
  rcases family_descends (prefixWord ++ tailWord_138196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138215 : List Nat := [1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_138215 : Nat := 118140960795 + 138215 * 2 ^ 59
def prefixEnd_138215 : Nat := 4983230072969 + 3 ^ 40 * 138215 * 2
def baseEnd_138215 : Nat := 42056728095574498889995

theorem tailTrace_138215 : CollatzResearch.WordTrace tailWord_138215 prefixEnd_138215 42056728095574498889995 := by
  unfold tailWord_138215
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041115194278135087800099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3360743462852090058533399 5041115194278135087800099)
  ·
    refine ⟨7561672791417202631700149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5041115194278135087800099 7561672791417202631700149)
    ·
      refine ⟨708906824195362746721889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7561672791417202631700149 708906824195362746721889)
      ·
        refine ⟨531680118146522060041417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708906824195362746721889 531680118146522060041417)
        ·
          refine ⟨398760088609891545031063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531680118146522060041417 398760088609891545031063)
          ·
            refine ⟨598140132914837317546595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398760088609891545031063 598140132914837317546595)
            ·
              refine ⟨897210199372255976319893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598140132914837317546595 897210199372255976319893)
              ·
                refine ⟨42056728095574498889995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 897210199372255976319893 42056728095574498889995)
                ·
                  rfl

theorem cell19_138215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_138215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138215 prefixEnd_138215 := by exact prefixLift 138215
  have htrace : WordTrace (prefixWord ++ tailWord_138215) baseStart_138215 baseEnd_138215 := by
    simpa [prefixWord, tailWord_138215, baseEnd_138215] using wordTrace_append hprefix tailTrace_138215
  have hstable : (prefixWord ++ tailWord_138215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138215).length < 2 ^ (prefixWord ++ tailWord_138215).sum := by decide
  have hdescent : baseEnd_138215 < baseStart_138215 := by decide
  rcases family_descends (prefixWord ++ tailWord_138215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138268 : List Nat := [2, 2, 3, 1, 5, 1, 1, 4]
def baseStart_138268 : Nat := 118140960795 + 138268 * 2 ^ 59
def prefixEnd_138268 : Nat := 4983230072969 + 3 ^ 40 * 138268 * 2
def baseEnd_138268 : Nat := 42072855191686079712073

theorem tailTrace_138268 : CollatzResearch.WordTrace tailWord_138268 prefixEnd_138268 42072855191686079712073 := by
  unfold tailWord_138268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521524131543062569739729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3362032175390750092986305 2521524131543062569739729)
  ·
    refine ⟨1891143098657296927304797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2521524131543062569739729 1891143098657296927304797)
    ·
      refine ⟨709178661996486347739299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1891143098657296927304797 709178661996486347739299)
      ·
        refine ⟨1063767992994729521608949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709178661996486347739299 1063767992994729521608949)
        ·
          refine ⟨99728249343255892650839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1063767992994729521608949 99728249343255892650839)
          ·
            refine ⟨149592374014883838976259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99728249343255892650839 149592374014883838976259)
            ·
              refine ⟨224388561022325758464389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149592374014883838976259 224388561022325758464389)
              ·
                refine ⟨42072855191686079712073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224388561022325758464389 42072855191686079712073)
                ·
                  rfl

theorem cell19_138268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_138268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138268 prefixEnd_138268 := by exact prefixLift 138268
  have htrace : WordTrace (prefixWord ++ tailWord_138268) baseStart_138268 baseEnd_138268 := by
    simpa [prefixWord, tailWord_138268, baseEnd_138268] using wordTrace_append hprefix tailTrace_138268
  have hstable : (prefixWord ++ tailWord_138268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138268).length < 2 ^ (prefixWord ++ tailWord_138268).sum := by decide
  have hdescent : baseEnd_138268 < baseStart_138268 := by decide
  rcases family_descends (prefixWord ++ tailWord_138268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138312 : List Nat := [2, 1, 3, 1, 1, 1, 10]
def baseStart_138312 : Nat := 118140960795 + 138312 * 2 ^ 59
def prefixEnd_138312 : Nat := 4983230072969 + 3 ^ 40 * 138312 * 2
def baseEnd_138312 : Nat := 14028747908102338244725

theorem tailTrace_138312 : CollatzResearch.WordTrace tailWord_138312 prefixEnd_138312 14028747908102338244725 := by
  unfold tailWord_138312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522326537463360327040595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3363102049951147102720793 2522326537463360327040595)
  ·
    refine ⟨3783489806195040490560893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2522326537463360327040595 3783489806195040490560893)
    ·
      refine ⟨1418808677323140183960335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3783489806195040490560893 1418808677323140183960335)
      ·
        refine ⟨2128213015984710275940503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418808677323140183960335 2128213015984710275940503)
        ·
          refine ⟨3192319523977065413910755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128213015984710275940503 3192319523977065413910755)
          ·
            refine ⟨4788479285965598120866133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192319523977065413910755 4788479285965598120866133)
            ·
              refine ⟨14028747908102338244725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4788479285965598120866133 14028747908102338244725)
              ·
                rfl

theorem cell19_138312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_138312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138312 prefixEnd_138312 := by exact prefixLift 138312
  have htrace : WordTrace (prefixWord ++ tailWord_138312) baseStart_138312 baseEnd_138312 := by
    simpa [prefixWord, tailWord_138312, baseEnd_138312] using wordTrace_append hprefix tailTrace_138312
  have hstable : (prefixWord ++ tailWord_138312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138312).length < 2 ^ (prefixWord ++ tailWord_138312).sum := by decide
  have hdescent : baseEnd_138312 < baseStart_138312 := by decide
  rcases family_descends (prefixWord ++ tailWord_138312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138346 : List Nat := [3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_138346 : Nat := 118140960795 + 138346 * 2 ^ 59
def prefixEnd_138346 : Nat := 4983230072969 + 3 ^ 40 * 138346 * 2
def baseEnd_138346 : Nat := 42096589408605009978527

theorem tailTrace_138346 : CollatzResearch.WordTrace tailWord_138346 prefixEnd_138346 42096589408605009978527 := by
  unfold tailWord_138346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261473289200886115204723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3363928771202362973879261 1261473289200886115204723)
  ·
    refine ⟨1892209933801329172807085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1261473289200886115204723 1892209933801329172807085)
    ·
      refine ⟨709578725175498439802657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1892209933801329172807085 709578725175498439802657)
      ·
        refine ⟨532184043881623829851993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 709578725175498439802657 532184043881623829851993)
        ·
          refine ⟨399138032911217872388995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532184043881623829851993 399138032911217872388995)
          ·
            refine ⟨598707049366826808583493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399138032911217872388995 598707049366826808583493)
            ·
              refine ⟨112257571756280026609405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 598707049366826808583493 112257571756280026609405)
              ·
                refine ⟨42096589408605009978527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112257571756280026609405 42096589408605009978527)
                ·
                  rfl

theorem cell19_138346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_138346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138346 prefixEnd_138346 := by exact prefixLift 138346
  have htrace : WordTrace (prefixWord ++ tailWord_138346) baseStart_138346 baseEnd_138346 := by
    simpa [prefixWord, tailWord_138346, baseEnd_138346] using wordTrace_append hprefix tailTrace_138346
  have hstable : (prefixWord ++ tailWord_138346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138346).length < 2 ^ (prefixWord ++ tailWord_138346).sum := by decide
  have hdescent : baseEnd_138346 < baseStart_138346 := by decide
  rcases family_descends (prefixWord ++ tailWord_138346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138386 : List Nat := [3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_138386 : Nat := 118140960795 + 138386 * 2 ^ 59
def prefixEnd_138386 : Nat := 4983230072969 + 3 ^ 40 * 138386 * 2
def baseEnd_138386 : Nat := 42108760801896769089529

theorem tailTrace_138386 : CollatzResearch.WordTrace tailWord_138386 prefixEnd_138386 42108760801896769089529 := by
  unfold tailWord_138386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261838019164657823068753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3364901384439087528183341 1261838019164657823068753)
  ·
    refine ⟨946378514373493367301565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1261838019164657823068753 946378514373493367301565)
    ·
      refine ⟨354891942890060012738087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 946378514373493367301565 354891942890060012738087)
      ·
        refine ⟨532337914335090019107131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354891942890060012738087 532337914335090019107131)
        ·
          refine ⟨798506871502635028660697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532337914335090019107131 798506871502635028660697)
          ·
            refine ⟨598880153626976271495523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798506871502635028660697 598880153626976271495523)
            ·
              refine ⟨898320230440464407243285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598880153626976271495523 898320230440464407243285)
              ·
                refine ⟨42108760801896769089529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 898320230440464407243285 42108760801896769089529)
                ·
                  rfl

theorem cell19_138386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_138386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138386 prefixEnd_138386 := by exact prefixLift 138386
  have htrace : WordTrace (prefixWord ++ tailWord_138386) baseStart_138386 baseEnd_138386 := by
    simpa [prefixWord, tailWord_138386, baseEnd_138386] using wordTrace_append hprefix tailTrace_138386
  have hstable : (prefixWord ++ tailWord_138386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138386).length < 2 ^ (prefixWord ++ tailWord_138386).sum := by decide
  have hdescent : baseEnd_138386 < baseStart_138386 := by decide
  rcases family_descends (prefixWord ++ tailWord_138386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138422 : List Nat := [5, 1, 3, 2, 8]
def baseStart_138422 : Nat := 118140960795 + 138422 * 2 ^ 59
def prefixEnd_138422 : Nat := 4983230072969 + 3 ^ 40 * 138422 * 2
def baseEnd_138422 : Nat := 1559989446513309344053

theorem tailTrace_138422 : CollatzResearch.WordTrace tailWord_138422 prefixEnd_138422 1559989446513309344053 := by
  unfold tailWord_138422
  simp only [CollatzResearch.WordTrace]
  refine ⟨315541569033013090036595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3365776736352139627057013 315541569033013090036595)
  ·
    refine ⟨473312353549519635054893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 315541569033013090036595 473312353549519635054893)
    ·
      refine ⟨177492132581069863145585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 473312353549519635054893 177492132581069863145585)
      ·
        refine ⟨133119099435802397359189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177492132581069863145585 133119099435802397359189)
        ·
          refine ⟨1559989446513309344053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 133119099435802397359189 1559989446513309344053)
          ·
            rfl

theorem cell19_138422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 8].length) (baseStart_138422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138422 prefixEnd_138422 := by exact prefixLift 138422
  have htrace : WordTrace (prefixWord ++ tailWord_138422) baseStart_138422 baseEnd_138422 := by
    simpa [prefixWord, tailWord_138422, baseEnd_138422] using wordTrace_append hprefix tailTrace_138422
  have hstable : (prefixWord ++ tailWord_138422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138422).length < 2 ^ (prefixWord ++ tailWord_138422).sum := by decide
  have hdescent : baseEnd_138422 < baseStart_138422 := by decide
  rcases family_descends (prefixWord ++ tailWord_138422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138483 : List Nat := [1, 1, 1, 2, 2, 6, 6]
def baseStart_138483 : Nat := 118140960795 + 138483 * 2 ^ 59
def prefixEnd_138483 : Nat := 4983230072969 + 3 ^ 40 * 138483 * 2
def baseEnd_138483 : Nat := 14046092143543094977903

theorem tailTrace_138483 : CollatzResearch.WordTrace tailWord_138483 prefixEnd_138483 14046092143543094977903 := by
  unfold tailWord_138483
  simp only [CollatzResearch.WordTrace]
  refine ⟨5050889957307216858556103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3367259971538144572370735 5050889957307216858556103)
  ·
    refine ⟨7576334935960825287834155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5050889957307216858556103 7576334935960825287834155)
    ·
      refine ⟨11364502403941237931751233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7576334935960825287834155 11364502403941237931751233)
      ·
        refine ⟨8523376802955928448813425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11364502403941237931751233 8523376802955928448813425)
        ·
          refine ⟨6392532602216946336610069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8523376802955928448813425 6392532602216946336610069)
          ·
            refine ⟨299649965728919359528597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6392532602216946336610069 299649965728919359528597)
            ·
              refine ⟨14046092143543094977903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 299649965728919359528597 14046092143543094977903)
              ·
                rfl

theorem cell19_138483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_138483 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138483 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138483 prefixEnd_138483 := by exact prefixLift 138483
  have htrace : WordTrace (prefixWord ++ tailWord_138483) baseStart_138483 baseEnd_138483 := by
    simpa [prefixWord, tailWord_138483, baseEnd_138483] using wordTrace_append hprefix tailTrace_138483
  have hstable : (prefixWord ++ tailWord_138483).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138483).length < 2 ^ (prefixWord ++ tailWord_138483).sum := by decide
  have hdescent : baseEnd_138483 < baseStart_138483 := by decide
  rcases family_descends (prefixWord ++ tailWord_138483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138538 : List Nat := [3, 1, 4, 2, 1, 1, 7]
def baseStart_138538 : Nat := 118140960795 + 138538 * 2 ^ 59
def prefixEnd_138538 : Nat := 4983230072969 + 3 ^ 40 * 138538 * 2
def baseEnd_138538 : Nat := 14051670698801817903779

theorem tailTrace_138538 : CollatzResearch.WordTrace tailWord_138538 prefixEnd_138538 14051670698801817903779 := by
  unfold tailWord_138538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263223993026990312952067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3368597314738640834538845 1263223993026990312952067)
  ·
    refine ⟨1894835989540485469428101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1263223993026990312952067 1894835989540485469428101)
    ·
      refine ⟨355281748038841025517769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1894835989540485469428101 355281748038841025517769)
      ·
        refine ⟨266461311029130769138327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355281748038841025517769 266461311029130769138327)
        ·
          refine ⟨399691966543696153707491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266461311029130769138327 399691966543696153707491)
          ·
            refine ⟨599537949815544230561237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399691966543696153707491 599537949815544230561237)
            ·
              refine ⟨14051670698801817903779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 599537949815544230561237 14051670698801817903779)
              ·
                rfl

theorem cell19_138538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_138538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138538 prefixEnd_138538 := by exact prefixLift 138538
  have htrace : WordTrace (prefixWord ++ tailWord_138538) baseStart_138538 baseEnd_138538 := by
    simpa [prefixWord, tailWord_138538, baseEnd_138538] using wordTrace_append hprefix tailTrace_138538
  have hstable : (prefixWord ++ tailWord_138538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138538).length < 2 ^ (prefixWord ++ tailWord_138538).sum := by decide
  have hdescent : baseEnd_138538 < baseStart_138538 := by decide
  rcases family_descends (prefixWord ++ tailWord_138538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138559 : List Nat := [1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_138559 : Nat := 118140960795 + 138559 * 2 ^ 59
def prefixEnd_138559 : Nat := 4983230072969 + 3 ^ 40 * 138559 * 2
def baseEnd_138559 : Nat := 42161402077883627244613

theorem tailTrace_138559 : CollatzResearch.WordTrace tailWord_138559 prefixEnd_138559 42161402077883627244613 := by
  unfold tailWord_138559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053661905031881838322731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3369107936687921225548487 5053661905031881838322731)
  ·
    refine ⟨7580492857547822757484097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5053661905031881838322731 7580492857547822757484097)
    ·
      refine ⟨5685369643160867068113073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7580492857547822757484097 5685369643160867068113073)
      ·
        refine ⟨4264027232370650301084805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5685369643160867068113073 4264027232370650301084805)
        ·
          refine ⟨799505106069496931453401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4264027232370650301084805 799505106069496931453401)
          ·
            refine ⟨599628829552122698590051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799505106069496931453401 599628829552122698590051)
            ·
              refine ⟨899443244328184047885077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599628829552122698590051 899443244328184047885077)
              ·
                refine ⟨42161402077883627244613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 899443244328184047885077 42161402077883627244613)
                ·
                  rfl

theorem cell19_138559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_138559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138559 prefixEnd_138559 := by exact prefixLift 138559
  have htrace : WordTrace (prefixWord ++ tailWord_138559) baseStart_138559 baseEnd_138559 := by
    simpa [prefixWord, tailWord_138559, baseEnd_138559] using wordTrace_append hprefix tailTrace_138559
  have hstable : (prefixWord ++ tailWord_138559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138559).length < 2 ^ (prefixWord ++ tailWord_138559).sum := by decide
  have hdescent : baseEnd_138559 < baseStart_138559 := by decide
  rcases family_descends (prefixWord ++ tailWord_138559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138673 : List Nat := [1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_138673 : Nat := 118140960795 + 138673 * 2 ^ 59
def prefixEnd_138673 : Nat := 4983230072969 + 3 ^ 40 * 138673 * 2
def baseEnd_138673 : Nat := 42196090548765140710969

theorem tailTrace_138673 : CollatzResearch.WordTrace tailWord_138673 prefixEnd_138673 42196090548765140710969 := by
  unfold tailWord_138673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057819826618879307972673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3371879884412586205315115 5057819826618879307972673)
  ·
    refine ⟨3793364869964159480979505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5057819826618879307972673 3793364869964159480979505)
    ·
      refine ⟨2845023652473119610734629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3793364869964159480979505 2845023652473119610734629)
      ·
        refine ⟨533441934838709927012743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2845023652473119610734629 533441934838709927012743)
        ·
          refine ⟨800162902258064890519115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533441934838709927012743 800162902258064890519115)
          ·
            refine ⟨1200244353387097335778673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800162902258064890519115 1200244353387097335778673)
            ·
              refine ⟨900183265040323001834005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200244353387097335778673 900183265040323001834005)
              ·
                refine ⟨42196090548765140710969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 900183265040323001834005 42196090548765140710969)
                ·
                  rfl

theorem cell19_138673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_138673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138673 prefixEnd_138673 := by exact prefixLift 138673
  have htrace : WordTrace (prefixWord ++ tailWord_138673) baseStart_138673 baseEnd_138673 := by
    simpa [prefixWord, tailWord_138673, baseEnd_138673] using wordTrace_append hprefix tailTrace_138673
  have hstable : (prefixWord ++ tailWord_138673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138673).length < 2 ^ (prefixWord ++ tailWord_138673).sum := by decide
  have hdescent : baseEnd_138673 < baseStart_138673 := by decide
  rcases family_descends (prefixWord ++ tailWord_138673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138749 : List Nat := [1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_138749 : Nat := 118140960795 + 138749 * 2 ^ 59
def prefixEnd_138749 : Nat := 4983230072969 + 3 ^ 40 * 138749 * 2
def baseEnd_138749 : Nat := 42219216196019483021873

theorem tailTrace_138749 : CollatzResearch.WordTrace tailWord_138749 prefixEnd_138749 42219216196019483021873 := by
  unfold tailWord_138749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060591774343544287739301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3373727849562362858492867 5060591774343544287739301)
  ·
    refine ⟨948860957689414553951119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5060591774343544287739301 948860957689414553951119)
    ·
      refine ⟨1423291436534121830926679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948860957689414553951119 1423291436534121830926679)
      ·
        refine ⟨2134937154801182746390019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423291436534121830926679 2134937154801182746390019)
        ·
          refine ⟨3202405732201774119585029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134937154801182746390019 3202405732201774119585029)
          ·
            refine ⟨600451074787832647422193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3202405732201774119585029 600451074787832647422193)
            ·
              refine ⟨450338306090874485566645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600451074787832647422193 450338306090874485566645)
              ·
                refine ⟨42219216196019483021873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 450338306090874485566645 42219216196019483021873)
                ·
                  rfl

theorem cell19_138749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_138749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138749 prefixEnd_138749 := by exact prefixLift 138749
  have htrace : WordTrace (prefixWord ++ tailWord_138749) baseStart_138749 baseEnd_138749 := by
    simpa [prefixWord, tailWord_138749, baseEnd_138749] using wordTrace_append hprefix tailTrace_138749
  have hstable : (prefixWord ++ tailWord_138749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138749).length < 2 ^ (prefixWord ++ tailWord_138749).sum := by decide
  have hdescent : baseEnd_138749 < baseStart_138749 := by decide
  rcases family_descends (prefixWord ++ tailWord_138749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138766 : List Nat := [4, 1, 1, 2, 5, 6]
def baseStart_138766 : Nat := 118140960795 + 138766 * 2 ^ 59
def prefixEnd_138766 : Nat := 4983230072969 + 3 ^ 40 * 138766 * 2
def baseEnd_138766 : Nat := 4691598782018720071561

theorem tailTrace_138766 : CollatzResearch.WordTrace tailWord_138766 prefixEnd_138766 4691598782018720071561 := by
  unfold tailWord_138766
  simp only [CollatzResearch.WordTrace]
  refine ⟨632651476910244523888519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3374141210187970794072101 632651476910244523888519)
  ·
    refine ⟨948977215365366785832779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 632651476910244523888519 948977215365366785832779)
    ·
      refine ⟨1423465823048050178749169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948977215365366785832779 1423465823048050178749169)
      ·
        refine ⟨1067599367286037634061877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1423465823048050178749169 1067599367286037634061877)
        ·
          refine ⟨100087440683066028193301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1067599367286037634061877 100087440683066028193301)
          ·
            refine ⟨4691598782018720071561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100087440683066028193301 4691598782018720071561)
            ·
              rfl

theorem cell19_138766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_138766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138766 prefixEnd_138766 := by exact prefixLift 138766
  have htrace : WordTrace (prefixWord ++ tailWord_138766) baseStart_138766 baseEnd_138766 := by
    simpa [prefixWord, tailWord_138766, baseEnd_138766] using wordTrace_append hprefix tailTrace_138766
  have hstable : (prefixWord ++ tailWord_138766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138766).length < 2 ^ (prefixWord ++ tailWord_138766).sum := by decide
  have hdescent : baseEnd_138766 < baseStart_138766 := by decide
  rcases family_descends (prefixWord ++ tailWord_138766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138785 : List Nat := [1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_138785 : Nat := 118140960795 + 138785 * 2 ^ 59
def prefixEnd_138785 : Nat := 4983230072969 + 3 ^ 40 * 138785 * 2
def baseEnd_138785 : Nat := 42230170449982066221775

theorem tailTrace_138785 : CollatzResearch.WordTrace tailWord_138785 prefixEnd_138785 42230170449982066221775 := by
  unfold tailWord_138785
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061904802213122436049809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3374603201475414957366539 5061904802213122436049809)
  ·
    refine ⟨3796428601659841827037357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5061904802213122436049809 3796428601659841827037357)
    ·
      refine ⟨1423660725622440685139009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3796428601659841827037357 1423660725622440685139009)
      ·
        refine ⟨1067745544216830513854257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1423660725622440685139009 1067745544216830513854257)
        ·
          refine ⟨800809158162622885390693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067745544216830513854257 800809158162622885390693)
          ·
            refine ⟨150151717155491791010755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 800809158162622885390693 150151717155491791010755)
            ·
              refine ⟨225227575733237686516133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150151717155491791010755 225227575733237686516133)
              ·
                refine ⟨42230170449982066221775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225227575733237686516133 42230170449982066221775)
                ·
                  rfl

theorem cell19_138785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_138785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138785 prefixEnd_138785 := by exact prefixLift 138785
  have htrace : WordTrace (prefixWord ++ tailWord_138785) baseStart_138785 baseEnd_138785 := by
    simpa [prefixWord, tailWord_138785, baseEnd_138785] using wordTrace_append hprefix tailTrace_138785
  have hstable : (prefixWord ++ tailWord_138785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138785).length < 2 ^ (prefixWord ++ tailWord_138785).sum := by decide
  have hdescent : baseEnd_138785 < baseStart_138785 := by decide
  rcases family_descends (prefixWord ++ tailWord_138785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138861 : List Nat := [1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_138861 : Nat := 118140960795 + 138861 * 2 ^ 59
def prefixEnd_138861 : Nat := 4983230072969 + 3 ^ 40 * 138861 * 2
def baseEnd_138861 : Nat := 42253296097236408532679

theorem tailTrace_138861 : CollatzResearch.WordTrace tailWord_138861 prefixEnd_138861 42253296097236408532679 := by
  unfold tailWord_138861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064676749937787415816437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3376451166625191610544291 5064676749937787415816437)
  ·
    refine ⟨474813445306667570232791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5064676749937787415816437 474813445306667570232791)
    ·
      refine ⟨712220167960001355349187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474813445306667570232791 712220167960001355349187)
      ·
        refine ⟨1068330251940002033023781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712220167960001355349187 1068330251940002033023781)
        ·
          refine ⟨200311922238750381191959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1068330251940002033023781 200311922238750381191959)
          ·
            refine ⟨300467883358125571787939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200311922238750381191959 300467883358125571787939)
            ·
              refine ⟨450701825037188357681909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300467883358125571787939 450701825037188357681909)
              ·
                refine ⟨42253296097236408532679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 450701825037188357681909 42253296097236408532679)
                ·
                  rfl

theorem cell19_138861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_138861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138861 prefixEnd_138861 := by exact prefixLift 138861
  have htrace : WordTrace (prefixWord ++ tailWord_138861) baseStart_138861 baseEnd_138861 := by
    simpa [prefixWord, tailWord_138861, baseEnd_138861] using wordTrace_append hprefix tailTrace_138861
  have hstable : (prefixWord ++ tailWord_138861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138861).length < 2 ^ (prefixWord ++ tailWord_138861).sum := by decide
  have hdescent : baseEnd_138861 < baseStart_138861 := by decide
  rcases family_descends (prefixWord ++ tailWord_138861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138954 : List Nat := [3, 1, 2, 1, 6, 1, 1, 4]
def baseStart_138954 : Nat := 118140960795 + 138954 * 2 ^ 59
def prefixEnd_138954 : Nat := 4983230072969 + 3 ^ 40 * 138954 * 2
def baseEnd_138954 : Nat := 42281594586639748465759

theorem tailTrace_138954 : CollatzResearch.WordTrace tailWord_138954 prefixEnd_138954 42281594586639748465759 := by
  unfold tailWord_138954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267017184650216074737979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3378712492400576199301277 1267017184650216074737979)
  ·
    refine ⟨1900525776975324112106969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1267017184650216074737979 1900525776975324112106969)
    ·
      refine ⟨1425394332731493084080227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1900525776975324112106969 1425394332731493084080227)
      ·
        refine ⟨2138091499097239626120341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425394332731493084080227 2138091499097239626120341)
        ·
          refine ⟨100223039020183107474391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2138091499097239626120341 100223039020183107474391)
          ·
            refine ⟨150334558530274661211587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100223039020183107474391 150334558530274661211587)
            ·
              refine ⟨225501837795411991817381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150334558530274661211587 225501837795411991817381)
              ·
                refine ⟨42281594586639748465759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225501837795411991817381 42281594586639748465759)
                ·
                  rfl

theorem cell19_138954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_138954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138954 prefixEnd_138954 := by exact prefixLift 138954
  have htrace : WordTrace (prefixWord ++ tailWord_138954) baseStart_138954 baseEnd_138954 := by
    simpa [prefixWord, tailWord_138954, baseEnd_138954] using wordTrace_append hprefix tailTrace_138954
  have hstable : (prefixWord ++ tailWord_138954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138954).length < 2 ^ (prefixWord ++ tailWord_138954).sum := by decide
  have hdescent : baseEnd_138954 < baseStart_138954 := by decide
  rcases family_descends (prefixWord ++ tailWord_138954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138960 : List Nat := [2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_138960 : Nat := 118140960795 + 138960 * 2 ^ 59
def prefixEnd_138960 : Nat := 4983230072969 + 3 ^ 40 * 138960 * 2
def baseEnd_138960 : Nat := 42283420295633512332409

theorem tailTrace_138960 : CollatzResearch.WordTrace tailWord_138960 prefixEnd_138960 42283420295633512332409 := by
  unfold tailWord_138960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534143788289563661835167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3378858384386084882446889 2534143788289563661835167)
  ·
    refine ⟨3801215682434345492752751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2534143788289563661835167 3801215682434345492752751)
    ·
      refine ⟨5701823523651518239129127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3801215682434345492752751 5701823523651518239129127)
      ·
        refine ⟨8552735285477277358693691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701823523651518239129127 8552735285477277358693691)
        ·
          refine ⟨12829102928215916038040537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552735285477277358693691 12829102928215916038040537)
          ·
            refine ⟨9621827196161937028530403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12829102928215916038040537 9621827196161937028530403)
            ·
              refine ⟨14432740794242905542795605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9621827196161937028530403 14432740794242905542795605)
              ·
                refine ⟨42283420295633512332409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14432740794242905542795605 42283420295633512332409)
                ·
                  rfl

theorem cell19_138960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_138960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_138960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_138960 prefixEnd_138960 := by exact prefixLift 138960
  have htrace : WordTrace (prefixWord ++ tailWord_138960) baseStart_138960 baseEnd_138960 := by
    simpa [prefixWord, tailWord_138960, baseEnd_138960] using wordTrace_append hprefix tailTrace_138960
  have hstable : (prefixWord ++ tailWord_138960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138960).length < 2 ^ (prefixWord ++ tailWord_138960).sum := by decide
  have hdescent : baseEnd_138960 < baseStart_138960 := by decide
  rcases family_descends (prefixWord ++ tailWord_138960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139017 : List Nat := [1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_139017 : Nat := 118140960795 + 139017 * 2 ^ 59
def prefixEnd_139017 : Nat := 4983230072969 + 3 ^ 40 * 139017 * 2
def baseEnd_139017 : Nat := 42300764531074269065587

theorem tailTrace_139017 : CollatzResearch.WordTrace tailWord_139017 prefixEnd_139017 42300764531074269065587 := by
  unfold tailWord_139017
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070366537372626058495305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3380244358248417372330203 5070366537372626058495305)
  ·
    refine ⟨3802774903029469543871479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5070366537372626058495305 3802774903029469543871479)
    ·
      refine ⟨5704162354544204315807219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3802774903029469543871479 5704162354544204315807219)
      ·
        refine ⟨8556243531816306473710829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5704162354544204315807219 8556243531816306473710829)
        ·
          refine ⟨3208591324431114927641561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8556243531816306473710829 3208591324431114927641561)
          ·
            refine ⟨2406443493323336195731171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3208591324431114927641561 2406443493323336195731171)
            ·
              refine ⟨3609665239985004293596757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406443493323336195731171 3609665239985004293596757)
              ·
                refine ⟨42300764531074269065587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3609665239985004293596757 42300764531074269065587)
                ·
                  rfl

theorem cell19_139017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_139017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139017 prefixEnd_139017 := by exact prefixLift 139017
  have htrace : WordTrace (prefixWord ++ tailWord_139017) baseStart_139017 baseEnd_139017 := by
    simpa [prefixWord, tailWord_139017, baseEnd_139017] using wordTrace_append hprefix tailTrace_139017
  have hstable : (prefixWord ++ tailWord_139017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139017).length < 2 ^ (prefixWord ++ tailWord_139017).sum := by decide
  have hdescent : baseEnd_139017 < baseStart_139017 := by decide
  rcases family_descends (prefixWord ++ tailWord_139017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139028 : List Nat := [2, 4, 4, 1, 1, 1, 1, 5]
def baseStart_139028 : Nat := 118140960795 + 139028 * 2 ^ 59
def prefixEnd_139028 : Nat := 4983230072969 + 3 ^ 40 * 139028 * 2
def baseEnd_139028 : Nat := 42304111664229502821113

theorem tailTrace_139028 : CollatzResearch.WordTrace tailWord_139028 prefixEnd_139028 42304111664229502821113 := by
  unfold tailWord_139028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535383870166387468572869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3380511826888516624763825 2535383870166387468572869)
  ·
    refine ⟨475384475656197650357413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2535383870166387468572869 475384475656197650357413)
    ·
      refine ⟨89134589185537059442015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 475384475656197650357413 89134589185537059442015)
      ·
        refine ⟨133701883778305589163023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89134589185537059442015 133701883778305589163023)
        ·
          refine ⟨200552825667458383744535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133701883778305589163023 200552825667458383744535)
          ·
            refine ⟨300829238501187575616803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200552825667458383744535 300829238501187575616803)
            ·
              refine ⟨451243857751781363425205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300829238501187575616803 451243857751781363425205)
              ·
                refine ⟨42304111664229502821113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451243857751781363425205 42304111664229502821113)
                ·
                  rfl

theorem cell19_139028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_139028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139028 prefixEnd_139028 := by exact prefixLift 139028
  have htrace : WordTrace (prefixWord ++ tailWord_139028) baseStart_139028 baseEnd_139028 := by
    simpa [prefixWord, tailWord_139028, baseEnd_139028] using wordTrace_append hprefix tailTrace_139028
  have hstable : (prefixWord ++ tailWord_139028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139028).length < 2 ^ (prefixWord ++ tailWord_139028).sum := by decide
  have hdescent : baseEnd_139028 < baseStart_139028 := by decide
  rcases family_descends (prefixWord ++ tailWord_139028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139034 : List Nat := [3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_139034 : Nat := 118140960795 + 139034 * 2 ^ 59
def prefixEnd_139034 : Nat := 4983230072969 + 3 ^ 40 * 139034 * 2
def baseEnd_139034 : Nat := 42305937373223266687763

theorem tailTrace_139034 : CollatzResearch.WordTrace tailWord_139034 prefixEnd_139034 42305937373223266687763 := by
  unfold tailWord_139034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267746644577759490466039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3380657718874025307909437 1267746644577759490466039)
  ·
    refine ⟨1901619966866639235699059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1267746644577759490466039 1901619966866639235699059)
    ·
      refine ⟨2852429950299958853548589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901619966866639235699059 2852429950299958853548589)
      ·
        refine ⟨1069661231362484570080721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2852429950299958853548589 1069661231362484570080721)
        ·
          refine ⟨802245923521863427560541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069661231362484570080721 802245923521863427560541)
          ·
            refine ⟨300842221320698785335203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 802245923521863427560541 300842221320698785335203)
            ·
              refine ⟨451263331981048178002805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300842221320698785335203 451263331981048178002805)
              ·
                refine ⟨42305937373223266687763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451263331981048178002805 42305937373223266687763)
                ·
                  rfl

theorem cell19_139034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_139034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139034 prefixEnd_139034 := by exact prefixLift 139034
  have htrace : WordTrace (prefixWord ++ tailWord_139034) baseStart_139034 baseEnd_139034 := by
    simpa [prefixWord, tailWord_139034, baseEnd_139034] using wordTrace_append hprefix tailTrace_139034
  have hstable : (prefixWord ++ tailWord_139034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139034).length < 2 ^ (prefixWord ++ tailWord_139034).sum := by decide
  have hdescent : baseEnd_139034 < baseStart_139034 := by decide
  rcases family_descends (prefixWord ++ tailWord_139034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139070 : List Nat := [4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_139070 : Nat := 118140960795 + 139070 * 2 ^ 59
def prefixEnd_139070 : Nat := 4983230072969 + 3 ^ 40 * 139070 * 2
def baseEnd_139070 : Nat := 42316891627185849887665

theorem tailTrace_139070 : CollatzResearch.WordTrace tailWord_139070 prefixEnd_139070 42316891627185849887665 := by
  unfold tailWord_139070
  simp only [CollatzResearch.WordTrace]
  refine ⟨634037450772577013771833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3381533070787077406783109 634037450772577013771833)
  ·
    refine ⟨475528088079432760328875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 634037450772577013771833 475528088079432760328875)
    ·
      refine ⟨713292132119149140493313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 475528088079432760328875 713292132119149140493313)
      ·
        refine ⟨534969099089361855369985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 713292132119149140493313 534969099089361855369985)
        ·
          refine ⟨401226824317021391527489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534969099089361855369985 401226824317021391527489)
          ·
            refine ⟨300920118237766043645617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401226824317021391527489 300920118237766043645617)
            ·
              refine ⟨225690088678324532734213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300920118237766043645617 225690088678324532734213)
              ·
                refine ⟨42316891627185849887665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225690088678324532734213 42316891627185849887665)
                ·
                  rfl

theorem cell19_139070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_139070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139070 prefixEnd_139070 := by exact prefixLift 139070
  have htrace : WordTrace (prefixWord ++ tailWord_139070) baseStart_139070 baseEnd_139070 := by
    simpa [prefixWord, tailWord_139070, baseEnd_139070] using wordTrace_append hprefix tailTrace_139070
  have hstable : (prefixWord ++ tailWord_139070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139070).length < 2 ^ (prefixWord ++ tailWord_139070).sum := by decide
  have hdescent : baseEnd_139070 < baseStart_139070 := by decide
  rcases family_descends (prefixWord ++ tailWord_139070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139167 : List Nat := [1, 1, 2, 5, 3, 1, 6]
def baseStart_139167 : Nat := 118140960795 + 139167 * 2 ^ 59
def prefixEnd_139167 : Nat := 4983230072969 + 3 ^ 40 * 139167 * 2
def baseEnd_139167 : Nat := 14115469085306121910615

theorem tailTrace_139167 : CollatzResearch.WordTrace tailWord_139167 prefixEnd_139167 14115469085306121910615 := by
  unfold tailWord_139167
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075837486829201676455755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3383891657886134450970503 5075837486829201676455755)
  ·
    refine ⟨7613756230243802514683633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5075837486829201676455755 7613756230243802514683633)
    ·
      refine ⟨5710317172682851886012725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7613756230243802514683633 5710317172682851886012725)
      ·
        refine ⟨535342234939017364313693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5710317172682851886012725 535342234939017364313693)
        ·
          refine ⟨200753338102131511617635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535342234939017364313693 200753338102131511617635)
          ·
            refine ⟨301130007153197267426453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200753338102131511617635 301130007153197267426453)
            ·
              refine ⟨14115469085306121910615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 301130007153197267426453 14115469085306121910615)
              ·
                rfl

theorem cell19_139167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_139167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139167 prefixEnd_139167 := by exact prefixLift 139167
  have htrace : WordTrace (prefixWord ++ tailWord_139167) baseStart_139167 baseEnd_139167 := by
    simpa [prefixWord, tailWord_139167, baseEnd_139167] using wordTrace_append hprefix tailTrace_139167
  have hstable : (prefixWord ++ tailWord_139167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139167).length < 2 ^ (prefixWord ++ tailWord_139167).sum := by decide
  have hdescent : baseEnd_139167 < baseStart_139167 := by decide
  rcases family_descends (prefixWord ++ tailWord_139167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139277 : List Nat := [1, 7, 1, 2, 1, 7]
def baseStart_139277 : Nat := 118140960795 + 139277 * 2 ^ 59
def prefixEnd_139277 : Nat := 4983230072969 + 3 ^ 40 * 139277 * 2
def baseEnd_139277 : Nat := 4708875398607855920789

theorem tailTrace_139277 : CollatzResearch.WordTrace tailWord_139277 prefixEnd_139277 4708875398607855920789 := by
  unfold tailWord_139277
  simp only [CollatzResearch.WordTrace]
  refine ⟨5079849516430690462960085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3386566344287126975306723 5079849516430690462960085)
  ·
    refine ⟨119058973041344307725627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5079849516430690462960085 119058973041344307725627)
    ·
      refine ⟨178588459562016461588441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119058973041344307725627 178588459562016461588441)
      ·
        refine ⟨133941344671512346191331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178588459562016461588441 133941344671512346191331)
        ·
          refine ⟨200912017007268519286997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133941344671512346191331 200912017007268519286997)
          ·
            refine ⟨4708875398607855920789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200912017007268519286997 4708875398607855920789)
            ·
              rfl

theorem cell19_139277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_139277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139277 prefixEnd_139277 := by exact prefixLift 139277
  have htrace : WordTrace (prefixWord ++ tailWord_139277) baseStart_139277 baseEnd_139277 := by
    simpa [prefixWord, tailWord_139277, baseEnd_139277] using wordTrace_append hprefix tailTrace_139277
  have hstable : (prefixWord ++ tailWord_139277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139277).length < 2 ^ (prefixWord ++ tailWord_139277).sum := by decide
  have hdescent : baseEnd_139277 < baseStart_139277 := by decide
  rcases family_descends (prefixWord ++ tailWord_139277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139376 : List Nat := [2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_139376 : Nat := 118140960795 + 139376 * 2 ^ 59
def prefixEnd_139376 : Nat := 4983230072969 + 3 ^ 40 * 139376 * 2
def baseEnd_139376 : Nat := 42410002785867807086831

theorem tailTrace_139376 : CollatzResearch.WordTrace tailWord_139376 prefixEnd_139376 42410002785867807086831 := by
  unfold tailWord_139376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541730171536015185406991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3388973562048020247209321 2541730171536015185406991)
  ·
    refine ⟨3812595257304022778110487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2541730171536015185406991 3812595257304022778110487)
    ·
      refine ⟨5718892885956034167165731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3812595257304022778110487 5718892885956034167165731)
      ·
        refine ⟨8578339328934051250748597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5718892885956034167165731 8578339328934051250748597)
        ·
          refine ⟨804219312087567304757681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8578339328934051250748597 804219312087567304757681)
          ·
            refine ⟨603164484065675478568261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804219312087567304757681 603164484065675478568261)
            ·
              refine ⟨113093340762314152231549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 603164484065675478568261 113093340762314152231549)
              ·
                refine ⟨42410002785867807086831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113093340762314152231549 42410002785867807086831)
                ·
                  rfl

theorem cell19_139376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_139376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139376 prefixEnd_139376 := by exact prefixLift 139376
  have htrace : WordTrace (prefixWord ++ tailWord_139376) baseStart_139376 baseEnd_139376 := by
    simpa [prefixWord, tailWord_139376, baseEnd_139376] using wordTrace_append hprefix tailTrace_139376
  have hstable : (prefixWord ++ tailWord_139376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139376).length < 2 ^ (prefixWord ++ tailWord_139376).sum := by decide
  have hdescent : baseEnd_139376 < baseStart_139376 := by decide
  rcases family_descends (prefixWord ++ tailWord_139376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139393 : List Nat := [1, 2, 4, 2, 4, 1, 5]
def baseStart_139393 : Nat := 118140960795 + 139393 * 2 ^ 59
def prefixEnd_139393 : Nat := 4983230072969 + 3 ^ 40 * 139393 * 2
def baseEnd_139393 : Nat := 14138391876005601569669

theorem tailTrace_139393 : CollatzResearch.WordTrace tailWord_139393 prefixEnd_139393 14138391876005601569669 := by
  unfold tailWord_139393
  simp only [CollatzResearch.WordTrace]
  refine ⟨5084080384010442274182833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3389386922673628182788555 5084080384010442274182833)
  ·
    refine ⟨3813060288007831705637125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5084080384010442274182833 3813060288007831705637125)
    ·
      refine ⟨714948804001468444806961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3813060288007831705637125 714948804001468444806961)
      ·
        refine ⟨536211603001101333605221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714948804001468444806961 536211603001101333605221)
        ·
          refine ⟨100539675562706500050979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 536211603001101333605221 100539675562706500050979)
          ·
            refine ⟨150809513344059750076469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100539675562706500050979 150809513344059750076469)
            ·
              refine ⟨14138391876005601569669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150809513344059750076469 14138391876005601569669)
              ·
                rfl

theorem cell19_139393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_139393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139393 prefixEnd_139393 := by exact prefixLift 139393
  have htrace : WordTrace (prefixWord ++ tailWord_139393) baseStart_139393 baseEnd_139393 := by
    simpa [prefixWord, tailWord_139393, baseEnd_139393] using wordTrace_append hprefix tailTrace_139393
  have hstable : (prefixWord ++ tailWord_139393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139393).length < 2 ^ (prefixWord ++ tailWord_139393).sum := by decide
  have hdescent : baseEnd_139393 < baseStart_139393 := by decide
  rcases family_descends (prefixWord ++ tailWord_139393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139397 : List Nat := [1, 3, 1, 1, 5, 1, 7]
def baseStart_139397 : Nat := 118140960795 + 139397 * 2 ^ 59
def prefixEnd_139397 : Nat := 4983230072969 + 3 ^ 40 * 139397 * 2
def baseEnd_139397 : Nat := 14138797589115326873369

theorem tailTrace_139397 : CollatzResearch.WordTrace tailWord_139397 prefixEnd_139397 14138797589115326873369 := by
  unfold tailWord_139397
  simp only [CollatzResearch.WordTrace]
  refine ⟨5084226275995950957328445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3389484183997300638218963 5084226275995950957328445)
  ·
    refine ⟨1906584853498481608998167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5084226275995950957328445 1906584853498481608998167)
    ·
      refine ⟨2859877280247722413497251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906584853498481608998167 2859877280247722413497251)
      ·
        refine ⟨4289815920371583620245877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2859877280247722413497251 4289815920371583620245877)
        ·
          refine ⟨402170242534835964398051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4289815920371583620245877 402170242534835964398051)
          ·
            refine ⟨603255363802253946597077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402170242534835964398051 603255363802253946597077)
            ·
              refine ⟨14138797589115326873369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 603255363802253946597077 14138797589115326873369)
              ·
                rfl

theorem cell19_139397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_139397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139397 prefixEnd_139397 := by exact prefixLift 139397
  have htrace : WordTrace (prefixWord ++ tailWord_139397) baseStart_139397 baseEnd_139397 := by
    simpa [prefixWord, tailWord_139397, baseEnd_139397] using wordTrace_append hprefix tailTrace_139397
  have hstable : (prefixWord ++ tailWord_139397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139397).length < 2 ^ (prefixWord ++ tailWord_139397).sum := by decide
  have hdescent : baseEnd_139397 < baseStart_139397 := by decide
  rcases family_descends (prefixWord ++ tailWord_139397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139452 : List Nat := [2, 2, 2, 3, 4, 6]
def baseStart_139452 : Nat := 118140960795 + 139452 * 2 ^ 59
def prefixEnd_139452 : Nat := 4983230072969 + 3 ^ 40 * 139452 * 2
def baseEnd_139452 : Nat := 4714792048124683266415

theorem tailTrace_139452 : CollatzResearch.WordTrace tailWord_139452 prefixEnd_139452 4714792048124683266415 := by
  unfold tailWord_139452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543116145398347675290305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3390821527197796900387073 2543116145398347675290305)
  ·
    refine ⟨1907337109048760756467729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2543116145398347675290305 1907337109048760756467729)
    ·
      refine ⟨1430502831786570567350797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1907337109048760756467729 1430502831786570567350797)
      ·
        refine ⟨536438561919963962756549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1430502831786570567350797 536438561919963962756549)
        ·
          refine ⟨100582230359993243016853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 536438561919963962756549 100582230359993243016853)
          ·
            refine ⟨4714792048124683266415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100582230359993243016853 4714792048124683266415)
            ·
              rfl

theorem cell19_139452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_139452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139452 prefixEnd_139452 := by exact prefixLift 139452
  have htrace : WordTrace (prefixWord ++ tailWord_139452) baseStart_139452 baseEnd_139452 := by
    simpa [prefixWord, tailWord_139452, baseEnd_139452] using wordTrace_append hprefix tailTrace_139452
  have hstable : (prefixWord ++ tailWord_139452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139452).length < 2 ^ (prefixWord ++ tailWord_139452).sum := by decide
  have hdescent : baseEnd_139452 < baseStart_139452 := by decide
  rcases family_descends (prefixWord ++ tailWord_139452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139454 : List Nat := [4, 2, 1, 1, 11]
def baseStart_139454 : Nat := 118140960795 + 139454 * 2 ^ 59
def prefixEnd_139454 : Nat := 4983230072969 + 3 ^ 40 * 139454 * 2
def baseEnd_139454 : Nat := 1571619888992101383455

theorem tailTrace_139454 : CollatzResearch.WordTrace tailWord_139454 prefixEnd_139454 1571619888992101383455 := by
  unfold tailWord_139454
  simp only [CollatzResearch.WordTrace]
  refine ⟨635788154598681211519177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3390870157859633128102277 635788154598681211519177)
  ·
    refine ⟨476841115949010908639383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 635788154598681211519177 476841115949010908639383)
    ·
      refine ⟨715261673923516362959075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476841115949010908639383 715261673923516362959075)
      ·
        refine ⟨1072892510885274544438613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715261673923516362959075 1072892510885274544438613)
        ·
          refine ⟨1571619888992101383455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1072892510885274544438613 1571619888992101383455)
          ·
            rfl

theorem cell19_139454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 11].length) (baseStart_139454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139454 prefixEnd_139454 := by exact prefixLift 139454
  have htrace : WordTrace (prefixWord ++ tailWord_139454) baseStart_139454 baseEnd_139454 := by
    simpa [prefixWord, tailWord_139454, baseEnd_139454] using wordTrace_append hprefix tailTrace_139454
  have hstable : (prefixWord ++ tailWord_139454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139454).length < 2 ^ (prefixWord ++ tailWord_139454).sum := by decide
  have hdescent : baseEnd_139454 < baseStart_139454 := by decide
  rcases family_descends (prefixWord ++ tailWord_139454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139473 : List Nat := [1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_139473 : Nat := 118140960795 + 139473 * 2 ^ 59
def prefixEnd_139473 : Nat := 4983230072969 + 3 ^ 40 * 139473 * 2
def baseEnd_139473 : Nat := 42439518414600322931011

theorem tailTrace_139473 : CollatzResearch.WordTrace tailWord_139473 prefixEnd_139473 42439518414600322931011 := by
  unfold tailWord_139473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086998223720615937095073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3391332149147077291396715 5086998223720615937095073)
  ·
    refine ⟨3815248667790461952821305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5086998223720615937095073 3815248667790461952821305)
    ·
      refine ⟨2861436500842846464615979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3815248667790461952821305 2861436500842846464615979)
      ·
        refine ⟨4292154751264269696923969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861436500842846464615979 4292154751264269696923969)
        ·
          refine ⟨3219116063448202272692977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4292154751264269696923969 3219116063448202272692977)
          ·
            refine ⟨2414337047586151704519733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3219116063448202272692977 2414337047586151704519733)
            ·
              refine ⟨226344098211201722298725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2414337047586151704519733 226344098211201722298725)
              ·
                refine ⟨42439518414600322931011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226344098211201722298725 42439518414600322931011)
                ·
                  rfl

theorem cell19_139473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_139473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139473 prefixEnd_139473 := by exact prefixLift 139473
  have htrace : WordTrace (prefixWord ++ tailWord_139473) baseStart_139473 baseEnd_139473 := by
    simpa [prefixWord, tailWord_139473, baseEnd_139473] using wordTrace_append hprefix tailTrace_139473
  have hstable : (prefixWord ++ tailWord_139473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139473).length < 2 ^ (prefixWord ++ tailWord_139473).sum := by decide
  have hdescent : baseEnd_139473 < baseStart_139473 := by decide
  rcases family_descends (prefixWord ++ tailWord_139473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139638 : List Nat := [5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_139638 : Nat := 118140960795 + 139638 * 2 ^ 59
def prefixEnd_139638 : Nat := 4983230072969 + 3 ^ 40 * 139638 * 2
def baseEnd_139638 : Nat := 42489725411928829263895

theorem tailTrace_139638 : CollatzResearch.WordTrace tailWord_139638 prefixEnd_139638 42489725411928829263895 := by
  unfold tailWord_139638
  simp only [CollatzResearch.WordTrace]
  refine ⟨318313516757678069803223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3395344178748566077901045 318313516757678069803223)
  ·
    refine ⟨477470275136517104704835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318313516757678069803223 477470275136517104704835)
    ·
      refine ⟨716205412704775657057253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477470275136517104704835 716205412704775657057253)
      ·
        refine ⟨134288514882145435698235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 716205412704775657057253 134288514882145435698235)
        ·
          refine ⟨201432772323218153547353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134288514882145435698235 201432772323218153547353)
          ·
            refine ⟨151074579242413615160515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201432772323218153547353 151074579242413615160515)
            ·
              refine ⟨226611868863620422740773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151074579242413615160515 226611868863620422740773)
              ·
                refine ⟨42489725411928829263895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226611868863620422740773 42489725411928829263895)
                ·
                  rfl

theorem cell19_139638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_139638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139638 prefixEnd_139638 := by exact prefixLift 139638
  have htrace : WordTrace (prefixWord ++ tailWord_139638) baseStart_139638 baseEnd_139638 := by
    simpa [prefixWord, tailWord_139638, baseEnd_139638] using wordTrace_append hprefix tailTrace_139638
  have hstable : (prefixWord ++ tailWord_139638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139638).length < 2 ^ (prefixWord ++ tailWord_139638).sum := by decide
  have hdescent : baseEnd_139638 < baseStart_139638 := by decide
  rcases family_descends (prefixWord ++ tailWord_139638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139682 : List Nat := [3, 3, 1, 2, 1, 1, 8]
def baseStart_139682 : Nat := 118140960795 + 139682 * 2 ^ 59
def prefixEnd_139682 : Nat := 4983230072969 + 3 ^ 40 * 139682 * 2
def baseEnd_139682 : Nat := 14167704648183254761999

theorem tailTrace_139682 : CollatzResearch.WordTrace tailWord_139682 prefixEnd_139682 14167704648183254761999 := by
  unfold tailWord_139682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273655269990861157863325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3396414053308963087635533 1273655269990861157863325)
  ·
    refine ⟨477620726246572934198747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1273655269990861157863325 477620726246572934198747)
    ·
      refine ⟨716431089369859401298121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477620726246572934198747 716431089369859401298121)
      ·
        refine ⟨537323317027394550973591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 716431089369859401298121 537323317027394550973591)
        ·
          refine ⟨805984975541091826460387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537323317027394550973591 805984975541091826460387)
          ·
            refine ⟨1208977463311637739690581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805984975541091826460387 1208977463311637739690581)
            ·
              refine ⟨14167704648183254761999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1208977463311637739690581 14167704648183254761999)
              ·
                rfl

theorem cell19_139682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_139682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139682 prefixEnd_139682 := by exact prefixLift 139682
  have htrace : WordTrace (prefixWord ++ tailWord_139682) baseStart_139682 baseEnd_139682 := by
    simpa [prefixWord, tailWord_139682, baseEnd_139682] using wordTrace_append hprefix tailTrace_139682
  have hstable : (prefixWord ++ tailWord_139682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139682).length < 2 ^ (prefixWord ++ tailWord_139682).sum := by decide
  have hdescent : baseEnd_139682 < baseStart_139682 := by decide
  rcases family_descends (prefixWord ++ tailWord_139682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139720 : List Nat := [2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_139720 : Nat := 118140960795 + 139720 * 2 ^ 59
def prefixEnd_139720 : Nat := 4983230072969 + 3 ^ 40 * 139720 * 2
def baseEnd_139720 : Nat := 42514676768176935441449

theorem tailTrace_139720 : CollatzResearch.WordTrace tailWord_139720 prefixEnd_139720 42514676768176935441449 := by
  unfold tailWord_139720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548003526912888560668307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3397338035883851414224409 2548003526912888560668307)
  ·
    refine ⟨3822005290369332841002461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2548003526912888560668307 3822005290369332841002461)
    ·
      refine ⟨1433251983888499815375923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3822005290369332841002461 1433251983888499815375923)
      ·
        refine ⟨2149877975832749723063885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433251983888499815375923 2149877975832749723063885)
        ·
          refine ⟨806204240937281146148957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2149877975832749723063885 806204240937281146148957)
          ·
            refine ⟨302326590351480429805859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806204240937281146148957 302326590351480429805859)
            ·
              refine ⟨453489885527220644708789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302326590351480429805859 453489885527220644708789)
              ·
                refine ⟨42514676768176935441449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 453489885527220644708789 42514676768176935441449)
                ·
                  rfl

theorem cell19_139720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_139720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139720 prefixEnd_139720 := by exact prefixLift 139720
  have htrace : WordTrace (prefixWord ++ tailWord_139720) baseStart_139720 baseEnd_139720 := by
    simpa [prefixWord, tailWord_139720, baseEnd_139720] using wordTrace_append hprefix tailTrace_139720
  have hstable : (prefixWord ++ tailWord_139720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139720).length < 2 ^ (prefixWord ++ tailWord_139720).sum := by decide
  have hdescent : baseEnd_139720 < baseStart_139720 := by decide
  rcases family_descends (prefixWord ++ tailWord_139720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139758 : List Nat := [4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_139758 : Nat := 118140960795 + 139758 * 2 ^ 59
def prefixEnd_139758 : Nat := 4983230072969 + 3 ^ 40 * 139758 * 2
def baseEnd_139758 : Nat := 42526239591804106596901

theorem tailTrace_139758 : CollatzResearch.WordTrace tailWord_139758 prefixEnd_139758 42526239591804106596901 := by
  unfold tailWord_139758
  simp only [CollatzResearch.WordTrace]
  refine ⟨637174128461013701402491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3398262018458739740813285 637174128461013701402491)
  ·
    refine ⟨955761192691520552103737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 637174128461013701402491 955761192691520552103737)
    ·
      refine ⟨716820894518640414077803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 955761192691520552103737 716820894518640414077803)
      ·
        refine ⟨1075231341777960621116705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716820894518640414077803 1075231341777960621116705)
        ·
          refine ⟨806423506333470465837529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075231341777960621116705 806423506333470465837529)
          ·
            refine ⟨604817629750102849378147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806423506333470465837529 604817629750102849378147)
            ·
              refine ⟨907226444625154274067221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604817629750102849378147 907226444625154274067221)
              ·
                refine ⟨42526239591804106596901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 907226444625154274067221 42526239591804106596901)
                ·
                  rfl

theorem cell19_139758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_139758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139758 prefixEnd_139758 := by exact prefixLift 139758
  have htrace : WordTrace (prefixWord ++ tailWord_139758) baseStart_139758 baseEnd_139758 := by
    simpa [prefixWord, tailWord_139758, baseEnd_139758] using wordTrace_append hprefix tailTrace_139758
  have hstable : (prefixWord ++ tailWord_139758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139758).length < 2 ^ (prefixWord ++ tailWord_139758).sum := by decide
  have hdescent : baseEnd_139758 < baseStart_139758 := by decide
  rcases family_descends (prefixWord ++ tailWord_139758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139777 : List Nat := [1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_139777 : Nat := 118140960795 + 139777 * 2 ^ 59
def prefixEnd_139777 : Nat := 4983230072969 + 3 ^ 40 * 139777 * 2
def baseEnd_139777 : Nat := 42532021003617692174627

theorem tailTrace_139777 : CollatzResearch.WordTrace tailWord_139777 prefixEnd_139777 42532021003617692174627 := by
  unfold tailWord_139777
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098086014619275856161585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3398724009746183904107723 5098086014619275856161585)
  ·
    refine ⟨3823564510964456892121189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5098086014619275856161585 3823564510964456892121189)
    ·
      refine ⟨716918345805835667272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3823564510964456892121189 716918345805835667272723)
      ·
        refine ⟨1075377518708753500909085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716918345805835667272723 1075377518708753500909085)
        ·
          refine ⟨403266569515782562840907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1075377518708753500909085 403266569515782562840907)
          ·
            refine ⟨604899854273673844261361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403266569515782562840907 604899854273673844261361)
            ·
              refine ⟨453674890705255383196021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604899854273673844261361 453674890705255383196021)
              ·
                refine ⟨42532021003617692174627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 453674890705255383196021 42532021003617692174627)
                ·
                  rfl

theorem cell19_139777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_139777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139777 prefixEnd_139777 := by exact prefixLift 139777
  have htrace : WordTrace (prefixWord ++ tailWord_139777) baseStart_139777 baseEnd_139777 := by
    simpa [prefixWord, tailWord_139777, baseEnd_139777] using wordTrace_append hprefix tailTrace_139777
  have hstable : (prefixWord ++ tailWord_139777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139777).length < 2 ^ (prefixWord ++ tailWord_139777).sum := by decide
  have hdescent : baseEnd_139777 < baseStart_139777 := by decide
  rcases family_descends (prefixWord ++ tailWord_139777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139779 : List Nat := [1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_139779 : Nat := 118140960795 + 139779 * 2 ^ 59
def prefixEnd_139779 : Nat := 4983230072969 + 3 ^ 40 * 139779 * 2
def baseEnd_139779 : Nat := 42532629573282280130177

theorem tailTrace_139779 : CollatzResearch.WordTrace tailWord_139779 prefixEnd_139779 42532629573282280130177 := by
  unfold tailWord_139779
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098158960612030197734391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3398772640408020131822927 5098158960612030197734391)
  ·
    refine ⟨7647238440918045296601587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5098158960612030197734391 7647238440918045296601587)
    ·
      refine ⟨11470857661377067944902381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647238440918045296601587 11470857661377067944902381)
      ·
        refine ⟨4301571623016400479338393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11470857661377067944902381 4301571623016400479338393)
        ·
          refine ⟨3226178717262300359503795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4301571623016400479338393 3226178717262300359503795)
          ·
            refine ⟨4839268075893450539255693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226178717262300359503795 4839268075893450539255693)
            ·
              refine ⟨1814725528460043952220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4839268075893450539255693 1814725528460043952220885)
              ·
                refine ⟨42532629573282280130177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1814725528460043952220885 42532629573282280130177)
                ·
                  rfl

theorem cell19_139779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_139779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139779 prefixEnd_139779 := by exact prefixLift 139779
  have htrace : WordTrace (prefixWord ++ tailWord_139779) baseStart_139779 baseEnd_139779 := by
    simpa [prefixWord, tailWord_139779, baseEnd_139779] using wordTrace_append hprefix tailTrace_139779
  have hstable : (prefixWord ++ tailWord_139779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139779).length < 2 ^ (prefixWord ++ tailWord_139779).sum := by decide
  have hdescent : baseEnd_139779 < baseStart_139779 := by decide
  rcases family_descends (prefixWord ++ tailWord_139779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139828 : List Nat := [2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_139828 : Nat := 118140960795 + 139828 * 2 ^ 59
def prefixEnd_139828 : Nat := 4983230072969 + 3 ^ 40 * 139828 * 2
def baseEnd_139828 : Nat := 42547539530064685041155

theorem tailTrace_139828 : CollatzResearch.WordTrace tailWord_139828 prefixEnd_139828 42547539530064685041155 := by
  unfold tailWord_139828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549973068717255783134069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3399964091623007710845425 2549973068717255783134069)
  ·
    refine ⟨239059975192242729668819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2549973068717255783134069 239059975192242729668819)
    ·
      refine ⟨358589962788364094503229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239059975192242729668819 358589962788364094503229)
      ·
        refine ⟨134471236045636535438711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358589962788364094503229 134471236045636535438711)
        ·
          refine ⟨201706854068454803158067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134471236045636535438711 201706854068454803158067)
          ·
            refine ⟨302560281102682204737101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201706854068454803158067 302560281102682204737101)
            ·
              refine ⟨113460105413505826776413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302560281102682204737101 113460105413505826776413)
              ·
                refine ⟨42547539530064685041155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113460105413505826776413 42547539530064685041155)
                ·
                  rfl

theorem cell19_139828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_139828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139828 prefixEnd_139828 := by exact prefixLift 139828
  have htrace : WordTrace (prefixWord ++ tailWord_139828) baseStart_139828 baseEnd_139828 := by
    simpa [prefixWord, tailWord_139828, baseEnd_139828] using wordTrace_append hprefix tailTrace_139828
  have hstable : (prefixWord ++ tailWord_139828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139828).length < 2 ^ (prefixWord ++ tailWord_139828).sum := by decide
  have hdescent : baseEnd_139828 < baseStart_139828 := by decide
  rcases family_descends (prefixWord ++ tailWord_139828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139830 : List Nat := [5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_139830 : Nat := 118140960795 + 139830 * 2 ^ 59
def prefixEnd_139830 : Nat := 4983230072969 + 3 ^ 40 * 139830 * 2
def baseEnd_139830 : Nat := 42548148099729272996705

theorem tailTrace_139830 : CollatzResearch.WordTrace tailWord_139830 prefixEnd_139830 42548148099729272996705 := by
  unfold tailWord_139830
  simp only [CollatzResearch.WordTrace]
  refine ⟨318751192714204119240059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3400012722284843938560629 318751192714204119240059)
  ·
    refine ⟨478126789071306178860089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318751192714204119240059 478126789071306178860089)
    ·
      refine ⟨358595091803479634145067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 478126789071306178860089 358595091803479634145067)
      ·
        refine ⟨537892637705219451217601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358595091803479634145067 537892637705219451217601)
        ·
          refine ⟨403419478278914588413201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537892637705219451217601 403419478278914588413201)
          ·
            refine ⟨302564608709185941309901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403419478278914588413201 302564608709185941309901)
            ·
              refine ⟨113461728265944727991213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302564608709185941309901 113461728265944727991213)
              ·
                refine ⟨42548148099729272996705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113461728265944727991213 42548148099729272996705)
                ·
                  rfl

theorem cell19_139830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_139830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_139830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_139830 prefixEnd_139830 := by exact prefixLift 139830
  have htrace : WordTrace (prefixWord ++ tailWord_139830) baseStart_139830 baseEnd_139830 := by
    simpa [prefixWord, tailWord_139830, baseEnd_139830] using wordTrace_append hprefix tailTrace_139830
  have hstable : (prefixWord ++ tailWord_139830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139830).length < 2 ^ (prefixWord ++ tailWord_139830).sum := by decide
  have hdescent : baseEnd_139830 < baseStart_139830 := by decide
  rcases family_descends (prefixWord ++ tailWord_139830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140003 : List Nat := [1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_140003 : Nat := 118140960795 + 140003 * 2 ^ 59
def prefixEnd_140003 : Nat := 4983230072969 + 3 ^ 40 * 140003 * 2
def baseEnd_140003 : Nat := 42600789375716131151789

theorem tailTrace_140003 : CollatzResearch.WordTrace tailWord_140003 prefixEnd_140003 42600789375716131151789 := by
  unfold tailWord_140003
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106328911800516453888663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3404219274533677635925775 5106328911800516453888663)
  ·
    refine ⟨7659493367700774680832995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5106328911800516453888663 7659493367700774680832995)
    ·
      refine ⟨11489240051551162021249493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7659493367700774680832995 11489240051551162021249493)
      ·
        refine ⟨269279063708230359873035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11489240051551162021249493 269279063708230359873035)
        ·
          refine ⟨403918595562345539809553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269279063708230359873035 403918595562345539809553)
          ·
            refine ⟨302938946671759154857165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403918595562345539809553 302938946671759154857165)
            ·
              refine ⟨113602105001909683071437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302938946671759154857165 113602105001909683071437)
              ·
                refine ⟨42600789375716131151789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113602105001909683071437 42600789375716131151789)
                ·
                  rfl

theorem cell19_140003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_140003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140003 prefixEnd_140003 := by exact prefixLift 140003
  have htrace : WordTrace (prefixWord ++ tailWord_140003) baseStart_140003 baseEnd_140003 := by
    simpa [prefixWord, tailWord_140003, baseEnd_140003] using wordTrace_append hprefix tailTrace_140003
  have hstable : (prefixWord ++ tailWord_140003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140003).length < 2 ^ (prefixWord ++ tailWord_140003).sum := by decide
  have hdescent : baseEnd_140003 < baseStart_140003 := by decide
  rcases family_descends (prefixWord ++ tailWord_140003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140020 : List Nat := [2, 6, 1, 1, 2, 1, 6]
def baseStart_140020 : Nat := 118140960795 + 140020 * 2 ^ 59
def prefixEnd_140020 : Nat := 4983230072969 + 3 ^ 40 * 140020 * 2
def baseEnd_140020 : Nat := 14201987405955042924655

theorem tailTrace_140020 : CollatzResearch.WordTrace tailWord_140020 prefixEnd_140020 14201987405955042924655 := by
  unfold tailWord_140020
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553474476369464178628757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3404632635159285571505009 2553474476369464178628757)
  ·
    refine ⟨119694116079818633373223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2553474476369464178628757 119694116079818633373223)
    ·
      refine ⟨179541174119727950059835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119694116079818633373223 179541174119727950059835)
      ·
        refine ⟨269311761179591925089753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179541174119727950059835 269311761179591925089753)
        ·
          refine ⟨201983820884693943817315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269311761179591925089753 201983820884693943817315)
          ·
            refine ⟨302975731327040915725973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201983820884693943817315 302975731327040915725973)
            ·
              refine ⟨14201987405955042924655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 302975731327040915725973 14201987405955042924655)
              ·
                rfl

theorem cell19_140020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_140020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140020 prefixEnd_140020 := by exact prefixLift 140020
  have htrace : WordTrace (prefixWord ++ tailWord_140020) baseStart_140020 baseEnd_140020 := by
    simpa [prefixWord, tailWord_140020, baseEnd_140020] using wordTrace_append hprefix tailTrace_140020
  have hstable : (prefixWord ++ tailWord_140020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140020).length < 2 ^ (prefixWord ++ tailWord_140020).sum := by decide
  have hdescent : baseEnd_140020 < baseStart_140020 := by decide
  rcases family_descends (prefixWord ++ tailWord_140020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140060 : List Nat := [2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_140060 : Nat := 118140960795 + 140060 * 2 ^ 59
def prefixEnd_140060 : Nat := 4983230072969 + 3 ^ 40 * 140060 * 2
def baseEnd_140060 : Nat := 42618133611156887884967

theorem tailTrace_140060 : CollatzResearch.WordTrace tailWord_140060 prefixEnd_140060 42618133611156887884967 := by
  unfold tailWord_140060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554203936297007594356817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3405605248396010125809089 2554203936297007594356817)
  ·
    refine ⟨1915652952222755695767613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2554203936297007594356817 1915652952222755695767613)
    ·
      refine ⟨718369857083533385912855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1915652952222755695767613 718369857083533385912855)
      ·
        refine ⟨1077554785625300078869283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718369857083533385912855 1077554785625300078869283)
        ·
          refine ⟨1616332178437950118303925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077554785625300078869283 1616332178437950118303925)
          ·
            refine ⟨151531141728557823590993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1616332178437950118303925 151531141728557823590993)
            ·
              refine ⟨113648356296418367693245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151531141728557823590993 113648356296418367693245)
              ·
                refine ⟨42618133611156887884967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113648356296418367693245 42618133611156887884967)
                ·
                  rfl

theorem cell19_140060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_140060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140060 prefixEnd_140060 := by exact prefixLift 140060
  have htrace : WordTrace (prefixWord ++ tailWord_140060) baseStart_140060 baseEnd_140060 := by
    simpa [prefixWord, tailWord_140060, baseEnd_140060] using wordTrace_append hprefix tailTrace_140060
  have hstable : (prefixWord ++ tailWord_140060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140060).length < 2 ^ (prefixWord ++ tailWord_140060).sum := by decide
  have hdescent : baseEnd_140060 < baseStart_140060 := by decide
  rcases family_descends (prefixWord ++ tailWord_140060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140077 : List Nat := [1, 5, 3, 2, 1, 2, 5]
def baseStart_140077 : Nat := 118140960795 + 140077 * 2 ^ 59
def prefixEnd_140077 : Nat := 4983230072969 + 3 ^ 40 * 140077 * 2
def baseEnd_140077 : Nat := 14207768817768628502381

theorem tailTrace_140077 : CollatzResearch.WordTrace tailWord_140077 prefixEnd_140077 14207768817768628502381 := by
  unfold tailWord_140077
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109027913532427092082485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406018609021618061388323 5109027913532427092082485)
  ·
    refine ⟨478971366893665039882733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5109027913532427092082485 478971366893665039882733)
    ·
      refine ⟨179614262585124389956025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 478971366893665039882733 179614262585124389956025)
      ·
        refine ⟨134710696938843292467019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179614262585124389956025 134710696938843292467019)
        ·
          refine ⟨202066045408264938700529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134710696938843292467019 202066045408264938700529)
          ·
            refine ⟨151549534056198704025397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202066045408264938700529 151549534056198704025397)
            ·
              refine ⟨14207768817768628502381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151549534056198704025397 14207768817768628502381)
              ·
                rfl

theorem cell19_140077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_140077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140077 prefixEnd_140077 := by exact prefixLift 140077
  have htrace : WordTrace (prefixWord ++ tailWord_140077) baseStart_140077 baseEnd_140077 := by
    simpa [prefixWord, tailWord_140077, baseEnd_140077] using wordTrace_append hprefix tailTrace_140077
  have hstable : (prefixWord ++ tailWord_140077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140077).length < 2 ^ (prefixWord ++ tailWord_140077).sum := by decide
  have hdescent : baseEnd_140077 < baseStart_140077 := by decide
  rcases family_descends (prefixWord ++ tailWord_140077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140083 : List Nat := [1, 1, 1, 2, 6, 1, 7]
def baseStart_140083 : Nat := 118140960795 + 140083 * 2 ^ 59
def prefixEnd_140083 : Nat := 4983230072969 + 3 ^ 40 * 140083 * 2
def baseEnd_140083 : Nat := 14208377387433216457931

theorem tailTrace_140083 : CollatzResearch.WordTrace tailWord_140083 prefixEnd_140083 14208377387433216457931 := by
  unfold tailWord_140083
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109246751510690116800903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406164501007126744533935 5109246751510690116800903)
  ·
    refine ⟨7663870127266035175201355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5109246751510690116800903 7663870127266035175201355)
    ·
      refine ⟨11495805190899052762802033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7663870127266035175201355 11495805190899052762802033)
      ·
        refine ⟨8621853893174289572101525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11495805190899052762802033 8621853893174289572101525)
        ·
          refine ⟨404149401242544823692259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8621853893174289572101525 404149401242544823692259)
          ·
            refine ⟨606224101863817235538389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404149401242544823692259 606224101863817235538389)
            ·
              refine ⟨14208377387433216457931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 606224101863817235538389 14208377387433216457931)
              ·
                rfl

theorem cell19_140083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_140083 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140083 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140083 prefixEnd_140083 := by exact prefixLift 140083
  have htrace : WordTrace (prefixWord ++ tailWord_140083) baseStart_140083 baseEnd_140083 := by
    simpa [prefixWord, tailWord_140083, baseEnd_140083] using wordTrace_append hprefix tailTrace_140083
  have hstable : (prefixWord ++ tailWord_140083).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140083).length < 2 ^ (prefixWord ++ tailWord_140083).sum := by decide
  have hdescent : baseEnd_140083 < baseStart_140083 := by decide
  rcases family_descends (prefixWord ++ tailWord_140083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140121 : List Nat := [1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_140121 : Nat := 118140960795 + 140121 * 2 ^ 59
def prefixEnd_140121 : Nat := 4983230072969 + 3 ^ 40 * 140121 * 2
def baseEnd_140121 : Nat := 42636694985926820529245

theorem tailTrace_140121 : CollatzResearch.WordTrace tailWord_140121 prefixEnd_140121 42636694985926820529245 := by
  unfold tailWord_140121
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110632725373022606684217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3407088483582015071122811 5110632725373022606684217)
  ·
    refine ⟨3832974544029766955013163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5110632725373022606684217 3832974544029766955013163)
    ·
      refine ⟨5749461816044650432519745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832974544029766955013163 5749461816044650432519745)
      ·
        refine ⟨4312096362033487824389809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5749461816044650432519745 4312096362033487824389809)
        ·
          refine ⟨3234072271525115868292357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4312096362033487824389809 3234072271525115868292357)
          ·
            refine ⟨606388550910959225304817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3234072271525115868292357 606388550910959225304817)
            ·
              refine ⟨454791413183219418978613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606388550910959225304817 454791413183219418978613)
              ·
                refine ⟨42636694985926820529245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 454791413183219418978613 42636694985926820529245)
                ·
                  rfl

theorem cell19_140121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_140121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140121 prefixEnd_140121 := by exact prefixLift 140121
  have htrace : WordTrace (prefixWord ++ tailWord_140121) baseStart_140121 baseEnd_140121 := by
    simpa [prefixWord, tailWord_140121, baseEnd_140121] using wordTrace_append hprefix tailTrace_140121
  have hstable : (prefixWord ++ tailWord_140121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140121).length < 2 ^ (prefixWord ++ tailWord_140121).sum := by decide
  have hdescent : baseEnd_140121 < baseStart_140121 := by decide
  rcases family_descends (prefixWord ++ tailWord_140121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140159 : List Nat := [1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_140159 : Nat := 118140960795 + 140159 * 2 ^ 59
def prefixEnd_140159 : Nat := 4983230072969 + 3 ^ 40 * 140159 * 2
def baseEnd_140159 : Nat := 42648257809553991684697

theorem tailTrace_140159 : CollatzResearch.WordTrace tailWord_140159 prefixEnd_140159 42648257809553991684697 := by
  unfold tailWord_140159
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112018699235355096567531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3408012466156903397711687 5112018699235355096567531)
  ·
    refine ⟨7668028048853032644851297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5112018699235355096567531 7668028048853032644851297)
    ·
      refine ⟨5751021036639774483638473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7668028048853032644851297 5751021036639774483638473)
      ·
        refine ⟨4313265777479830862728855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5751021036639774483638473 4313265777479830862728855)
        ·
          refine ⟨6469898666219746294093283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4313265777479830862728855 6469898666219746294093283)
          ·
            refine ⟨9704847999329619441139925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469898666219746294093283 9704847999329619441139925)
            ·
              refine ⟨227457374984287955651717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9704847999329619441139925 227457374984287955651717)
              ·
                refine ⟨42648257809553991684697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227457374984287955651717 42648257809553991684697)
                ·
                  rfl

theorem cell19_140159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_140159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140159 prefixEnd_140159 := by exact prefixLift 140159
  have htrace : WordTrace (prefixWord ++ tailWord_140159) baseStart_140159 baseEnd_140159 := by
    simpa [prefixWord, tailWord_140159, baseEnd_140159] using wordTrace_append hprefix tailTrace_140159
  have hstable : (prefixWord ++ tailWord_140159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140159).length < 2 ^ (prefixWord ++ tailWord_140159).sum := by decide
  have hdescent : baseEnd_140159 < baseStart_140159 := by decide
  rcases family_descends (prefixWord ++ tailWord_140159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140235 : List Nat := [1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_140235 : Nat := 118140960795 + 140235 * 2 ^ 59
def prefixEnd_140235 : Nat := 4983230072969 + 3 ^ 40 * 140235 * 2
def baseEnd_140235 : Nat := 42671383456808333995601

theorem tailTrace_140235 : CollatzResearch.WordTrace tailWord_140235 prefixEnd_140235 42671383456808333995601 := by
  unfold tailWord_140235
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114790646960020076334159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3409860431306680050889439 5114790646960020076334159)
  ·
    refine ⟨7672185970440030114501239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114790646960020076334159 7672185970440030114501239)
    ·
      refine ⟨11508278955660045171751859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7672185970440030114501239 11508278955660045171751859)
      ·
        refine ⟨17262418433490067757627789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508278955660045171751859 17262418433490067757627789)
        ·
          refine ⟨6473406912558775409110421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17262418433490067757627789 6473406912558775409110421)
          ·
            refine ⟨303440949026192597302051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6473406912558775409110421 303440949026192597302051)
            ·
              refine ⟨455161423539288895953077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303440949026192597302051 455161423539288895953077)
              ·
                refine ⟨42671383456808333995601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 455161423539288895953077 42671383456808333995601)
                ·
                  rfl

theorem cell19_140235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_140235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140235 prefixEnd_140235 := by exact prefixLift 140235
  have htrace : WordTrace (prefixWord ++ tailWord_140235) baseStart_140235 baseEnd_140235 := by
    simpa [prefixWord, tailWord_140235, baseEnd_140235] using wordTrace_append hprefix tailTrace_140235
  have hstable : (prefixWord ++ tailWord_140235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140235).length < 2 ^ (prefixWord ++ tailWord_140235).sum := by decide
  have hdescent : baseEnd_140235 < baseStart_140235 := by decide
  rcases family_descends (prefixWord ++ tailWord_140235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140273 : List Nat := [1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_140273 : Nat := 118140960795 + 140273 * 2 ^ 59
def prefixEnd_140273 : Nat := 4983230072969 + 3 ^ 40 * 140273 * 2
def baseEnd_140273 : Nat := 42682946280435505151053

theorem tailTrace_140273 : CollatzResearch.WordTrace tailWord_140273 prefixEnd_140273 42682946280435505151053 := by
  unfold tailWord_140273
  simp only [CollatzResearch.WordTrace]
  refine ⟨5116176620822352566217473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3410784413881568377478315 5116176620822352566217473)
  ·
    refine ⟨3837132465616764424663105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5116176620822352566217473 3837132465616764424663105)
    ·
      refine ⟨2877849349212573318497329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3837132465616764424663105 2877849349212573318497329)
      ·
        refine ⟨2158387011909429988872997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2877849349212573318497329 2158387011909429988872997)
        ·
          refine ⟨404697564733018122913687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2158387011909429988872997 404697564733018122913687)
          ·
            refine ⟨607046347099527184370531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404697564733018122913687 607046347099527184370531)
            ·
              refine ⟨910569520649290776555797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607046347099527184370531 910569520649290776555797)
              ·
                refine ⟨42682946280435505151053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 910569520649290776555797 42682946280435505151053)
                ·
                  rfl

theorem cell19_140273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_140273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140273 prefixEnd_140273 := by exact prefixLift 140273
  have htrace : WordTrace (prefixWord ++ tailWord_140273) baseStart_140273 baseEnd_140273 := by
    simpa [prefixWord, tailWord_140273, baseEnd_140273] using wordTrace_append hprefix tailTrace_140273
  have hstable : (prefixWord ++ tailWord_140273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140273).length < 2 ^ (prefixWord ++ tailWord_140273).sum := by decide
  have hdescent : baseEnd_140273 < baseStart_140273 := by decide
  rcases family_descends (prefixWord ++ tailWord_140273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140311 : List Nat := [1, 1, 3, 5, 1, 8]
def baseStart_140311 : Nat := 118140960795 + 140311 * 2 ^ 59
def prefixEnd_140311 : Nat := 4983230072969 + 3 ^ 40 * 140311 * 2
def baseEnd_140311 : Nat := 4743834344895852922945

theorem tailTrace_140311 : CollatzResearch.WordTrace tailWord_140311 prefixEnd_140311 4743834344895852922945 := by
  unfold tailWord_140311
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117562594684685056100787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3411708396456456704067191 5117562594684685056100787)
  ·
    refine ⟨7676343892027027584151181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5117562594684685056100787 7676343892027027584151181)
    ·
      refine ⟨2878628959510135344056693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7676343892027027584151181 2878628959510135344056693)
      ·
        refine ⟨269871464954075188505315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2878628959510135344056693 269871464954075188505315)
        ·
          refine ⟨404807197431112782757973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269871464954075188505315 404807197431112782757973)
          ·
            refine ⟨4743834344895852922945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 404807197431112782757973 4743834344895852922945)
            ·
              rfl

theorem cell19_140311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_140311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140311 prefixEnd_140311 := by exact prefixLift 140311
  have htrace : WordTrace (prefixWord ++ tailWord_140311) baseStart_140311 baseEnd_140311 := by
    simpa [prefixWord, tailWord_140311, baseEnd_140311] using wordTrace_append hprefix tailTrace_140311
  have hstable : (prefixWord ++ tailWord_140311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140311).length < 2 ^ (prefixWord ++ tailWord_140311).sum := by decide
  have hdescent : baseEnd_140311 < baseStart_140311 := by decide
  rcases family_descends (prefixWord ++ tailWord_140311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140425 : List Nat := [1, 2, 1, 1, 4, 5, 5]
def baseStart_140425 : Nat := 118140960795 + 140425 * 2 ^ 59
def prefixEnd_140425 : Nat := 4983230072969 + 3 ^ 40 * 140425 * 2
def baseEnd_140425 : Nat := 14243065858314729924287

theorem tailTrace_140425 : CollatzResearch.WordTrace tailWord_140425 prefixEnd_140425 14243065858314729924287 := by
  unfold tailWord_140425
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121720516271682525750729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3414480344181121683833819 5121720516271682525750729)
  ·
    refine ⟨3841290387203761894313047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5121720516271682525750729 3841290387203761894313047)
    ·
      refine ⟨5761935580805642841469571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841290387203761894313047 5761935580805642841469571)
      ·
        refine ⟨8642903371208464262204357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761935580805642841469571 8642903371208464262204357)
        ·
          refine ⟨1620544382101587049163317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8642903371208464262204357 1620544382101587049163317)
          ·
            refine ⟨151926035822023785859061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1620544382101587049163317 151926035822023785859061)
            ·
              refine ⟨14243065858314729924287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151926035822023785859061 14243065858314729924287)
              ·
                rfl

theorem cell19_140425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_140425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140425 prefixEnd_140425 := by exact prefixLift 140425
  have htrace : WordTrace (prefixWord ++ tailWord_140425) baseStart_140425 baseEnd_140425 := by
    simpa [prefixWord, tailWord_140425, baseEnd_140425] using wordTrace_append hprefix tailTrace_140425
  have hstable : (prefixWord ++ tailWord_140425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140425).length < 2 ^ (prefixWord ++ tailWord_140425).sum := by decide
  have hdescent : baseEnd_140425 < baseStart_140425 := by decide
  rcases family_descends (prefixWord ++ tailWord_140425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140442 : List Nat := [3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_140442 : Nat := 118140960795 + 140442 * 2 ^ 59
def prefixEnd_140442 : Nat := 4983230072969 + 3 ^ 40 * 140442 * 2
def baseEnd_140442 : Nat := 42734370417093187395037

theorem tailTrace_140442 : CollatzResearch.WordTrace tailWord_140442 prefixEnd_140442 42734370417093187395037 := by
  unfold tailWord_140442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280585139302523607279895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3414893704806729619413053 1280585139302523607279895)
  ·
    refine ⟨1920877708953785410919843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1280585139302523607279895 1920877708953785410919843)
    ·
      refine ⟨2881316563430678116379765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920877708953785410919843 2881316563430678116379765)
      ·
        refine ⟨270123427821626073410603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2881316563430678116379765 270123427821626073410603)
        ·
          refine ⟨405185141732439110115905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270123427821626073410603 405185141732439110115905)
          ·
            refine ⟨303888856299329332586929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405185141732439110115905 303888856299329332586929)
            ·
              refine ⟨227916642224496999440197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303888856299329332586929 227916642224496999440197)
              ·
                refine ⟨42734370417093187395037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227916642224496999440197 42734370417093187395037)
                ·
                  rfl

theorem cell19_140442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_140442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140442 prefixEnd_140442 := by exact prefixLift 140442
  have htrace : WordTrace (prefixWord ++ tailWord_140442) baseStart_140442 baseEnd_140442 := by
    simpa [prefixWord, tailWord_140442, baseEnd_140442] using wordTrace_append hprefix tailTrace_140442
  have hstable : (prefixWord ++ tailWord_140442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140442).length < 2 ^ (prefixWord ++ tailWord_140442).sum := by decide
  have hdescent : baseEnd_140442 < baseStart_140442 := by decide
  rcases family_descends (prefixWord ++ tailWord_140442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140444 : List Nat := [2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_140444 : Nat := 118140960795 + 140444 * 2 ^ 59
def prefixEnd_140444 : Nat := 4983230072969 + 3 ^ 40 * 140444 * 2
def baseEnd_140444 : Nat := 42734978986757775350587

theorem tailTrace_140444 : CollatzResearch.WordTrace tailWord_140444 prefixEnd_140444 42734978986757775350587 := by
  unfold tailWord_140444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561206751601424385346193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3414942335468565847128257 2561206751601424385346193)
  ·
    refine ⟨1920905063701068289009645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2561206751601424385346193 1920905063701068289009645)
    ·
      refine ⟨720339398887900608378617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1920905063701068289009645 720339398887900608378617)
      ·
        refine ⟨540254549165925456283963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720339398887900608378617 540254549165925456283963)
        ·
          refine ⟨810381823748888184425945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540254549165925456283963 810381823748888184425945)
          ·
            refine ⟨607786367811666138319459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810381823748888184425945 607786367811666138319459)
            ·
              refine ⟨911679551717499207479189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607786367811666138319459 911679551717499207479189)
              ·
                refine ⟨42734978986757775350587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 911679551717499207479189 42734978986757775350587)
                ·
                  rfl

theorem cell19_140444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_140444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140444 prefixEnd_140444 := by exact prefixLift 140444
  have htrace : WordTrace (prefixWord ++ tailWord_140444) baseStart_140444 baseEnd_140444 := by
    simpa [prefixWord, tailWord_140444, baseEnd_140444] using wordTrace_append hprefix tailTrace_140444
  have hstable : (prefixWord ++ tailWord_140444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140444).length < 2 ^ (prefixWord ++ tailWord_140444).sum := by decide
  have hdescent : baseEnd_140444 < baseStart_140444 := by decide
  rcases family_descends (prefixWord ++ tailWord_140444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140493 : List Nat := [1, 6, 2, 2, 2, 1, 1, 4]
def baseStart_140493 : Nat := 118140960795 + 140493 * 2 ^ 59
def prefixEnd_140493 : Nat := 4983230072969 + 3 ^ 40 * 140493 * 2
def baseEnd_140493 : Nat := 42749888943540180261565

theorem tailTrace_140493 : CollatzResearch.WordTrace tailWord_140493 prefixEnd_140493 42749888943540180261565 := by
  unfold tailWord_140493
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124200680025330139226133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3416133786683553426150755 5124200680025330139226133)
  ·
    refine ⟨240196906876187350276225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5124200680025330139226133 240196906876187350276225)
    ·
      refine ⟨180147680157140512707169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240196906876187350276225 180147680157140512707169)
      ·
        refine ⟨135110760117855384530377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180147680157140512707169 135110760117855384530377)
        ·
          refine ⟨101333070088391538397783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135110760117855384530377 101333070088391538397783)
          ·
            refine ⟨151999605132587307596675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101333070088391538397783 151999605132587307596675)
            ·
              refine ⟨227999407698880961395013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151999605132587307596675 227999407698880961395013)
              ·
                refine ⟨42749888943540180261565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227999407698880961395013 42749888943540180261565)
                ·
                  rfl

theorem cell19_140493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_140493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140493 prefixEnd_140493 := by exact prefixLift 140493
  have htrace : WordTrace (prefixWord ++ tailWord_140493) baseStart_140493 baseEnd_140493 := by
    simpa [prefixWord, tailWord_140493, baseEnd_140493] using wordTrace_append hprefix tailTrace_140493
  have hstable : (prefixWord ++ tailWord_140493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140493).length < 2 ^ (prefixWord ++ tailWord_140493).sum := by decide
  have hdescent : baseEnd_140493 < baseStart_140493 := by decide
  rcases family_descends (prefixWord ++ tailWord_140493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140573 : List Nat := [1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_140573 : Nat := 118140960795 + 140573 * 2 ^ 59
def prefixEnd_140573 : Nat := 4983230072969 + 3 ^ 40 * 140573 * 2
def baseEnd_140573 : Nat := 42774231730123698483569

theorem tailTrace_140573 : CollatzResearch.WordTrace tailWord_140573 prefixEnd_140573 42774231730123698483569 := by
  unfold tailWord_140573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127118519735503802138373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3418079013157002534758915 5127118519735503802138373)
  ·
    refine ⟨961334722450406962900945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5127118519735503802138373 961334722450406962900945)
    ·
      refine ⟨721001041837805222175709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 961334722450406962900945 721001041837805222175709)
      ·
        refine ⟨270375390689176958315891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 721001041837805222175709 270375390689176958315891)
        ·
          refine ⟨405563086033765437473837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270375390689176958315891 405563086033765437473837)
          ·
            refine ⟨152086157262662039052689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 405563086033765437473837 152086157262662039052689)
            ·
              refine ⟨114064617946996529289517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152086157262662039052689 114064617946996529289517)
              ·
                refine ⟨42774231730123698483569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114064617946996529289517 42774231730123698483569)
                ·
                  rfl

theorem cell19_140573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_140573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140573 prefixEnd_140573 := by exact prefixLift 140573
  have htrace : WordTrace (prefixWord ++ tailWord_140573) baseStart_140573 baseEnd_140573 := by
    simpa [prefixWord, tailWord_140573, baseEnd_140573] using wordTrace_append hprefix tailTrace_140573
  have hstable : (prefixWord ++ tailWord_140573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140573).length < 2 ^ (prefixWord ++ tailWord_140573).sum := by decide
  have hdescent : baseEnd_140573 < baseStart_140573 := by decide
  rcases family_descends (prefixWord ++ tailWord_140573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140615 : List Nat := [1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_140615 : Nat := 118140960795 + 140615 * 2 ^ 59
def prefixEnd_140615 : Nat := 4983230072969 + 3 ^ 40 * 140615 * 2
def baseEnd_140615 : Nat := 42787011693080045550121

theorem tailTrace_140615 : CollatzResearch.WordTrace tailWord_140615 prefixEnd_140615 42787011693080045550121 := by
  unfold tailWord_140615
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128650385583344975167299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3419100257055563316778199 5128650385583344975167299)
  ·
    refine ⟨7692975578375017462750949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128650385583344975167299 7692975578375017462750949)
    ·
      refine ⟨1442432920945315774265803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7692975578375017462750949 1442432920945315774265803)
      ·
        refine ⟨2163649381417973661398705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442432920945315774265803 2163649381417973661398705)
        ·
          refine ⟨1622737036063480246049029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2163649381417973661398705 1622737036063480246049029)
          ·
            refine ⟨304263194261902546134193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1622737036063480246049029 304263194261902546134193)
            ·
              refine ⟨228197395696426909600645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304263194261902546134193 228197395696426909600645)
              ·
                refine ⟨42787011693080045550121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228197395696426909600645 42787011693080045550121)
                ·
                  rfl

theorem cell19_140615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_140615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140615 prefixEnd_140615 := by exact prefixLift 140615
  have htrace : WordTrace (prefixWord ++ tailWord_140615) baseStart_140615 baseEnd_140615 := by
    simpa [prefixWord, tailWord_140615, baseEnd_140615] using wordTrace_append hprefix tailTrace_140615
  have hstable : (prefixWord ++ tailWord_140615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140615).length < 2 ^ (prefixWord ++ tailWord_140615).sum := by decide
  have hdescent : baseEnd_140615 < baseStart_140615 := by decide
  rcases family_descends (prefixWord ++ tailWord_140615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140617 : List Nat := [1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_140617 : Nat := 118140960795 + 140617 * 2 ^ 59
def prefixEnd_140617 : Nat := 4983230072969 + 3 ^ 40 * 140617 * 2
def baseEnd_140617 : Nat := 42787620262744633505671

theorem tailTrace_140617 : CollatzResearch.WordTrace tailWord_140617 prefixEnd_140617 42787620262744633505671 := by
  unfold tailWord_140617
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128723331576099316740105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3419148887717399544493403 5128723331576099316740105)
  ·
    refine ⟨3846542498682074487555079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5128723331576099316740105 3846542498682074487555079)
    ·
      refine ⟨5769813748023111731332619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3846542498682074487555079 5769813748023111731332619)
      ·
        refine ⟨8654720622034667596998929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769813748023111731332619 8654720622034667596998929)
        ·
          refine ⟨6491040466526000697749197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8654720622034667596998929 6491040466526000697749197)
          ·
            refine ⟨2434140174947250261655949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6491040466526000697749197 2434140174947250261655949)
            ·
              refine ⟨912802565605218848120981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2434140174947250261655949 912802565605218848120981)
              ·
                refine ⟨42787620262744633505671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 912802565605218848120981 42787620262744633505671)
                ·
                  rfl

theorem cell19_140617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_140617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140617 prefixEnd_140617 := by exact prefixLift 140617
  have htrace : WordTrace (prefixWord ++ tailWord_140617) baseStart_140617 baseEnd_140617 := by
    simpa [prefixWord, tailWord_140617, baseEnd_140617] using wordTrace_append hprefix tailTrace_140617
  have hstable : (prefixWord ++ tailWord_140617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140617).length < 2 ^ (prefixWord ++ tailWord_140617).sum := by decide
  have hdescent : baseEnd_140617 < baseStart_140617 := by decide
  rcases family_descends (prefixWord ++ tailWord_140617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140693 : List Nat := [1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_140693 : Nat := 118140960795 + 140693 * 2 ^ 59
def prefixEnd_140693 : Nat := 4983230072969 + 3 ^ 40 * 140693 * 2
def baseEnd_140693 : Nat := 42810745909998975816575

theorem tailTrace_140693 : CollatzResearch.WordTrace tailWord_140693 prefixEnd_140693 42810745909998975816575 := by
  unfold tailWord_140693
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131495279300764296506733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3420996852867176197671155 5131495279300764296506733)
  ·
    refine ⟨1924310729737786611190025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5131495279300764296506733 1924310729737786611190025)
    ·
      refine ⟨1443233047303339958392519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1924310729737786611190025 1443233047303339958392519)
      ·
        refine ⟨2164849570955009937588779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443233047303339958392519 2164849570955009937588779)
        ·
          refine ⟨3247274356432514906383169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164849570955009937588779 3247274356432514906383169)
          ·
            refine ⟨2435455767324386179787377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3247274356432514906383169 2435455767324386179787377)
            ·
              refine ⟨1826591825493289634840533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435455767324386179787377 1826591825493289634840533)
              ·
                refine ⟨42810745909998975816575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1826591825493289634840533 42810745909998975816575)
                ·
                  rfl

theorem cell19_140693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_140693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140693 prefixEnd_140693 := by exact prefixLift 140693
  have htrace : WordTrace (prefixWord ++ tailWord_140693) baseStart_140693 baseEnd_140693 := by
    simpa [prefixWord, tailWord_140693, baseEnd_140693] using wordTrace_append hprefix tailTrace_140693
  have hstable : (prefixWord ++ tailWord_140693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140693).length < 2 ^ (prefixWord ++ tailWord_140693).sum := by decide
  have hdescent : baseEnd_140693 < baseStart_140693 := by decide
  rcases family_descends (prefixWord ++ tailWord_140693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140738 : List Nat := [3, 5, 2, 1, 1, 2, 2, 3]
def baseStart_140738 : Nat := 118140960795 + 140738 * 2 ^ 59
def prefixEnd_140738 : Nat := 4983230072969 + 3 ^ 40 * 140738 * 2
def baseEnd_140738 : Nat := 42824438727452204816453

theorem tailTrace_140738 : CollatzResearch.WordTrace tailWord_140738 prefixEnd_140738 42824438727452204816453 := by
  unfold tailWord_140738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283284141034434245473717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3422091042758491321263245 1283284141034434245473717)
  ·
    refine ⟨120307888221978210513161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1283284141034434245473717 120307888221978210513161)
    ·
      refine ⟨90230916166483657884871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120307888221978210513161 90230916166483657884871)
      ·
        refine ⟨135346374249725486827307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90230916166483657884871 135346374249725486827307)
        ·
          refine ⟨203019561374588230240961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135346374249725486827307 203019561374588230240961)
          ·
            refine ⟨152264671030941172680721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203019561374588230240961 152264671030941172680721)
            ·
              refine ⟨114198503273205879510541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152264671030941172680721 114198503273205879510541)
              ·
                refine ⟨42824438727452204816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114198503273205879510541 42824438727452204816453)
                ·
                  rfl

theorem cell19_140738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_140738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140738 prefixEnd_140738 := by exact prefixLift 140738
  have htrace : WordTrace (prefixWord ++ tailWord_140738) baseStart_140738 baseEnd_140738 := by
    simpa [prefixWord, tailWord_140738, baseEnd_140738] using wordTrace_append hprefix tailTrace_140738
  have hstable : (prefixWord ++ tailWord_140738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140738).length < 2 ^ (prefixWord ++ tailWord_140738).sum := by decide
  have hdescent : baseEnd_140738 < baseStart_140738 := by decide
  rcases family_descends (prefixWord ++ tailWord_140738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140746 : List Nat := [3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_140746 : Nat := 118140960795 + 140746 * 2 ^ 59
def prefixEnd_140746 : Nat := 4983230072969 + 3 ^ 40 * 140746 * 2
def baseEnd_140746 : Nat := 42826873006110556638653

theorem tailTrace_140746 : CollatzResearch.WordTrace tailWord_140746 prefixEnd_140746 42826873006110556638653 := by
  unfold tailWord_140746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283357087027188587046523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3422285565405836232124061 1283357087027188587046523)
  ·
    refine ⟨1925035630540782880569785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283357087027188587046523 1925035630540782880569785)
    ·
      refine ⟨1443776722905587160427339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1925035630540782880569785 1443776722905587160427339)
      ·
        refine ⟨2165665084358380740641009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443776722905587160427339 2165665084358380740641009)
        ·
          refine ⟨1624248813268785555480757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165665084358380740641009 1624248813268785555480757)
          ·
            refine ⟨152273326243948645826321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1624248813268785555480757 152273326243948645826321)
            ·
              refine ⟨114204994682961484369741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152273326243948645826321 114204994682961484369741)
              ·
                refine ⟨42826873006110556638653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114204994682961484369741 42826873006110556638653)
                ·
                  rfl

theorem cell19_140746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_140746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140746 prefixEnd_140746 := by exact prefixLift 140746
  have htrace : WordTrace (prefixWord ++ tailWord_140746) baseStart_140746 baseEnd_140746 := by
    simpa [prefixWord, tailWord_140746, baseEnd_140746] using wordTrace_append hprefix tailTrace_140746
  have hstable : (prefixWord ++ tailWord_140746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140746).length < 2 ^ (prefixWord ++ tailWord_140746).sum := by decide
  have hdescent : baseEnd_140746 < baseStart_140746 := by decide
  rcases family_descends (prefixWord ++ tailWord_140746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140748 : List Nat := [2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_140748 : Nat := 118140960795 + 140748 * 2 ^ 59
def prefixEnd_140748 : Nat := 4983230072969 + 3 ^ 40 * 140748 * 2
def baseEnd_140748 : Nat := 42827481575775144594203

theorem tailTrace_140748 : CollatzResearch.WordTrace tailWord_140748 prefixEnd_140748 42827481575775144594203 := by
  unfold tailWord_140748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566750647050754344879449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3422334196067672459839265 2566750647050754344879449)
  ·
    refine ⟨1925062985288065758659587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2566750647050754344879449 1925062985288065758659587)
    ·
      refine ⟨2887594477932098637989381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925062985288065758659587 2887594477932098637989381)
      ·
        refine ⟨541423964612268494623009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2887594477932098637989381 541423964612268494623009)
        ·
          refine ⟨406067973459201370967257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541423964612268494623009 406067973459201370967257)
          ·
            refine ⟨304550980094401028225443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406067973459201370967257 304550980094401028225443)
            ·
              refine ⟨456826470141601542338165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304550980094401028225443 456826470141601542338165)
              ·
                refine ⟨42827481575775144594203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 456826470141601542338165 42827481575775144594203)
                ·
                  rfl

theorem cell19_140748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_140748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140748 prefixEnd_140748 := by exact prefixLift 140748
  have htrace : WordTrace (prefixWord ++ tailWord_140748) baseStart_140748 baseEnd_140748 := by
    simpa [prefixWord, tailWord_140748, baseEnd_140748] using wordTrace_append hprefix tailTrace_140748
  have hstable : (prefixWord ++ tailWord_140748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140748).length < 2 ^ (prefixWord ++ tailWord_140748).sum := by decide
  have hdescent : baseEnd_140748 < baseStart_140748 := by decide
  rcases family_descends (prefixWord ++ tailWord_140748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140769 : List Nat := [1, 2, 3, 1, 2, 3, 7]
def baseStart_140769 : Nat := 118140960795 + 140769 * 2 ^ 59
def prefixEnd_140769 : Nat := 4983230072969 + 3 ^ 40 * 140769 * 2
def baseEnd_140769 : Nat := 14277957185751106042493

theorem tailTrace_140769 : CollatzResearch.WordTrace tailWord_140769 prefixEnd_140769 14277957185751106042493 := by
  unfold tailWord_140769
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134267227025429276273361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3422844818016952850848907 5134267227025429276273361)
  ·
    refine ⟨3850700420269071957205021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5134267227025429276273361 3850700420269071957205021)
    ·
      refine ⟨1444012657600901983951883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3850700420269071957205021 1444012657600901983951883)
      ·
        refine ⟨2166018986401352975927825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444012657600901983951883 2166018986401352975927825)
        ·
          refine ⟨1624514239801014731945869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166018986401352975927825 1624514239801014731945869)
          ·
            refine ⟨609192839925380524479701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1624514239801014731945869 609192839925380524479701)
            ·
              refine ⟨14277957185751106042493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 609192839925380524479701 14277957185751106042493)
              ·
                rfl

theorem cell19_140769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_140769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140769 prefixEnd_140769 := by exact prefixLift 140769
  have htrace : WordTrace (prefixWord ++ tailWord_140769) baseStart_140769 baseEnd_140769 := by
    simpa [prefixWord, tailWord_140769, baseEnd_140769] using wordTrace_append hprefix tailTrace_140769
  have hstable : (prefixWord ++ tailWord_140769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140769).length < 2 ^ (prefixWord ++ tailWord_140769).sum := by decide
  have hdescent : baseEnd_140769 < baseStart_140769 := by decide
  rcases family_descends (prefixWord ++ tailWord_140769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140786 : List Nat := [3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_140786 : Nat := 118140960795 + 140786 * 2 ^ 59
def prefixEnd_140786 : Nat := 4983230072969 + 3 ^ 40 * 140786 * 2
def baseEnd_140786 : Nat := 42839044399402315749655

theorem tailTrace_140786 : CollatzResearch.WordTrace tailWord_140786 prefixEnd_140786 42839044399402315749655 := by
  unfold tailWord_140786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283721816990960294910553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3423258178642560786428141 1283721816990960294910553)
  ·
    refine ⟨962791362743220221182915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1283721816990960294910553 962791362743220221182915)
    ·
      refine ⟨1444187044114830331774373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962791362743220221182915 1444187044114830331774373)
      ·
        refine ⟨270785070771530687207695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1444187044114830331774373 270785070771530687207695)
        ·
          refine ⟨406177606157296030811543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270785070771530687207695 406177606157296030811543)
          ·
            refine ⟨609266409235944046217315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406177606157296030811543 609266409235944046217315)
            ·
              refine ⟨913899613853916069325973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609266409235944046217315 913899613853916069325973)
              ·
                refine ⟨42839044399402315749655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 913899613853916069325973 42839044399402315749655)
                ·
                  rfl

theorem cell19_140786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_140786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140786 prefixEnd_140786 := by exact prefixLift 140786
  have htrace : WordTrace (prefixWord ++ tailWord_140786) baseStart_140786 baseEnd_140786 := by
    simpa [prefixWord, tailWord_140786, baseEnd_140786] using wordTrace_append hprefix tailTrace_140786
  have hstable : (prefixWord ++ tailWord_140786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140786).length < 2 ^ (prefixWord ++ tailWord_140786).sum := by decide
  have hdescent : baseEnd_140786 < baseStart_140786 := by decide
  rcases family_descends (prefixWord ++ tailWord_140786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140824 : List Nat := [2, 1, 2, 3, 5, 6]
def baseStart_140824 : Nat := 118140960795 + 140824 * 2 ^ 59
def prefixEnd_140824 : Nat := 4983230072969 + 3 ^ 40 * 140824 * 2
def baseEnd_140824 : Nat := 4761178580336609656123

theorem tailTrace_140824 : CollatzResearch.WordTrace tailWord_140824 prefixEnd_140824 4761178580336609656123 := by
  unfold tailWord_140824
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568136620913086834762763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3424182161217449113017017 2568136620913086834762763)
  ·
    refine ⟨3852204931369630252144145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568136620913086834762763 3852204931369630252144145)
    ·
      refine ⟨2889153698527222689108109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3852204931369630252144145 2889153698527222689108109)
      ·
        refine ⟨1083432636947708508415541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2889153698527222689108109 1083432636947708508415541)
        ·
          refine ⟨101571809713847672663957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1083432636947708508415541 101571809713847672663957)
          ·
            refine ⟨4761178580336609656123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101571809713847672663957 4761178580336609656123)
            ·
              rfl

theorem cell19_140824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_140824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140824 prefixEnd_140824 := by exact prefixLift 140824
  have htrace : WordTrace (prefixWord ++ tailWord_140824) baseStart_140824 baseEnd_140824 := by
    simpa [prefixWord, tailWord_140824, baseEnd_140824] using wordTrace_append hprefix tailTrace_140824
  have hstable : (prefixWord ++ tailWord_140824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140824).length < 2 ^ (prefixWord ++ tailWord_140824).sum := by decide
  have hdescent : baseEnd_140824 < baseStart_140824 := by decide
  rcases family_descends (prefixWord ++ tailWord_140824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140860 : List Nat := [2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_140860 : Nat := 118140960795 + 140860 * 2 ^ 59
def prefixEnd_140860 : Nat := 4983230072969 + 3 ^ 40 * 140860 * 2
def baseEnd_140860 : Nat := 42861561476992070105009

theorem tailTrace_140860 : CollatzResearch.WordTrace tailWord_140860 prefixEnd_140860 42861561476992070105009 := by
  unfold tailWord_140860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568793134847875908918017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3425057513130501211890689 2568793134847875908918017)
  ·
    refine ⟨1926594851135906931688513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2568793134847875908918017 1926594851135906931688513)
    ·
      refine ⟨1444946138351930198766385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1926594851135906931688513 1444946138351930198766385)
      ·
        refine ⟨1083709603763947649074789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1444946138351930198766385 1083709603763947649074789)
        ·
          refine ⟨203195550705740184201523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1083709603763947649074789 203195550705740184201523)
          ·
            refine ⟨304793326058610276302285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203195550705740184201523 304793326058610276302285)
            ·
              refine ⟨114297497271978853613357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304793326058610276302285 114297497271978853613357)
              ·
                refine ⟨42861561476992070105009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114297497271978853613357 42861561476992070105009)
                ·
                  rfl

theorem cell19_140860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_140860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140860 prefixEnd_140860 := by exact prefixLift 140860
  have htrace : WordTrace (prefixWord ++ tailWord_140860) baseStart_140860 baseEnd_140860 := by
    simpa [prefixWord, tailWord_140860, baseEnd_140860] using wordTrace_append hprefix tailTrace_140860
  have hstable : (prefixWord ++ tailWord_140860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140860).length < 2 ^ (prefixWord ++ tailWord_140860).sum := by decide
  have hdescent : baseEnd_140860 < baseStart_140860 := by decide
  rcases family_descends (prefixWord ++ tailWord_140860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140917 : List Nat := [1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_140917 : Nat := 118140960795 + 140917 * 2 ^ 59
def prefixEnd_140917 : Nat := 4983230072969 + 3 ^ 40 * 140917 * 2
def baseEnd_140917 : Nat := 42878905712432826838187

theorem tailTrace_140917 : CollatzResearch.WordTrace tailWord_140917 prefixEnd_140917 42878905712432826838187 := by
  unfold tailWord_140917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139665230489250552661005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3426443486992833701774003 5139665230489250552661005)
  ·
    refine ⟨1927374461433468957247877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5139665230489250552661005 1927374461433468957247877)
    ·
      refine ⟨361382711518775429483977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1927374461433468957247877 361382711518775429483977)
      ·
        refine ⟨271037033639081572112983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361382711518775429483977 271037033639081572112983)
        ·
          refine ⟨406555550458622358169475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271037033639081572112983 406555550458622358169475)
          ·
            refine ⟨609833325687933537254213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406555550458622358169475 609833325687933537254213)
            ·
              refine ⟨114343748566487538235165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 609833325687933537254213 114343748566487538235165)
              ·
                refine ⟨42878905712432826838187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114343748566487538235165 42878905712432826838187)
                ·
                  rfl

theorem cell19_140917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_140917 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140917 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140917 prefixEnd_140917 := by exact prefixLift 140917
  have htrace : WordTrace (prefixWord ++ tailWord_140917) baseStart_140917 baseEnd_140917 := by
    simpa [prefixWord, tailWord_140917, baseEnd_140917] using wordTrace_append hprefix tailTrace_140917
  have hstable : (prefixWord ++ tailWord_140917).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140917).length < 2 ^ (prefixWord ++ tailWord_140917).sum := by decide
  have hdescent : baseEnd_140917 < baseStart_140917 := by decide
  rcases family_descends (prefixWord ++ tailWord_140917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140921 : List Nat := [1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_140921 : Nat := 118140960795 + 140921 * 2 ^ 59
def prefixEnd_140921 : Nat := 4983230072969 + 3 ^ 40 * 140921 * 2
def baseEnd_140921 : Nat := 42880122851762002749287

theorem tailTrace_140921 : CollatzResearch.WordTrace tailWord_140921 prefixEnd_140921 42880122851762002749287 := by
  unfold tailWord_140921
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139811122474759235806617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3426540748316506157204411 5139811122474759235806617)
  ·
    refine ⟨3854858341856069426854963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5139811122474759235806617 3854858341856069426854963)
    ·
      refine ⟨5782287512784104140282445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3854858341856069426854963 5782287512784104140282445)
      ·
        refine ⟨2168357817294039052605917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5782287512784104140282445 2168357817294039052605917)
        ·
          refine ⟨813134181485264644727219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2168357817294039052605917 813134181485264644727219)
          ·
            refine ⟨1219701272227896967090829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813134181485264644727219 1219701272227896967090829)
            ·
              refine ⟨457387977085461362659061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1219701272227896967090829 457387977085461362659061)
              ·
                refine ⟨42880122851762002749287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457387977085461362659061 42880122851762002749287)
                ·
                  rfl

theorem cell19_140921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_140921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140921 prefixEnd_140921 := by exact prefixLift 140921
  have htrace : WordTrace (prefixWord ++ tailWord_140921) baseStart_140921 baseEnd_140921 := by
    simpa [prefixWord, tailWord_140921, baseEnd_140921] using wordTrace_append hprefix tailTrace_140921
  have hstable : (prefixWord ++ tailWord_140921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140921).length < 2 ^ (prefixWord ++ tailWord_140921).sum := by decide
  have hdescent : baseEnd_140921 < baseStart_140921 := by decide
  rcases family_descends (prefixWord ++ tailWord_140921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140936 : List Nat := [2, 1, 3, 5, 1, 2, 5]
def baseStart_140936 : Nat := 118140960795 + 140936 * 2 ^ 59
def prefixEnd_140936 : Nat := 4983230072969 + 3 ^ 40 * 140936 * 2
def baseEnd_140936 : Nat := 14294895708082137471971

theorem tailTrace_140936 : CollatzResearch.WordTrace tailWord_140936 prefixEnd_140936 14294895708082137471971 := by
  unfold tailWord_140936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570179108710208398801331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3426905478280277865068441 2570179108710208398801331)
  ·
    refine ⟨3855268663065312598201997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570179108710208398801331 3855268663065312598201997)
    ·
      refine ⟨1445725748649492224325749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3855268663065312598201997 1445725748649492224325749)
      ·
        refine ⟨135536788935889896030539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1445725748649492224325749 135536788935889896030539)
        ·
          refine ⟨203305183403834844045809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135536788935889896030539 203305183403834844045809)
          ·
            refine ⟨152478887552876133034357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203305183403834844045809 152478887552876133034357)
            ·
              refine ⟨14294895708082137471971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152478887552876133034357 14294895708082137471971)
              ·
                rfl

theorem cell19_140936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_140936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140936 prefixEnd_140936 := by exact prefixLift 140936
  have htrace : WordTrace (prefixWord ++ tailWord_140936) baseStart_140936 baseEnd_140936 := by
    simpa [prefixWord, tailWord_140936, baseEnd_140936] using wordTrace_append hprefix tailTrace_140936
  have hstable : (prefixWord ++ tailWord_140936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140936).length < 2 ^ (prefixWord ++ tailWord_140936).sum := by decide
  have hdescent : baseEnd_140936 < baseStart_140936 := by decide
  rcases family_descends (prefixWord ++ tailWord_140936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140938 : List Nat := [3, 1, 2, 3, 2, 3, 5]
def baseStart_140938 : Nat := 118140960795 + 140938 * 2 ^ 59
def prefixEnd_140938 : Nat := 4983230072969 + 3 ^ 40 * 140938 * 2
def baseEnd_140938 : Nat := 14295098564637000123821

theorem tailTrace_140938 : CollatzResearch.WordTrace tailWord_140938 prefixEnd_140938 14295098564637000123821 := by
  unfold tailWord_140938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285107790853292784793867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3426954108942114092783645 1285107790853292784793867)
  ·
    refine ⟨1927661686279939177190801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1285107790853292784793867 1927661686279939177190801)
    ·
      refine ⟨1445746264709954382893101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1927661686279939177190801 1445746264709954382893101)
      ·
        refine ⟨542154849266232893584913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1445746264709954382893101 542154849266232893584913)
        ·
          refine ⟨406616136949674670188685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542154849266232893584913 406616136949674670188685)
          ·
            refine ⟨152481051356128001320757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406616136949674670188685 152481051356128001320757)
            ·
              refine ⟨14295098564637000123821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152481051356128001320757 14295098564637000123821)
              ·
                rfl

theorem cell19_140938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_140938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140938 prefixEnd_140938 := by exact prefixLift 140938
  have htrace : WordTrace (prefixWord ++ tailWord_140938) baseStart_140938 baseEnd_140938 := by
    simpa [prefixWord, tailWord_140938, baseEnd_140938] using wordTrace_append hprefix tailTrace_140938
  have hstable : (prefixWord ++ tailWord_140938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140938).length < 2 ^ (prefixWord ++ tailWord_140938).sum := by decide
  have hdescent : baseEnd_140938 < baseStart_140938 := by decide
  rcases family_descends (prefixWord ++ tailWord_140938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140978 : List Nat := [3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_140978 : Nat := 118140960795 + 140978 * 2 ^ 59
def prefixEnd_140978 : Nat := 4983230072969 + 3 ^ 40 * 140978 * 2
def baseEnd_140978 : Nat := 42897467087202759482465

theorem tailTrace_140978 : CollatzResearch.WordTrace tailWord_140978 prefixEnd_140978 42897467087202759482465 := by
  unfold tailWord_140978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285472520817064492657897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3427926722178838647087725 1285472520817064492657897)
  ·
    refine ⟨964104390612798369493423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1285472520817064492657897 964104390612798369493423)
    ·
      refine ⟨1446156585919197554240135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964104390612798369493423 1446156585919197554240135)
      ·
        refine ⟨2169234878878796331360203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446156585919197554240135 2169234878878796331360203)
        ·
          refine ⟨3253852318318194497040305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169234878878796331360203 3253852318318194497040305)
          ·
            refine ⟨2440389238738645872780229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3253852318318194497040305 2440389238738645872780229)
            ·
              refine ⟨457572982263496101146293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2440389238738645872780229 457572982263496101146293)
              ·
                refine ⟨42897467087202759482465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457572982263496101146293 42897467087202759482465)
                ·
                  rfl

theorem cell19_140978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_140978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_140978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_140978 prefixEnd_140978 := by exact prefixLift 140978
  have htrace : WordTrace (prefixWord ++ tailWord_140978) baseStart_140978 baseEnd_140978 := by
    simpa [prefixWord, tailWord_140978, baseEnd_140978] using wordTrace_append hprefix tailTrace_140978
  have hstable : (prefixWord ++ tailWord_140978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140978).length < 2 ^ (prefixWord ++ tailWord_140978).sum := by decide
  have hdescent : baseEnd_140978 < baseStart_140978 := by decide
  rcases family_descends (prefixWord ++ tailWord_140978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141012 : List Nat := [2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_141012 : Nat := 118140960795 + 141012 * 2 ^ 59
def prefixEnd_141012 : Nat := 4983230072969 + 3 ^ 40 * 141012 * 2
def baseEnd_141012 : Nat := 42907812771500754726817

theorem tailTrace_141012 : CollatzResearch.WordTrace tailWord_141012 prefixEnd_141012 42907812771500754726817 := by
  unfold tailWord_141012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571565082572540888684645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3428753443430054518246193 2571565082572540888684645)
  ·
    refine ⟨482168452982351416628371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2571565082572540888684645 482168452982351416628371)
    ·
      refine ⟨723252679473527124942557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482168452982351416628371 723252679473527124942557)
      ·
        refine ⟨271219754802572671853459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 723252679473527124942557 271219754802572671853459)
        ·
          refine ⟨406829632203859007780189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271219754802572671853459 406829632203859007780189)
          ·
            refine ⟨152561112076447127917571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406829632203859007780189 152561112076447127917571)
            ·
              refine ⟨228841668114670691876357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152561112076447127917571 228841668114670691876357)
              ·
                refine ⟨42907812771500754726817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228841668114670691876357 42907812771500754726817)
                ·
                  rfl

theorem cell19_141012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_141012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141012 prefixEnd_141012 := by exact prefixLift 141012
  have htrace : WordTrace (prefixWord ++ tailWord_141012) baseStart_141012 baseEnd_141012 := by
    simpa [prefixWord, tailWord_141012, baseEnd_141012] using wordTrace_append hprefix tailTrace_141012
  have hstable : (prefixWord ++ tailWord_141012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141012).length < 2 ^ (prefixWord ++ tailWord_141012).sum := by decide
  have hdescent : baseEnd_141012 < baseStart_141012 := by decide
  rcases family_descends (prefixWord ++ tailWord_141012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141086 : List Nat := [4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_141086 : Nat := 118140960795 + 141086 * 2 ^ 59
def prefixEnd_141086 : Nat := 4983230072969 + 3 ^ 40 * 141086 * 2
def baseEnd_141086 : Nat := 42930329849090509082171

theorem tailTrace_141086 : CollatzResearch.WordTrace tailWord_141086 prefixEnd_141086 42930329849090509082171 := by
  unfold tailWord_141086
  simp only [CollatzResearch.WordTrace]
  refine ⟨643228645859624051945389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3430552777917994943708741 643228645859624051945389)
  ·
    refine ⟨241210742197359019479521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 643228645859624051945389 241210742197359019479521)
    ·
      refine ⟨180908056648019264609641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241210742197359019479521 180908056648019264609641)
      ·
        refine ⟨135681042486014448457231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180908056648019264609641 135681042486014448457231)
        ·
          refine ⟨203521563729021672685847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135681042486014448457231 203521563729021672685847)
          ·
            refine ⟨305282345593532509028771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203521563729021672685847 305282345593532509028771)
            ·
              refine ⟨457923518390298763543157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305282345593532509028771 457923518390298763543157)
              ·
                refine ⟨42930329849090509082171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457923518390298763543157 42930329849090509082171)
                ·
                  rfl

theorem cell19_141086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_141086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141086 prefixEnd_141086 := by exact prefixLift 141086
  have htrace : WordTrace (prefixWord ++ tailWord_141086) baseStart_141086 baseEnd_141086 := by
    simpa [prefixWord, tailWord_141086, baseEnd_141086] using wordTrace_append hprefix tailTrace_141086
  have hstable : (prefixWord ++ tailWord_141086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141086).length < 2 ^ (prefixWord ++ tailWord_141086).sum := by decide
  have hdescent : baseEnd_141086 < baseStart_141086 := by decide
  rcases family_descends (prefixWord ++ tailWord_141086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141109 : List Nat := [1, 3, 3, 1, 4, 2, 5]
def baseStart_141109 : Nat := 118140960795 + 141109 * 2 ^ 59
def prefixEnd_141109 : Nat := 4983230072969 + 3 ^ 40 * 141109 * 2
def baseEnd_141109 : Nat := 14312442800077756856999

theorem tailTrace_141109 : CollatzResearch.WordTrace tailWord_141109 prefixEnd_141109 14312442800077756856999 := by
  unfold tailWord_141109
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146668045793667343650381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3431112030529111562433587 5146668045793667343650381)
  ·
    refine ⟨1930000517172625253868893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5146668045793667343650381 1930000517172625253868893)
    ·
      refine ⟨723750193939734470200835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1930000517172625253868893 723750193939734470200835)
      ·
        refine ⟨1085625290909601705301253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723750193939734470200835 1085625290909601705301253)
        ·
          refine ⟨203554742045550319743985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1085625290909601705301253 203554742045550319743985)
          ·
            refine ⟨152666056534162739807989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203554742045550319743985 152666056534162739807989)
            ·
              refine ⟨14312442800077756856999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152666056534162739807989 14312442800077756856999)
              ·
                rfl

theorem cell19_141109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_141109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141109 prefixEnd_141109 := by exact prefixLift 141109
  have htrace : WordTrace (prefixWord ++ tailWord_141109) baseStart_141109 baseEnd_141109 := by
    simpa [prefixWord, tailWord_141109, baseEnd_141109] using wordTrace_append hprefix tailTrace_141109
  have hstable : (prefixWord ++ tailWord_141109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141109).length < 2 ^ (prefixWord ++ tailWord_141109).sum := by decide
  have hdescent : baseEnd_141109 < baseStart_141109 := by decide
  rcases family_descends (prefixWord ++ tailWord_141109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141126 : List Nat := [6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_141126 : Nat := 118140960795 + 141126 * 2 ^ 59
def prefixEnd_141126 : Nat := 4983230072969 + 3 ^ 40 * 141126 * 2
def baseEnd_141126 : Nat := 42942501242382268193173

theorem tailTrace_141126 : CollatzResearch.WordTrace tailWord_141126 prefixEnd_141126 42942501242382268193173 := by
  unfold tailWord_141126
  simp only [CollatzResearch.WordTrace]
  refine ⟨160852752710377476469351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3431525391154719498012821 160852752710377476469351)
  ·
    refine ⟨241279129065566214704027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160852752710377476469351 241279129065566214704027)
    ·
      refine ⟨361918693598349322056041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241279129065566214704027 361918693598349322056041)
      ·
        refine ⟨271439020198761991542031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361918693598349322056041 271439020198761991542031)
        ·
          refine ⟨407158530298142987313047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271439020198761991542031 407158530298142987313047)
          ·
            refine ⟨610737795447214480969571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407158530298142987313047 610737795447214480969571)
            ·
              refine ⟨916106693170821721454357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610737795447214480969571 916106693170821721454357)
              ·
                refine ⟨42942501242382268193173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 916106693170821721454357 42942501242382268193173)
                ·
                  rfl

theorem cell19_141126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_141126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141126 prefixEnd_141126 := by exact prefixLift 141126
  have htrace : WordTrace (prefixWord ++ tailWord_141126) baseStart_141126 baseEnd_141126 := by
    simpa [prefixWord, tailWord_141126, baseEnd_141126] using wordTrace_append hprefix tailTrace_141126
  have hstable : (prefixWord ++ tailWord_141126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141126).length < 2 ^ (prefixWord ++ tailWord_141126).sum := by decide
  have hdescent : baseEnd_141126 < baseStart_141126 := by decide
  rcases family_descends (prefixWord ++ tailWord_141126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141130 : List Nat := [3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_141130 : Nat := 118140960795 + 141130 * 2 ^ 59
def prefixEnd_141130 : Nat := 4983230072969 + 3 ^ 40 * 141130 * 2
def baseEnd_141130 : Nat := 42943718381711444104273

theorem tailTrace_141130 : CollatzResearch.WordTrace tailWord_141130 prefixEnd_141130 42943718381711444104273 := by
  unfold tailWord_141130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286858494679396982541211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3431622652478391953443229 1286858494679396982541211)
  ·
    refine ⟨1930287742019095473811817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1286858494679396982541211 1930287742019095473811817)
    ·
      refine ⟨1447715806514321605358863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1930287742019095473811817 1447715806514321605358863)
      ·
        refine ⟨2171573709771482408038295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447715806514321605358863 2171573709771482408038295)
        ·
          refine ⟨3257360564657223612057443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171573709771482408038295 3257360564657223612057443)
          ·
            refine ⟨4886040846985835418086165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257360564657223612057443 4886040846985835418086165)
            ·
              refine ⟨229033164702461035222789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4886040846985835418086165 229033164702461035222789)
              ·
                refine ⟨42943718381711444104273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229033164702461035222789 42943718381711444104273)
                ·
                  rfl

theorem cell19_141130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_141130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141130 prefixEnd_141130 := by exact prefixLift 141130
  have htrace : WordTrace (prefixWord ++ tailWord_141130) baseStart_141130 baseEnd_141130 := by
    simpa [prefixWord, tailWord_141130, baseEnd_141130] using wordTrace_append hprefix tailTrace_141130
  have hstable : (prefixWord ++ tailWord_141130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141130).length < 2 ^ (prefixWord ++ tailWord_141130).sum := by decide
  have hdescent : baseEnd_141130 < baseStart_141130 := by decide
  rcases family_descends (prefixWord ++ tailWord_141130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141187 : List Nat := [1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_141187 : Nat := 118140960795 + 141187 * 2 ^ 59
def prefixEnd_141187 : Nat := 4983230072969 + 3 ^ 40 * 141187 * 2
def baseEnd_141187 : Nat := 42961062617152200837451

theorem tailTrace_141187 : CollatzResearch.WordTrace tailWord_141187 prefixEnd_141187 42961062617152200837451 := by
  unfold tailWord_141187
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149512939511086664989815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3433008626340724443326543 5149512939511086664989815)
  ·
    refine ⟨7724269409266629997484723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5149512939511086664989815 7724269409266629997484723)
    ·
      refine ⟨11586404113899944996227085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7724269409266629997484723 11586404113899944996227085)
      ·
        refine ⟨4344901542712479373585157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11586404113899944996227085 4344901542712479373585157)
        ·
          refine ⟨814669039258589882547217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4344901542712479373585157 814669039258589882547217)
          ·
            refine ⟨611001779443942411910413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814669039258589882547217 611001779443942411910413)
            ·
              refine ⟨229125667291478404466405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611001779443942411910413 229125667291478404466405)
              ·
                refine ⟨42961062617152200837451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229125667291478404466405 42961062617152200837451)
                ·
                  rfl

theorem cell19_141187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_141187 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141187 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141187 prefixEnd_141187 := by exact prefixLift 141187
  have htrace : WordTrace (prefixWord ++ tailWord_141187) baseStart_141187 baseEnd_141187 := by
    simpa [prefixWord, tailWord_141187, baseEnd_141187] using wordTrace_append hprefix tailTrace_141187
  have hstable : (prefixWord ++ tailWord_141187).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141187).length < 2 ^ (prefixWord ++ tailWord_141187).sum := by decide
  have hdescent : baseEnd_141187 < baseStart_141187 := by decide
  rcases family_descends (prefixWord ++ tailWord_141187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141202 : List Nat := [3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_141202 : Nat := 118140960795 + 141202 * 2 ^ 59
def prefixEnd_141202 : Nat := 4983230072969 + 3 ^ 40 * 141202 * 2
def baseEnd_141202 : Nat := 42965626889636610504077

theorem tailTrace_141202 : CollatzResearch.WordTrace tailWord_141202 prefixEnd_141202 42965626889636610504077 := by
  unfold tailWord_141202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1287515008614186056696465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3433373356304496151190573 1287515008614186056696465)
  ·
    refine ⟨965636256460639542522349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1287515008614186056696465 965636256460639542522349)
    ·
      refine ⟨362113596172739828445881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 965636256460639542522349 362113596172739828445881)
      ·
        refine ⟨271585197129554871334411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362113596172739828445881 271585197129554871334411)
        ·
          refine ⟨407377795694332307001617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271585197129554871334411 407377795694332307001617)
          ·
            refine ⟨305533346770749230251213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407377795694332307001617 305533346770749230251213)
            ·
              refine ⟨114575005039030961344205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305533346770749230251213 114575005039030961344205)
              ·
                refine ⟨42965626889636610504077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114575005039030961344205 42965626889636610504077)
                ·
                  rfl

theorem cell19_141202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_141202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141202 prefixEnd_141202 := by exact prefixLift 141202
  have htrace : WordTrace (prefixWord ++ tailWord_141202) baseStart_141202 baseEnd_141202 := by
    simpa [prefixWord, tailWord_141202, baseEnd_141202] using wordTrace_append hprefix tailTrace_141202
  have hstable : (prefixWord ++ tailWord_141202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141202).length < 2 ^ (prefixWord ++ tailWord_141202).sum := by decide
  have hdescent : baseEnd_141202 < baseStart_141202 := by decide
  rcases family_descends (prefixWord ++ tailWord_141202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
