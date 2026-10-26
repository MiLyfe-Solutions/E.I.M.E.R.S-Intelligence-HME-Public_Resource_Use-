import V185TrunkScan22Chunk466

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4162667 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 12]
def baseStart_4162667 : Nat := 118140960795 + 4162667 * 2 ^ 59
def prefixEnd_4162667 : Nat := 4983230072969 + 3 ^ 40 * 4162667 * 2
def baseEnd_4162667 : Nat := 474988661246526728870833

theorem tailTrace_4162667 : CollatzResearch.WordTrace tailWord_4162667 prefixEnd_4162667 474988661246526728870833 := by
  unfold tailWord_4162667
  simp only [CollatzResearch.WordTrace]
  refine ⟨151824938410375860768926255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101216625606917240512617503 151824938410375860768926255)
  ·
    refine ⟨227737407615563791153389383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151824938410375860768926255 227737407615563791153389383)
    ·
      refine ⟨341606111423345686730084075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227737407615563791153389383 341606111423345686730084075)
      ·
        refine ⟨512409167135018530095126113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341606111423345686730084075 512409167135018530095126113)
        ·
          refine ⟨384306875351263897571344585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512409167135018530095126113 384306875351263897571344585)
          ·
            refine ⟨288230156513447923178508439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384306875351263897571344585 288230156513447923178508439)
            ·
              refine ⟨432345234770171884767762659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288230156513447923178508439 432345234770171884767762659)
              ·
                refine ⟨648517852155257827151643989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432345234770171884767762659 648517852155257827151643989)
                ·
                  refine ⟨474988661246526728870833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 648517852155257827151643989 474988661246526728870833)
                  ·
                    rfl

theorem cell22_4162667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_4162667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162667 prefixEnd_4162667 := by exact prefixLift 4162667
  have htrace : WordTrace (prefixWord ++ tailWord_4162667) baseStart_4162667 baseEnd_4162667 := by
    simpa [prefixWord, tailWord_4162667, baseEnd_4162667] using wordTrace_append hprefix tailTrace_4162667
  have hstable : (prefixWord ++ tailWord_4162667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162667).length < 2 ^ (prefixWord ++ tailWord_4162667).sum := by decide
  have hdescent : baseEnd_4162667 < baseStart_4162667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162684 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_4162684 : Nat := 118140960795 + 4162684 * 2 ^ 59
def prefixEnd_4162684 : Nat := 4983230072969 + 3 ^ 40 * 4162684 * 2
def baseEnd_4162684 : Nat := 474990601062332602979149

theorem tailTrace_4162684 : CollatzResearch.WordTrace tailWord_4162684 prefixEnd_4162684 474990601062332602979149 := by
  unfold tailWord_4162684
  simp only [CollatzResearch.WordTrace]
  refine ⟨75912779225657136336147553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101217038967542848448196737 75912779225657136336147553)
  ·
    refine ⟨56934584419242852252110665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75912779225657136336147553 56934584419242852252110665)
    ·
      refine ⟨42700938314432139189082999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56934584419242852252110665 42700938314432139189082999)
      ·
        refine ⟨64051407471648208783624499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42700938314432139189082999 64051407471648208783624499)
        ·
          refine ⟨96077111207472313175436749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64051407471648208783624499 96077111207472313175436749)
          ·
            refine ⟨36028916702802117440788781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96077111207472313175436749 36028916702802117440788781)
            ·
              refine ⟨13510843763550794040295793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36028916702802117440788781 13510843763550794040295793)
              ·
                refine ⟨10133132822663095530221845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13510843763550794040295793 10133132822663095530221845)
                ·
                  refine ⟨474990601062332602979149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10133132822663095530221845 474990601062332602979149)
                  ·
                    rfl

theorem cell22_4162684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_4162684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162684 prefixEnd_4162684 := by exact prefixLift 4162684
  have htrace : WordTrace (prefixWord ++ tailWord_4162684) baseStart_4162684 baseEnd_4162684 := by
    simpa [prefixWord, tailWord_4162684, baseEnd_4162684] using wordTrace_append hprefix tailTrace_4162684
  have hstable : (prefixWord ++ tailWord_4162684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162684).length < 2 ^ (prefixWord ++ tailWord_4162684).sum := by decide
  have hdescent : baseEnd_4162684 < baseStart_4162684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162718 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4162718 : Nat := 118140960795 + 4162718 * 2 ^ 59
def prefixEnd_4162718 : Nat := 4983230072969 + 3 ^ 40 * 4162718 * 2
def baseEnd_4162718 : Nat := 474994480693944351195781

theorem tailTrace_4162718 : CollatzResearch.WordTrace tailWord_4162718 prefixEnd_4162718 474994480693944351195781 := by
  unfold tailWord_4162718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978349816648887059879101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101217865688794064319355205 18978349816648887059879101)
  ·
    refine ⟨7116881181243332647454663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18978349816648887059879101 7116881181243332647454663)
    ·
      refine ⟨10675321771864998971181995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7116881181243332647454663 10675321771864998971181995)
      ·
        refine ⟨16012982657797498456772993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10675321771864998971181995 16012982657797498456772993)
        ·
          refine ⟨12009736993348123842579745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16012982657797498456772993 12009736993348123842579745)
          ·
            refine ⟨9007302745011092881934809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009736993348123842579745 9007302745011092881934809)
            ·
              refine ⟨6755477058758319661451107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9007302745011092881934809 6755477058758319661451107)
              ·
                refine ⟨10133215588137479492176661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755477058758319661451107 10133215588137479492176661)
                ·
                  refine ⟨474994480693944351195781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10133215588137479492176661 474994480693944351195781)
                  ·
                    rfl

theorem cell22_4162718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4162718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162718 prefixEnd_4162718 := by exact prefixLift 4162718
  have htrace : WordTrace (prefixWord ++ tailWord_4162718) baseStart_4162718 baseEnd_4162718 := by
    simpa [prefixWord, tailWord_4162718, baseEnd_4162718] using wordTrace_append hprefix tailTrace_4162718
  have hstable : (prefixWord ++ tailWord_4162718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162718).length < 2 ^ (prefixWord ++ tailWord_4162718).sum := by decide
  have hdescent : baseEnd_4162718 < baseStart_4162718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162806 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4162806 : Nat := 118140960795 + 4162806 * 2 ^ 59
def prefixEnd_4162806 : Nat := 4983230072969 + 3 ^ 40 * 4162806 * 2
def baseEnd_4162806 : Nat := 1425013566280230157387073

theorem tailTrace_4162806 : CollatzResearch.WordTrace tailWord_4162806 prefixEnd_4162806 1425013566280230157387073 := by
  unfold tailWord_4162806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9489375509804517969264767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101220005437914858338824181 9489375509804517969264767)
  ·
    refine ⟨14234063264706776953897151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9489375509804517969264767 14234063264706776953897151)
    ·
      refine ⟨21351094897060165430845727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14234063264706776953897151 21351094897060165430845727)
      ·
        refine ⟨32026642345590248146268591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21351094897060165430845727 32026642345590248146268591)
        ·
          refine ⟨48039963518385372219402887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32026642345590248146268591 48039963518385372219402887)
          ·
            refine ⟨72059945277578058329104331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48039963518385372219402887 72059945277578058329104331)
            ·
              refine ⟨108089917916367087493656497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72059945277578058329104331 108089917916367087493656497)
              ·
                refine ⟨81067438437275315620242373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108089917916367087493656497 81067438437275315620242373)
                ·
                  refine ⟨15200144706989121678795445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81067438437275315620242373 15200144706989121678795445)
                  ·
                    refine ⟨1425013566280230157387073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15200144706989121678795445 1425013566280230157387073)
                    ·
                      rfl

theorem cell22_4162806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4162806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162806 prefixEnd_4162806 := by exact prefixLift 4162806
  have htrace : WordTrace (prefixWord ++ tailWord_4162806) baseStart_4162806 baseEnd_4162806 := by
    simpa [prefixWord, tailWord_4162806, baseEnd_4162806] using wordTrace_append hprefix tailTrace_4162806
  have hstable : (prefixWord ++ tailWord_4162806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162806).length < 2 ^ (prefixWord ++ tailWord_4162806).sum := by decide
  have hdescent : baseEnd_4162806 < baseStart_4162806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162851 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 1, 5]
def baseStart_4162851 : Nat := 118140960795 + 4162851 * 2 ^ 59
def prefixEnd_4162851 : Nat := 4983230072969 + 3 ^ 40 * 4162851 * 2
def baseEnd_4162851 : Nat := 1425028970699865040011935

theorem tailTrace_4162851 : CollatzResearch.WordTrace tailWord_4162851 prefixEnd_4162851 1425028970699865040011935 := by
  unfold tailWord_4162851
  simp only [CollatzResearch.WordTrace]
  refine ⟨151831649441709260193624407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101221099627806173462416271 151831649441709260193624407)
  ·
    refine ⟨227747474162563890290436611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151831649441709260193624407 227747474162563890290436611)
    ·
      refine ⟨341621211243845835435654917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227747474162563890290436611 341621211243845835435654917)
      ·
        refine ⟨64053977108221094144185297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341621211243845835435654917 64053977108221094144185297)
        ·
          refine ⟨48040482831165820608138973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64053977108221094144185297 48040482831165820608138973)
          ·
            refine ⟨18015181061687182728052115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48040482831165820608138973 18015181061687182728052115)
            ·
              refine ⟨27022771592530774092078173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18015181061687182728052115 27022771592530774092078173)
              ·
                refine ⟨10133539347199040284529315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27022771592530774092078173 10133539347199040284529315)
                ·
                  refine ⟨15200309020798560426793973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10133539347199040284529315 15200309020798560426793973)
                  ·
                    refine ⟨1425028970699865040011935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15200309020798560426793973 1425028970699865040011935)
                    ·
                      rfl

theorem cell22_4162851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_4162851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162851 prefixEnd_4162851 := by exact prefixLift 4162851
  have htrace : WordTrace (prefixWord ++ tailWord_4162851) baseStart_4162851 baseEnd_4162851 := by
    simpa [prefixWord, tailWord_4162851, baseEnd_4162851] using wordTrace_append hprefix tailTrace_4162851
  have hstable : (prefixWord ++ tailWord_4162851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162851).length < 2 ^ (prefixWord ++ tailWord_4162851).sum := by decide
  have hdescent : baseEnd_4162851 < baseStart_4162851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162868 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4162868 : Nat := 118140960795 + 4162868 * 2 ^ 59
def prefixEnd_4162868 : Nat := 4983230072969 + 3 ^ 40 * 4162868 * 2
def baseEnd_4162868 : Nat := 1425034790147282662336883

theorem tailTrace_4162868 : CollatzResearch.WordTrace tailWord_4162868 prefixEnd_4162868 1425034790147282662336883 := by
  unfold tailWord_4162868
  simp only [CollatzResearch.WordTrace]
  refine ⟨75916134741323836048496629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101221512988431781397995505 75916134741323836048496629)
  ·
    refine ⟨7117137631999109629546559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75916134741323836048496629 7117137631999109629546559)
    ·
      refine ⟨10675706447998664444319839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117137631999109629546559 10675706447998664444319839)
      ·
        refine ⟨16013559671997996666479759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10675706447998664444319839 16013559671997996666479759)
        ·
          refine ⟨24020339507996994999719639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16013559671997996666479759 24020339507996994999719639)
          ·
            refine ⟨36030509261995492499579459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24020339507996994999719639 36030509261995492499579459)
            ·
              refine ⟨54045763892993238749369189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36030509261995492499579459 54045763892993238749369189)
              ·
                refine ⟨10133580729936232265506723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54045763892993238749369189 10133580729936232265506723)
                ·
                  refine ⟨15200371094904348398260085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10133580729936232265506723 15200371094904348398260085)
                  ·
                    refine ⟨1425034790147282662336883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15200371094904348398260085 1425034790147282662336883)
                    ·
                      rfl

theorem cell22_4162868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4162868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162868 prefixEnd_4162868 := by exact prefixLift 4162868
  have htrace : WordTrace (prefixWord ++ tailWord_4162868) baseStart_4162868 baseEnd_4162868 := by
    simpa [prefixWord, tailWord_4162868, baseEnd_4162868] using wordTrace_append hprefix tailTrace_4162868
  have hstable : (prefixWord ++ tailWord_4162868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162868).length < 2 ^ (prefixWord ++ tailWord_4162868).sum := by decide
  have hdescent : baseEnd_4162868 < baseStart_4162868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163005 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 4]
def baseStart_4163005 : Nat := 118140960795 + 4163005 * 2 ^ 59
def prefixEnd_4163005 : Nat := 4983230072969 + 3 ^ 40 * 4163005 * 2
def baseEnd_4163005 : Nat := 475027229349019990553821

theorem tailTrace_4163005 : CollatzResearch.WordTrace tailWord_4163005 prefixEnd_4163005 475027229349019990553821 := by
  unfold tailWord_4163005
  simp only [CollatzResearch.WordTrace]
  refine ⟨151837266283151344494730469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101224844188767562996486979 151837266283151344494730469)
  ·
    refine ⟨28469487428090877092761963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151837266283151344494730469 28469487428090877092761963)
    ·
      refine ⟨42704231142136315639142945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28469487428090877092761963 42704231142136315639142945)
      ·
        refine ⟨32028173356602236729357209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42704231142136315639142945 32028173356602236729357209)
        ·
          refine ⟨24021130017451677547017907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32028173356602236729357209 24021130017451677547017907)
          ·
            refine ⟨36031695026177516320526861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24021130017451677547017907 36031695026177516320526861)
            ·
              refine ⟨13511885634816568620197573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36031695026177516320526861 13511885634816568620197573)
              ·
                refine ⟨2533478556528106616287045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13511885634816568620197573 2533478556528106616287045)
                ·
                  refine ⟨475027229349019990553821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533478556528106616287045 475027229349019990553821)
                  ·
                    rfl

theorem cell22_4163005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_4163005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163005 prefixEnd_4163005 := by exact prefixLift 4163005
  have htrace : WordTrace (prefixWord ++ tailWord_4163005) baseStart_4163005 baseEnd_4163005 := by
    simpa [prefixWord, tailWord_4163005, baseEnd_4163005] using wordTrace_append hprefix tailTrace_4163005
  have hstable : (prefixWord ++ tailWord_4163005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163005).length < 2 ^ (prefixWord ++ tailWord_4163005).sum := by decide
  have hdescent : baseEnd_4163005 < baseStart_4163005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163020 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_4163020 : Nat := 118140960795 + 4163020 * 2 ^ 59
def prefixEnd_4163020 : Nat := 4983230072969 + 3 ^ 40 * 4163020 * 2
def baseEnd_4163020 : Nat := 1425086822853604932536417

theorem tailTrace_4163020 : CollatzResearch.WordTrace tailWord_4163020 prefixEnd_4163020 1425086822853604932536417 := by
  unfold tailWord_4163020
  simp only [CollatzResearch.WordTrace]
  refine ⟨75918906689048501028263257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101225208918731334704351009 75918906689048501028263257)
  ·
    refine ⟨56939180016786375771197443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75918906689048501028263257 56939180016786375771197443)
    ·
      refine ⟨85408770025179563656796165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56939180016786375771197443 85408770025179563656796165)
      ·
        refine ⟨16014144379721168185649281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85408770025179563656796165 16014144379721168185649281)
        ·
          refine ⟨12010608284790876139236961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16014144379721168185649281 12010608284790876139236961)
          ·
            refine ⟨9007956213593157104427721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12010608284790876139236961 9007956213593157104427721)
            ·
              refine ⟨6755967160194867828320791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9007956213593157104427721 6755967160194867828320791)
              ·
                refine ⟨10133950740292301742481187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755967160194867828320791 10133950740292301742481187)
                ·
                  refine ⟨15200926110438452613721781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10133950740292301742481187 15200926110438452613721781)
                  ·
                    refine ⟨1425086822853604932536417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15200926110438452613721781 1425086822853604932536417)
                    ·
                      rfl

theorem cell22_4163020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_4163020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163020 prefixEnd_4163020 := by exact prefixLift 4163020
  have htrace : WordTrace (prefixWord ++ tailWord_4163020) baseStart_4163020 baseEnd_4163020 := by
    simpa [prefixWord, tailWord_4163020, baseEnd_4163020] using wordTrace_append hprefix tailTrace_4163020
  have hstable : (prefixWord ++ tailWord_4163020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163020).length < 2 ^ (prefixWord ++ tailWord_4163020).sum := by decide
  have hdescent : baseEnd_4163020 < baseStart_4163020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163172 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_4163172 : Nat := 118140960795 + 4163172 * 2 ^ 59
def prefixEnd_4163172 : Nat := 4983230072969 + 3 ^ 40 * 4163172 * 2
def baseEnd_4163172 : Nat := 1425138855559927202735951

theorem tailTrace_4163172 : CollatzResearch.WordTrace tailWord_4163172 prefixEnd_4163172 1425138855559927202735951 := by
  unfold tailWord_4163172
  simp only [CollatzResearch.WordTrace]
  refine ⟨75921678636773166008029885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101228904849030888010706513 75921678636773166008029885)
  ·
    refine ⟨28470629488789937253011207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75921678636773166008029885 28470629488789937253011207)
    ·
      refine ⟨42705944233184905879516811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28470629488789937253011207 42705944233184905879516811)
      ·
        refine ⟨64058916349777358819275217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42705944233184905879516811 64058916349777358819275217)
        ·
          refine ⟨48044187262333019114456413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64058916349777358819275217 48044187262333019114456413)
          ·
            refine ⟨18016570223374882167921155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48044187262333019114456413 18016570223374882167921155)
            ·
              refine ⟨27024855335062323251881733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18016570223374882167921155 27024855335062323251881733)
              ·
                refine ⟨5067160375324185609727825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27024855335062323251881733 5067160375324185609727825)
                ·
                  refine ⟨3800370281493139207295869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067160375324185609727825 3800370281493139207295869)
                  ·
                    refine ⟨1425138855559927202735951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800370281493139207295869 1425138855559927202735951)
                    ·
                      rfl

theorem cell22_4163172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_4163172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163172 prefixEnd_4163172 := by exact prefixLift 4163172
  have htrace : WordTrace (prefixWord ++ tailWord_4163172) baseStart_4163172 baseEnd_4163172 := by
    simpa [prefixWord, tailWord_4163172, baseEnd_4163172] using wordTrace_append hprefix tailTrace_4163172
  have hstable : (prefixWord ++ tailWord_4163172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163172).length < 2 ^ (prefixWord ++ tailWord_4163172).sum := by decide
  have hdescent : baseEnd_4163172 < baseStart_4163172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163183 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_4163183 : Nat := 118140960795 + 4163183 * 2 ^ 59
def prefixEnd_4163183 : Nat := 4983230072969 + 3 ^ 40 * 4163183 * 2
def baseEnd_4163183 : Nat := 1425142621084726840710917

theorem tailTrace_4163183 : CollatzResearch.WordTrace tailWord_4163183 prefixEnd_4163183 1425142621084726840710917 := by
  unfold tailWord_4163183
  simp only [CollatzResearch.WordTrace]
  refine ⟨151843758476506480894710203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101229172317670987263140135 151843758476506480894710203)
  ·
    refine ⟨227765637714759721342065305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151843758476506480894710203 227765637714759721342065305)
    ·
      refine ⟨170824228286069791006548979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227765637714759721342065305 170824228286069791006548979)
      ·
        refine ⟨256236342429104686509823469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170824228286069791006548979 256236342429104686509823469)
        ·
          refine ⟨96088628410914257441183801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256236342429104686509823469 96088628410914257441183801)
          ·
            refine ⟨72066471308185693080887851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96088628410914257441183801 72066471308185693080887851)
            ·
              refine ⟨108099706962278539621331777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72066471308185693080887851 108099706962278539621331777)
              ·
                refine ⟨81074780221708904715998833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108099706962278539621331777 81074780221708904715998833)
                ·
                  refine ⟨60806085166281678536999125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81074780221708904715998833 60806085166281678536999125)
                  ·
                    refine ⟨1425142621084726840710917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60806085166281678536999125 1425142621084726840710917)
                    ·
                      rfl

theorem cell22_4163183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_4163183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163183 prefixEnd_4163183 := by exact prefixLift 4163183
  have htrace : WordTrace (prefixWord ++ tailWord_4163183) baseStart_4163183 baseEnd_4163183 := by
    simpa [prefixWord, tailWord_4163183, baseEnd_4163183] using wordTrace_append hprefix tailTrace_4163183
  have hstable : (prefixWord ++ tailWord_4163183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163183).length < 2 ^ (prefixWord ++ tailWord_4163183).sum := by decide
  have hdescent : baseEnd_4163183 < baseStart_4163183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163189 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_4163189 : Nat := 118140960795 + 4163189 * 2 ^ 59
def prefixEnd_4163189 : Nat := 4983230072969 + 3 ^ 40 * 4163189 * 2
def baseEnd_4163189 : Nat := 1425144675007344825060899

theorem tailTrace_4163189 : CollatzResearch.WordTrace tailWord_4163189 prefixEnd_4163189 1425144675007344825060899 := by
  unfold tailWord_4163189
  simp only [CollatzResearch.WordTrace]
  refine ⟨151843977314484743919428621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101229318209656495946285747 151843977314484743919428621)
  ·
    refine ⟨56941491492931778969785733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151843977314484743919428621 56941491492931778969785733)
    ·
      refine ⟨10676529654924708556834825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56941491492931778969785733 10676529654924708556834825)
      ·
        refine ⟨8007397241193531417626119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10676529654924708556834825 8007397241193531417626119)
        ·
          refine ⟨12011095861790297126439179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007397241193531417626119 12011095861790297126439179)
          ·
            refine ⟨18016643792685445689658769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011095861790297126439179 18016643792685445689658769)
            ·
              refine ⟨13512482844514084267244077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18016643792685445689658769 13512482844514084267244077)
              ·
                refine ⟨5067181066692781600216529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13512482844514084267244077 5067181066692781600216529)
                ·
                  refine ⟨3800385800019586200162397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067181066692781600216529 3800385800019586200162397)
                  ·
                    refine ⟨1425144675007344825060899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800385800019586200162397 1425144675007344825060899)
                    ·
                      rfl

theorem cell22_4163189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_4163189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163189 prefixEnd_4163189 := by exact prefixLift 4163189
  have htrace : WordTrace (prefixWord ++ tailWord_4163189) baseStart_4163189 baseEnd_4163189 := by
    simpa [prefixWord, tailWord_4163189, baseEnd_4163189] using wordTrace_append hprefix tailTrace_4163189
  have hstable : (prefixWord ++ tailWord_4163189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163189).length < 2 ^ (prefixWord ++ tailWord_4163189).sum := by decide
  have hdescent : baseEnd_4163189 < baseStart_4163189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163204 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_4163204 : Nat := 118140960795 + 4163204 * 2 ^ 59
def prefixEnd_4163204 : Nat := 4983230072969 + 3 ^ 40 * 4163204 * 2
def baseEnd_4163204 : Nat := 1425149809813889785935853

theorem tailTrace_4163204 : CollatzResearch.WordTrace tailWord_4163204 prefixEnd_4163204 1425149809813889785935853 := by
  unfold tailWord_4163204
  simp only [CollatzResearch.WordTrace]
  refine ⟨75922262204715200740612333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101229682939620267654149777 75922262204715200740612333)
  ·
    refine ⟨28470848326768200277729625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75922262204715200740612333 28470848326768200277729625)
    ·
      refine ⟨21353136245076150208297219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28470848326768200277729625 21353136245076150208297219)
      ·
        refine ⟨32029704367614225312445829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21353136245076150208297219 32029704367614225312445829)
        ·
          refine ⟨6005569568927667246083593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32029704367614225312445829 6005569568927667246083593)
          ·
            refine ⟨4504177176695750434562695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6005569568927667246083593 4504177176695750434562695)
            ·
              refine ⟨6756265765043625651844043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504177176695750434562695 6756265765043625651844043)
              ·
                refine ⟨10134398647565438477766065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756265765043625651844043 10134398647565438477766065)
                ·
                  refine ⟨7600798985674078858324549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10134398647565438477766065 7600798985674078858324549)
                  ·
                    refine ⟨1425149809813889785935853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7600798985674078858324549 1425149809813889785935853)
                    ·
                      rfl

theorem cell22_4163204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_4163204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163204 prefixEnd_4163204 := by exact prefixLift 4163204
  have htrace : WordTrace (prefixWord ++ tailWord_4163204) baseStart_4163204 baseEnd_4163204 := by
    simpa [prefixWord, tailWord_4163204, baseEnd_4163204] using wordTrace_append hprefix tailTrace_4163204
  have hstable : (prefixWord ++ tailWord_4163204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163204).length < 2 ^ (prefixWord ++ tailWord_4163204).sum := by decide
  have hdescent : baseEnd_4163204 < baseStart_4163204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163240 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4163240 : Nat := 118140960795 + 4163240 * 2 ^ 59
def prefixEnd_4163240 : Nat := 4983230072969 + 3 ^ 40 * 4163240 * 2
def baseEnd_4163240 : Nat := 1425162133349597692035743

theorem tailTrace_4163240 : CollatzResearch.WordTrace tailWord_4163240 prefixEnd_4163240 1425162133349597692035743 := by
  unfold tailWord_4163240
  simp only [CollatzResearch.WordTrace]
  refine ⟨75922918718649989814767587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101230558291533319753023449 75922918718649989814767587)
  ·
    refine ⟨113884378077974984722151381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75922918718649989814767587 113884378077974984722151381)
    ·
      refine ⟨2669165111202538704425423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 113884378077974984722151381 2669165111202538704425423)
      ·
        refine ⟨4003747666803808056638135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669165111202538704425423 4003747666803808056638135)
        ·
          refine ⟨6005621500205712084957203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003747666803808056638135 6005621500205712084957203)
          ·
            refine ⟨9008432250308568127435805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005621500205712084957203 9008432250308568127435805)
            ·
              refine ⟨3378162093865713047788427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9008432250308568127435805 3378162093865713047788427)
              ·
                refine ⟨5067243140798569571682641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378162093865713047788427 5067243140798569571682641)
                ·
                  refine ⟨3800432355598927178761981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067243140798569571682641 3800432355598927178761981)
                  ·
                    refine ⟨1425162133349597692035743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800432355598927178761981 1425162133349597692035743)
                    ·
                      rfl

theorem cell22_4163240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4163240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163240 prefixEnd_4163240 := by exact prefixLift 4163240
  have htrace : WordTrace (prefixWord ++ tailWord_4163240) baseStart_4163240 baseEnd_4163240 := by
    simpa [prefixWord, tailWord_4163240, baseEnd_4163240] using wordTrace_append hprefix tailTrace_4163240
  have hstable : (prefixWord ++ tailWord_4163240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163240).length < 2 ^ (prefixWord ++ tailWord_4163240).sum := by decide
  have hdescent : baseEnd_4163240 < baseStart_4163240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163247 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 5]
def baseStart_4163247 : Nat := 118140960795 + 4163247 * 2 ^ 59
def prefixEnd_4163247 : Nat := 4983230072969 + 3 ^ 40 * 4163247 * 2
def baseEnd_4163247 : Nat := 475054843197550669036907

theorem tailTrace_4163247 : CollatzResearch.WordTrace tailWord_4163247 prefixEnd_4163247 475054843197550669036907 := by
  unfold tailWord_4163247
  simp only [CollatzResearch.WordTrace]
  refine ⟨151846092748274619825039995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101230728498849746550026663 151846092748274619825039995)
  ·
    refine ⟨227769139122411929737559993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151846092748274619825039995 227769139122411929737559993)
    ·
      refine ⟨170826854341808947303169995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227769139122411929737559993 170826854341808947303169995)
      ·
        refine ⟨256240281512713420954754993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170826854341808947303169995 256240281512713420954754993)
        ·
          refine ⟨192180211134535065716066245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256240281512713420954754993 192180211134535065716066245)
          ·
            refine ⟨36033789587725324821762421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192180211134535065716066245 36033789587725324821762421)
            ·
              refine ⟨3378167773849249202040227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36033789587725324821762421 3378167773849249202040227)
              ·
                refine ⟨5067251660773873803060341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378167773849249202040227 5067251660773873803060341)
                ·
                  refine ⟨475054843197550669036907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5067251660773873803060341 475054843197550669036907)
                  ·
                    rfl

theorem cell22_4163247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 5].length) (baseStart_4163247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163247 prefixEnd_4163247 := by exact prefixLift 4163247
  have htrace : WordTrace (prefixWord ++ tailWord_4163247) baseStart_4163247 baseEnd_4163247 := by
    simpa [prefixWord, tailWord_4163247, baseEnd_4163247] using wordTrace_append hprefix tailTrace_4163247
  have hstable : (prefixWord ++ tailWord_4163247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163247).length < 2 ^ (prefixWord ++ tailWord_4163247).sum := by decide
  have hdescent : baseEnd_4163247 < baseStart_4163247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163305 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_4163305 : Nat := 118140960795 + 4163305 * 2 ^ 59
def prefixEnd_4163305 : Nat := 4983230072969 + 3 ^ 40 * 4163305 * 2
def baseEnd_4163305 : Nat := 1425184384177959189160543

theorem tailTrace_4163305 : CollatzResearch.WordTrace tailWord_4163305 prefixEnd_4163305 1425184384177959189160543 := by
  unfold tailWord_4163305
  simp only [CollatzResearch.WordTrace]
  refine ⟨151848208182064495730651369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101232138788042997153767579 151848208182064495730651369)
  ·
    refine ⟨113886156136548371797988527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151848208182064495730651369 113886156136548371797988527)
    ·
      refine ⟨170829234204822557696982791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113886156136548371797988527 170829234204822557696982791)
      ·
        refine ⟨256243851307233836545474187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170829234204822557696982791 256243851307233836545474187)
        ·
          refine ⟨384365776960850754818211281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256243851307233836545474187 384365776960850754818211281)
          ·
            refine ⟨288274332720638066113658461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384365776960850754818211281 288274332720638066113658461)
            ·
              refine ⟨108102874770239274792621923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288274332720638066113658461 108102874770239274792621923)
              ·
                refine ⟨162154312155358912188932885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108102874770239274792621923 162154312155358912188932885)
                ·
                  refine ⟨7600983382282449008856229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162154312155358912188932885 7600983382282449008856229)
                  ·
                    refine ⟨1425184384177959189160543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7600983382282449008856229 1425184384177959189160543)
                    ·
                      rfl

theorem cell22_4163305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_4163305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163305 prefixEnd_4163305 := by exact prefixLift 4163305
  have htrace : WordTrace (prefixWord ++ tailWord_4163305) baseStart_4163305 baseEnd_4163305 := by
    simpa [prefixWord, tailWord_4163305, baseEnd_4163305] using wordTrace_append hprefix tailTrace_4163305
  have hstable : (prefixWord ++ tailWord_4163305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163305).length < 2 ^ (prefixWord ++ tailWord_4163305).sum := by decide
  have hdescent : baseEnd_4163305 < baseStart_4163305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163358 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4163358 : Nat := 118140960795 + 4163358 * 2 ^ 59
def prefixEnd_4163358 : Nat := 4983230072969 + 3 ^ 40 * 4163358 * 2
def baseEnd_4163358 : Nat := 1425202527161084717585381

theorem tailTrace_4163358 : CollatzResearch.WordTrace tailWord_4163358 prefixEnd_4163358 1425202527161084717585381 := by
  unfold tailWord_4163358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18981267656359060722791341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101233427500581657188220485 18981267656359060722791341)
  ·
    refine ⟨7117975371134647771046753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18981267656359060722791341 7117975371134647771046753)
    ·
      refine ⟨5338481528350985828285065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7117975371134647771046753 5338481528350985828285065)
      ·
        refine ⟨4003861146263239371213799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5338481528350985828285065 4003861146263239371213799)
        ·
          refine ⟨6005791719394859056820699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003861146263239371213799 6005791719394859056820699)
          ·
            refine ⟨9008687579092288585231049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005791719394859056820699 9008687579092288585231049)
            ·
              refine ⟨6756515684319216438923287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9008687579092288585231049 6756515684319216438923287)
              ·
                refine ⟨10134773526478824658384931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756515684319216438923287 10134773526478824658384931)
                ·
                  refine ⟨15202160289718236987577397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134773526478824658384931 15202160289718236987577397)
                  ·
                    refine ⟨1425202527161084717585381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15202160289718236987577397 1425202527161084717585381)
                    ·
                      rfl

theorem cell22_4163358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4163358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163358 prefixEnd_4163358 := by exact prefixLift 4163358
  have htrace : WordTrace (prefixWord ++ tailWord_4163358) baseStart_4163358 baseEnd_4163358 := by
    simpa [prefixWord, tailWord_4163358, baseEnd_4163358] using wordTrace_append hprefix tailTrace_4163358
  have hstable : (prefixWord ++ tailWord_4163358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163358).length < 2 ^ (prefixWord ++ tailWord_4163358).sum := by decide
  have hdescent : baseEnd_4163358 < baseStart_4163358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163386 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_4163386 : Nat := 118140960795 + 4163386 * 2 ^ 59
def prefixEnd_4163386 : Nat := 4983230072969 + 3 ^ 40 * 4163386 * 2
def baseEnd_4163386 : Nat := 1425212112133301977885295

theorem tailTrace_4163386 : CollatzResearch.WordTrace tailWord_4163386 prefixEnd_4163386 1425212112133301977885295 := by
  unfold tailWord_4163386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37962790623692761641087503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101234108329847364376233341 37962790623692761641087503)
  ·
    refine ⟨56944185935539142461631255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37962790623692761641087503 56944185935539142461631255)
    ·
      refine ⟨85416278903308713692446883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56944185935539142461631255 85416278903308713692446883)
      ·
        refine ⟨128124418354963070538670325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85416278903308713692446883 128124418354963070538670325)
        ·
          refine ⟨12011664220777787863000343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128124418354963070538670325 12011664220777787863000343)
          ·
            refine ⟨18017496331166681794500515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011664220777787863000343 18017496331166681794500515)
            ·
              refine ⟨27026244496750022691750773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18017496331166681794500515 27026244496750022691750773)
              ·
                refine ⟨2533710421570314627351635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27026244496750022691750773 2533710421570314627351635)
                ·
                  refine ⟨3800565632355471941027453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533710421570314627351635 3800565632355471941027453)
                  ·
                    refine ⟨1425212112133301977885295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800565632355471941027453 1425212112133301977885295)
                    ·
                      rfl

theorem cell22_4163386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_4163386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163386 prefixEnd_4163386 := by exact prefixLift 4163386
  have htrace : WordTrace (prefixWord ++ tailWord_4163386) baseStart_4163386 baseEnd_4163386 := by
    simpa [prefixWord, tailWord_4163386, baseEnd_4163386] using wordTrace_append hprefix tailTrace_4163386
  have hstable : (prefixWord ++ tailWord_4163386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163386).length < 2 ^ (prefixWord ++ tailWord_4163386).sum := by decide
  have hdescent : baseEnd_4163386 < baseStart_4163386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163442 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_4163442 : Nat := 118140960795 + 4163442 * 2 ^ 59
def prefixEnd_4163442 : Nat := 4983230072969 + 3 ^ 40 * 4163442 * 2
def baseEnd_4163442 : Nat := 1425231282077736498485123

theorem tailTrace_4163442 : CollatzResearch.WordTrace tailWord_4163442 prefixEnd_4163442 1425231282077736498485123 := by
  unfold tailWord_4163442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37963301245642042032097145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101235469988378778752259053 37963301245642042032097145)
  ·
    refine ⟨28472475934231531524072859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37963301245642042032097145 28472475934231531524072859)
    ·
      refine ⟨42708713901347297286109289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28472475934231531524072859 42708713901347297286109289)
      ·
        refine ⟨32031535426010472964581967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42708713901347297286109289 32031535426010472964581967)
        ·
          refine ⟨48047303139015709446872951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32031535426010472964581967 48047303139015709446872951)
          ·
            refine ⟨72070954708523564170309427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48047303139015709446872951 72070954708523564170309427)
            ·
              refine ⟨108106432062785346255464141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72070954708523564170309427 108106432062785346255464141)
              ·
                refine ⟨40539912023544504845799053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108106432062785346255464141 40539912023544504845799053)
                ·
                  refine ⟨15202467008829189317174645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40539912023544504845799053 15202467008829189317174645)
                  ·
                    refine ⟨1425231282077736498485123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15202467008829189317174645 1425231282077736498485123)
                    ·
                      rfl

theorem cell22_4163442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_4163442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163442 prefixEnd_4163442 := by exact prefixLift 4163442
  have htrace : WordTrace (prefixWord ++ tailWord_4163442) baseStart_4163442 baseEnd_4163442 := by
    simpa [prefixWord, tailWord_4163442, baseEnd_4163442] using wordTrace_append hprefix tailTrace_4163442
  have hstable : (prefixWord ++ tailWord_4163442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163442).length < 2 ^ (prefixWord ++ tailWord_4163442).sum := by decide
  have hdescent : baseEnd_4163442 < baseStart_4163442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163459 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 4, 3]
def baseStart_4163459 : Nat := 118140960795 + 4163459 * 2 ^ 59
def prefixEnd_4163459 : Nat := 4983230072969 + 3 ^ 40 * 4163459 * 2
def baseEnd_4163459 : Nat := 1425237101525154120810071

theorem tailTrace_4163459 : CollatzResearch.WordTrace tailWord_4163459 prefixEnd_4163459 1425237101525154120810071 := by
  unfold tailWord_4163459
  simp only [CollatzResearch.WordTrace]
  refine ⟨151853825023506580031757431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101235883349004386687838287 151853825023506580031757431)
  ·
    refine ⟨227780737535259870047636147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151853825023506580031757431 227780737535259870047636147)
    ·
      refine ⟨341671106302889805071454221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227780737535259870047636147 341671106302889805071454221)
      ·
        refine ⟨128126664863583676901795333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341671106302889805071454221 128126664863583676901795333)
        ·
          refine ⟨24023749661921939419086625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128126664863583676901795333 24023749661921939419086625)
          ·
            refine ⟨18017812246441454564314969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24023749661921939419086625 18017812246441454564314969)
            ·
              refine ⟨13513359184831090923236227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18017812246441454564314969 13513359184831090923236227)
              ·
                refine ⟨20270038777246636384854341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513359184831090923236227 20270038777246636384854341)
                ·
                  refine ⟨3800632270733744322160189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20270038777246636384854341 3800632270733744322160189)
                  ·
                    refine ⟨1425237101525154120810071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800632270733744322160189 1425237101525154120810071)
                    ·
                      rfl

theorem cell22_4163459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 3].length) (baseStart_4163459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163459 prefixEnd_4163459 := by exact prefixLift 4163459
  have htrace : WordTrace (prefixWord ++ tailWord_4163459) baseStart_4163459 baseEnd_4163459 := by
    simpa [prefixWord, tailWord_4163459, baseEnd_4163459] using wordTrace_append hprefix tailTrace_4163459
  have hstable : (prefixWord ++ tailWord_4163459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163459).length < 2 ^ (prefixWord ++ tailWord_4163459).sum := by decide
  have hdescent : baseEnd_4163459 < baseStart_4163459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163461 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 4]
def baseStart_4163461 : Nat := 118140960795 + 4163461 * 2 ^ 59
def prefixEnd_4163461 : Nat := 4983230072969 + 3 ^ 40 * 4163461 * 2
def baseEnd_4163461 : Nat := 475079262055342260753355

theorem tailTrace_4163461 : CollatzResearch.WordTrace tailWord_4163461 prefixEnd_4163461 475079262055342260753355 := by
  unfold tailWord_4163461
  simp only [CollatzResearch.WordTrace]
  refine ⟨151853897969499334373330237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101235931979666222915553491 151853897969499334373330237)
  ·
    refine ⟨56945211738562250389998839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151853897969499334373330237 56945211738562250389998839)
    ·
      refine ⟨85417817607843375584998259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56945211738562250389998839 85417817607843375584998259)
      ·
        refine ⟨128126726411765063377497389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85417817607843375584998259 128126726411765063377497389)
        ·
          refine ⟨48047522404411898766561521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128126726411765063377497389 48047522404411898766561521)
          ·
            refine ⟨36035641803308924074921141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48047522404411898766561521 36035641803308924074921141)
            ·
              refine ⟨3378341419060211632023857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36035641803308924074921141 3378341419060211632023857)
              ·
                refine ⟨2533756064295158724017893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378341419060211632023857 2533756064295158724017893)
                ·
                  refine ⟨475079262055342260753355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533756064295158724017893 475079262055342260753355)
                  ·
                    rfl

theorem cell22_4163461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_4163461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163461 prefixEnd_4163461 := by exact prefixLift 4163461
  have htrace : WordTrace (prefixWord ++ tailWord_4163461) baseStart_4163461 baseEnd_4163461 := by
    simpa [prefixWord, tailWord_4163461, baseEnd_4163461] using wordTrace_append hprefix tailTrace_4163461
  have hstable : (prefixWord ++ tailWord_4163461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163461).length < 2 ^ (prefixWord ++ tailWord_4163461).sum := by decide
  have hdescent : baseEnd_4163461 < baseStart_4163461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163480 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 1, 4]
def baseStart_4163480 : Nat := 118140960795 + 4163480 * 2 ^ 59
def prefixEnd_4163480 : Nat := 4983230072969 + 3 ^ 40 * 4163480 * 2
def baseEnd_4163480 : Nat := 1425244290254317066035007

theorem tailTrace_4163480 : CollatzResearch.WordTrace tailWord_4163480 prefixEnd_4163480 1425244290254317066035007 := by
  unfold tailWord_4163480
  simp only [CollatzResearch.WordTrace]
  refine ⟨75927295478215250309135947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101236393970953667078847929 75927295478215250309135947)
  ·
    refine ⟨113890943217322875463703921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75927295478215250309135947 113890943217322875463703921)
    ·
      refine ⟨85418207412992156597777941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113890943217322875463703921 85418207412992156597777941)
      ·
        refine ⟨4003978472484007340520841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85418207412992156597777941 4003978472484007340520841)
        ·
          refine ⟨3002983854363005505390631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4003978472484007340520841 3002983854363005505390631)
          ·
            refine ⟨4504475781544508258085947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002983854363005505390631 4504475781544508258085947)
            ·
              refine ⟨6756713672316762387128921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504475781544508258085947 6756713672316762387128921)
              ·
                refine ⟨5067535254237571790346691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756713672316762387128921 5067535254237571790346691)
                ·
                  refine ⟨7601302881356357685520037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067535254237571790346691 7601302881356357685520037)
                  ·
                    refine ⟨1425244290254317066035007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601302881356357685520037 1425244290254317066035007)
                    ·
                      rfl

theorem cell22_4163480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_4163480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163480 prefixEnd_4163480 := by exact prefixLift 4163480
  have htrace : WordTrace (prefixWord ++ tailWord_4163480) baseStart_4163480 baseEnd_4163480 := by
    simpa [prefixWord, tailWord_4163480, baseEnd_4163480] using wordTrace_append hprefix tailTrace_4163480
  have hstable : (prefixWord ++ tailWord_4163480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163480).length < 2 ^ (prefixWord ++ tailWord_4163480).sum := by decide
  have hdescent : baseEnd_4163480 < baseStart_4163480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163534 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_4163534 : Nat := 118140960795 + 4163534 * 2 ^ 59
def prefixEnd_4163534 : Nat := 4983230072969 + 3 ^ 40 * 4163534 * 2
def baseEnd_4163534 : Nat := 475087591852626308394947

theorem tailTrace_4163534 : CollatzResearch.WordTrace tailWord_4163534 prefixEnd_4163534 475087591852626308394947 := by
  unfold tailWord_4163534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982070062279358480092207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101237706998823245227158437 18982070062279358480092207)
  ·
    refine ⟨28473105093419037720138311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18982070062279358480092207 28473105093419037720138311)
    ·
      refine ⟨42709657640128556580207467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28473105093419037720138311 42709657640128556580207467)
      ·
        refine ⟨64064486460192834870311201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42709657640128556580207467 64064486460192834870311201)
        ·
          refine ⟨48048364845144626152733401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64064486460192834870311201 48048364845144626152733401)
          ·
            refine ⟨36036273633858469614550051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48048364845144626152733401 36036273633858469614550051)
            ·
              refine ⟨54054410450787704421825077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36036273633858469614550051 54054410450787704421825077)
              ·
                refine ⟨5067600979761347289546101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54054410450787704421825077 5067600979761347289546101)
                ·
                  refine ⟨475087591852626308394947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5067600979761347289546101 475087591852626308394947)
                  ·
                    rfl

theorem cell22_4163534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_4163534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163534 prefixEnd_4163534 := by exact prefixLift 4163534
  have htrace : WordTrace (prefixWord ++ tailWord_4163534) baseStart_4163534 baseEnd_4163534 := by
    simpa [prefixWord, tailWord_4163534, baseEnd_4163534] using wordTrace_append hprefix tailTrace_4163534
  have hstable : (prefixWord ++ tailWord_4163534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163534).length < 2 ^ (prefixWord ++ tailWord_4163534).sum := by decide
  have hdescent : baseEnd_4163534 < baseStart_4163534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163538 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_4163538 : Nat := 118140960795 + 4163538 * 2 ^ 59
def prefixEnd_4163538 : Nat := 4983230072969 + 3 ^ 40 * 4163538 * 2
def baseEnd_4163538 : Nat := 1425264144839624248084829

theorem tailTrace_4163538 : CollatzResearch.WordTrace tailWord_4163538 prefixEnd_4163538 1425264144839624248084829 := by
  unfold tailWord_4163538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964176597555094130970817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101237804260146917682588845 37964176597555094130970817)
  ·
    refine ⟨28473132448166320598228113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37964176597555094130970817 28473132448166320598228113)
    ·
      refine ⟨21354849336124740448671085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28473132448166320598228113 21354849336124740448671085)
      ·
        refine ⟨8008068501046777668251657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21354849336124740448671085 8008068501046777668251657)
        ·
          refine ⟨6006051375785083251188743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8008068501046777668251657 6006051375785083251188743)
          ·
            refine ⟨9009077063677624876783115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006051375785083251188743 9009077063677624876783115)
            ·
              refine ⟨13513615595516437315174673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009077063677624876783115 13513615595516437315174673)
              ·
                refine ⟨10135211696637327986381005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513615595516437315174673 10135211696637327986381005)
                ·
                  refine ⟨3800704386238997994892877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10135211696637327986381005 3800704386238997994892877)
                  ·
                    refine ⟨1425264144839624248084829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800704386238997994892877 1425264144839624248084829)
                    ·
                      rfl

theorem cell22_4163538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_4163538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163538 prefixEnd_4163538 := by exact prefixLift 4163538
  have htrace : WordTrace (prefixWord ++ tailWord_4163538) baseStart_4163538 baseEnd_4163538 := by
    simpa [prefixWord, tailWord_4163538, baseEnd_4163538] using wordTrace_append hprefix tailTrace_4163538
  have hstable : (prefixWord ++ tailWord_4163538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163538).length < 2 ^ (prefixWord ++ tailWord_4163538).sum := by decide
  have hdescent : baseEnd_4163538 < baseStart_4163538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163609 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_4163609 : Nat := 118140960795 + 4163609 * 2 ^ 59
def prefixEnd_4163609 : Nat := 4983230072969 + 3 ^ 40 * 4163609 * 2
def baseEnd_4163609 : Nat := 1425288449590603729559611

theorem tailTrace_4163609 : CollatzResearch.WordTrace tailWord_4163609 prefixEnd_4163609 1425288449590603729559611 := by
  unfold tailWord_4163609
  simp only [CollatzResearch.WordTrace]
  refine ⟨151859295972963155649717881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101239530648642103766478587 151859295972963155649717881)
  ·
    refine ⟨113894471979722366737288411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151859295972963155649717881 113894471979722366737288411)
    ·
      refine ⟨170841707969583550105932617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113894471979722366737288411 170841707969583550105932617)
      ·
        refine ⟨128131280977187662579449463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170841707969583550105932617 128131280977187662579449463)
        ·
          refine ⟨192196921465781493869174195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128131280977187662579449463 192196921465781493869174195)
          ·
            refine ⟨288295382198672240803761293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192196921465781493869174195 288295382198672240803761293)
            ·
              refine ⟨108110768324502090301410485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288295382198672240803761293 108110768324502090301410485)
              ·
                refine ⟨10135384530422070965757233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108110768324502090301410485 10135384530422070965757233)
                ·
                  refine ⟨7601538397816553224317925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10135384530422070965757233 7601538397816553224317925)
                  ·
                    refine ⟨1425288449590603729559611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601538397816553224317925 1425288449590603729559611)
                    ·
                      rfl

theorem cell22_4163609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_4163609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163609 prefixEnd_4163609 := by exact prefixLift 4163609
  have htrace : WordTrace (prefixWord ++ tailWord_4163609) baseStart_4163609 baseEnd_4163609 := by
    simpa [prefixWord, tailWord_4163609, baseEnd_4163609] using wordTrace_append hprefix tailTrace_4163609
  have hstable : (prefixWord ++ tailWord_4163609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163609).length < 2 ^ (prefixWord ++ tailWord_4163609).sum := by decide
  have hdescent : baseEnd_4163609 < baseStart_4163609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163613 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 4]
def baseStart_4163613 : Nat := 118140960795 + 4163613 * 2 ^ 59
def prefixEnd_4163613 : Nat := 4983230072969 + 3 ^ 40 * 4163613 * 2
def baseEnd_4163613 : Nat := 475096606290783017486533

theorem tailTrace_4163613 : CollatzResearch.WordTrace tailWord_4163613 prefixEnd_4163613 475096606290783017486533 := by
  unfold tailWord_4163613
  simp only [CollatzResearch.WordTrace]
  refine ⟨151859441864948664332863493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101239627909965776221908995 151859441864948664332863493)
  ·
    refine ⟨28473645349677874562411905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151859441864948664332863493 28473645349677874562411905)
    ·
      refine ⟨21355234012258405921808929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28473645349677874562411905 21355234012258405921808929)
      ·
        refine ⟨16016425509193804441356697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21355234012258405921808929 16016425509193804441356697)
        ·
          refine ⟨12012319131895353331017523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16016425509193804441356697 12012319131895353331017523)
          ·
            refine ⟨18018478697843029996526285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12012319131895353331017523 18018478697843029996526285)
            ·
              refine ⟨6756929511691136248697357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18018478697843029996526285 6756929511691136248697357)
              ·
                refine ⟨2533848566884176093261509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6756929511691136248697357 2533848566884176093261509)
                ·
                  refine ⟨475096606290783017486533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533848566884176093261509 475096606290783017486533)
                  ·
                    rfl

theorem cell22_4163613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_4163613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163613 prefixEnd_4163613 := by exact prefixLift 4163613
  have htrace : WordTrace (prefixWord ++ tailWord_4163613) baseStart_4163613 baseEnd_4163613 := by
    simpa [prefixWord, tailWord_4163613, baseEnd_4163613] using wordTrace_append hprefix tailTrace_4163613
  have hstable : (prefixWord ++ tailWord_4163613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163613).length < 2 ^ (prefixWord ++ tailWord_4163613).sum := by decide
  have hdescent : baseEnd_4163613 < baseStart_4163613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163626 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4163626 : Nat := 118140960795 + 4163626 * 2 ^ 59
def prefixEnd_4163626 : Nat := 4983230072969 + 3 ^ 40 * 4163626 * 2
def baseEnd_4163626 : Nat := 1425294269038021351884559

theorem tailTrace_4163626 : CollatzResearch.WordTrace tailWord_4163626 prefixEnd_4163626 1425294269038021351884559 := by
  unfold tailWord_4163626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964979003475391888271683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101239944009267711702057821 37964979003475391888271683)
  ·
    refine ⟨56947468505213087832407525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37964979003475391888271683 56947468505213087832407525)
    ·
      refine ⟨10677650344727453968576411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56947468505213087832407525 10677650344727453968576411)
      ·
        refine ⟨16016475517091180952864617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10677650344727453968576411 16016475517091180952864617)
        ·
          refine ⟨12012356637818385714648463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16016475517091180952864617 12012356637818385714648463)
          ·
            refine ⟨18018534956727578571972695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12012356637818385714648463 18018534956727578571972695)
            ·
              refine ⟨27027802435091367857959043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18018534956727578571972695 27027802435091367857959043)
              ·
                refine ⟨40541703652637051786938565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27027802435091367857959043 40541703652637051786938565)
                ·
                  refine ⟨7601569434869447210050981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40541703652637051786938565 7601569434869447210050981)
                  ·
                    refine ⟨1425294269038021351884559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601569434869447210050981 1425294269038021351884559)
                    ·
                      rfl

theorem cell22_4163626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4163626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163626 prefixEnd_4163626 := by exact prefixLift 4163626
  have htrace : WordTrace (prefixWord ++ tailWord_4163626) baseStart_4163626 baseEnd_4163626 := by
    simpa [prefixWord, tailWord_4163626, baseEnd_4163626] using wordTrace_append hprefix tailTrace_4163626
  have hstable : (prefixWord ++ tailWord_4163626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163626).length < 2 ^ (prefixWord ++ tailWord_4163626).sum := by decide
  have hdescent : baseEnd_4163626 < baseStart_4163626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163630 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_4163630 : Nat := 118140960795 + 4163630 * 2 ^ 59
def prefixEnd_4163630 : Nat := 4983230072969 + 3 ^ 40 * 4163630 * 2
def baseEnd_4163630 : Nat := 475098546106588891594849

theorem tailTrace_4163630 : CollatzResearch.WordTrace tailWord_4163630 prefixEnd_4163630 475098546106588891594849 := by
  unfold tailWord_4163630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982507738235884529529043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101240041270591384157488229 18982507738235884529529043)
  ·
    refine ⟨28473761607353826794293565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18982507738235884529529043 28473761607353826794293565)
    ·
      refine ⟨10677660602757685047860087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28473761607353826794293565 10677660602757685047860087)
      ·
        refine ⟨16016490904136527571790131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10677660602757685047860087 16016490904136527571790131)
        ·
          refine ⟨24024736356204791357685197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016490904136527571790131 24024736356204791357685197)
          ·
            refine ⟨9009276133576796759131949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24024736356204791357685197 9009276133576796759131949)
            ·
              refine ⟨3378478550091298784674481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9009276133576796759131949 3378478550091298784674481)
              ·
                refine ⟨2533858912568474088505861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378478550091298784674481 2533858912568474088505861)
                ·
                  refine ⟨475098546106588891594849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533858912568474088505861 475098546106588891594849)
                  ·
                    rfl

theorem cell22_4163630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_4163630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163630 prefixEnd_4163630 := by exact prefixLift 4163630
  have htrace : WordTrace (prefixWord ++ tailWord_4163630) baseStart_4163630 baseEnd_4163630 := by
    simpa [prefixWord, tailWord_4163630, baseEnd_4163630] using wordTrace_append hprefix tailTrace_4163630
  have hstable : (prefixWord ++ tailWord_4163630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163630).length < 2 ^ (prefixWord ++ tailWord_4163630).sum := by decide
  have hdescent : baseEnd_4163630 < baseStart_4163630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163641 : List Nat := [1, 2, 1, 5, 3, 1, 2, 7]
def baseStart_4163641 : Nat := 118140960795 + 4163641 * 2 ^ 59
def prefixEnd_4163641 : Nat := 4983230072969 + 3 ^ 40 * 4163641 * 2
def baseEnd_4163641 : Nat := 158366600427174034751057

theorem tailTrace_4163641 : CollatzResearch.WordTrace tailWord_4163641 prefixEnd_4163641 158366600427174034751057 := by
  unfold tailWord_4163641
  simp only [CollatzResearch.WordTrace]
  refine ⟨151860463108847225114882777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101240308739231483409921851 151860463108847225114882777)
  ·
    refine ⟨113895347331635418836162083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151860463108847225114882777 113895347331635418836162083)
    ·
      refine ⟨170843020997453128254243125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113895347331635418836162083 170843020997453128254243125)
      ·
        refine ⟨16016533218511230773835293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170843020997453128254243125 16016533218511230773835293)
        ·
          refine ⟨6006199956941711540188235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16016533218511230773835293 6006199956941711540188235)
          ·
            refine ⟨9009299935412567310282353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006199956941711540188235 9009299935412567310282353)
            ·
              refine ⟨6756974951559425482711765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9009299935412567310282353 6756974951559425482711765)
              ·
                refine ⟨158366600427174034751057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6756974951559425482711765 158366600427174034751057)
                ·
                  rfl

theorem cell22_4163641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 7].length) (baseStart_4163641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163641 prefixEnd_4163641 := by exact prefixLift 4163641
  have htrace : WordTrace (prefixWord ++ tailWord_4163641) baseStart_4163641 baseEnd_4163641 := by
    simpa [prefixWord, tailWord_4163641, baseEnd_4163641] using wordTrace_append hprefix tailTrace_4163641
  have hstable : (prefixWord ++ tailWord_4163641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163641).length < 2 ^ (prefixWord ++ tailWord_4163641).sum := by decide
  have hdescent : baseEnd_4163641 < baseStart_4163641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163673 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 1, 3]
def baseStart_4163673 : Nat := 118140960795 + 4163673 * 2 ^ 59
def prefixEnd_4163673 : Nat := 4983230072969 + 3 ^ 40 * 4163673 * 2
def baseEnd_4163673 : Nat := 1425310358098528895959415

theorem tailTrace_4163673 : CollatzResearch.WordTrace tailWord_4163673 prefixEnd_4163673 1425310358098528895959415 := by
  unfold tailWord_4163673
  simp only [CollatzResearch.WordTrace]
  refine ⟨151861630244731294580047673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101241086829820863053365115 151861630244731294580047673)
  ·
    refine ⟨113896222683548470935035755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151861630244731294580047673 113896222683548470935035755)
    ·
      refine ⟨170844334025322706402553633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113896222683548470935035755 170844334025322706402553633)
      ·
        refine ⟨128133250518992029801915225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170844334025322706402553633 128133250518992029801915225)
        ·
          refine ⟨96099937889244022351436419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128133250518992029801915225 96099937889244022351436419)
          ·
            refine ⟨144149906833866033527154629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96099937889244022351436419 144149906833866033527154629)
            ·
              refine ⟨27028107531349881286341493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144149906833866033527154629 27028107531349881286341493)
              ·
                refine ⟨2533885081064051370594515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27028107531349881286341493 2533885081064051370594515)
                ·
                  refine ⟨3800827621596077055891773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533885081064051370594515 3800827621596077055891773)
                  ·
                    refine ⟨1425310358098528895959415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800827621596077055891773 1425310358098528895959415)
                    ·
                      rfl

theorem cell22_4163673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_4163673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163673 prefixEnd_4163673 := by exact prefixLift 4163673
  have htrace : WordTrace (prefixWord ++ tailWord_4163673) baseStart_4163673 baseEnd_4163673 := by
    simpa [prefixWord, tailWord_4163673, baseEnd_4163673] using wordTrace_append hprefix tailTrace_4163673
  have hstable : (prefixWord ++ tailWord_4163673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163673).length < 2 ^ (prefixWord ++ tailWord_4163673).sum := by decide
  have hdescent : baseEnd_4163673 < baseStart_4163673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163716 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4163716 : Nat := 118140960795 + 4163716 * 2 ^ 59
def prefixEnd_4163716 : Nat := 4983230072969 + 3 ^ 40 * 4163716 * 2
def baseEnd_4163716 : Nat := 1425325077877291117134283

theorem tailTrace_4163716 : CollatzResearch.WordTrace tailWord_4163716 prefixEnd_4163716 1425325077877291117134283 := by
  unfold tailWord_4163716
  simp only [CollatzResearch.WordTrace]
  refine ⟨75931599291787756461931501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101242132389050341949242001 75931599291787756461931501)
  ·
    refine ⟨28474349734420408673224313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75931599291787756461931501 28474349734420408673224313)
    ·
      refine ⟨21355762300815306504918235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28474349734420408673224313 21355762300815306504918235)
      ·
        refine ⟨32033643451222959757377353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21355762300815306504918235 32033643451222959757377353)
        ·
          refine ⟨24025232588417219818033015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32033643451222959757377353 24025232588417219818033015)
          ·
            refine ⟨36037848882625829727049523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24025232588417219818033015 36037848882625829727049523)
            ·
              refine ⟨54056773323938744590574285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36037848882625829727049523 54056773323938744590574285)
              ·
                refine ⟨20271289996477029221465357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54056773323938744590574285 20271289996477029221465357)
                ·
                  refine ⟨7601733748678885958049509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20271289996477029221465357 7601733748678885958049509)
                  ·
                    refine ⟨1425325077877291117134283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7601733748678885958049509 1425325077877291117134283)
                    ·
                      rfl

theorem cell22_4163716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4163716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163716 prefixEnd_4163716 := by exact prefixLift 4163716
  have htrace : WordTrace (prefixWord ++ tailWord_4163716) baseStart_4163716 baseEnd_4163716 := by
    simpa [prefixWord, tailWord_4163716, baseEnd_4163716] using wordTrace_append hprefix tailTrace_4163716
  have hstable : (prefixWord ++ tailWord_4163716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163716).length < 2 ^ (prefixWord ++ tailWord_4163716).sum := by decide
  have hdescent : baseEnd_4163716 < baseStart_4163716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163748 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_4163748 : Nat := 118140960795 + 4163748 * 2 ^ 59
def prefixEnd_4163748 : Nat := 4983230072969 + 3 ^ 40 * 4163748 * 2
def baseEnd_4163748 : Nat := 475112010710417900111395

theorem tailTrace_4163748 : CollatzResearch.WordTrace tailWord_4163748 prefixEnd_4163748 475112010710417900111395 := by
  unfold tailWord_4163748
  simp only [CollatzResearch.WordTrace]
  refine ⟨75932182859729791194513949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101242910479639721592685265 75932182859729791194513949)
  ·
    refine ⟨28474568572398671697942731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75932182859729791194513949 28474568572398671697942731)
    ·
      refine ⟨42711852858598007546914097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28474568572398671697942731 42711852858598007546914097)
      ·
        refine ⟨32033889643948505660185573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42711852858598007546914097 32033889643948505660185573)
        ·
          refine ⟨6006354308240344811284795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32033889643948505660185573 6006354308240344811284795)
          ·
            refine ⟨9009531462360517216927193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006354308240344811284795 9009531462360517216927193)
            ·
              refine ⟨6757148596770387912695395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9009531462360517216927193 6757148596770387912695395)
              ·
                refine ⟨10135722895155581869043093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757148596770387912695395 10135722895155581869043093)
                ·
                  refine ⟨475112010710417900111395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10135722895155581869043093 475112010710417900111395)
                  ·
                    rfl

theorem cell22_4163748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_4163748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163748 prefixEnd_4163748 := by exact prefixLift 4163748
  have htrace : WordTrace (prefixWord ++ tailWord_4163748) baseStart_4163748 baseEnd_4163748 := by
    simpa [prefixWord, tailWord_4163748, baseEnd_4163748] using wordTrace_append hprefix tailTrace_4163748
  have hstable : (prefixWord ++ tailWord_4163748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163748).length < 2 ^ (prefixWord ++ tailWord_4163748).sum := by decide
  have hdescent : baseEnd_4163748 < baseStart_4163748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163759 : List Nat := [1, 1, 2, 1, 2, 3, 1, 11]
def baseStart_4163759 : Nat := 118140960795 + 4163759 * 2 ^ 59
def prefixEnd_4163759 : Nat := 4983230072969 + 3 ^ 40 * 4163759 * 2
def baseEnd_4163759 : Nat := 158371088628450370923239

theorem tailTrace_4163759 : CollatzResearch.WordTrace tailWord_4163759 prefixEnd_4163759 158371088628450370923239 := by
  unfold tailWord_4163759
  simp only [CollatzResearch.WordTrace]
  refine ⟨151864766922419731267678331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101243177948279820845118887 151864766922419731267678331)
  ·
    refine ⟨227797150383629596901517497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151864766922419731267678331 227797150383629596901517497)
    ·
      refine ⟨170847862787722197676138123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227797150383629596901517497 170847862787722197676138123)
      ·
        refine ⟨256271794181583296514207185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170847862787722197676138123 256271794181583296514207185)
        ·
          refine ⟨192203845636187472385655389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256271794181583296514207185 192203845636187472385655389)
          ·
            refine ⟨72076442113570302144620771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192203845636187472385655389 72076442113570302144620771)
            ·
              refine ⟨108114663170355453216931157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72076442113570302144620771 108114663170355453216931157)
              ·
                refine ⟨158371088628450370923239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108114663170355453216931157 158371088628450370923239)
                ·
                  rfl

theorem cell22_4163759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 11].length) (baseStart_4163759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163759 prefixEnd_4163759 := by exact prefixLift 4163759
  have htrace : WordTrace (prefixWord ++ tailWord_4163759) baseStart_4163759 baseEnd_4163759 := by
    simpa [prefixWord, tailWord_4163759, baseEnd_4163759] using wordTrace_append hprefix tailTrace_4163759
  have hstable : (prefixWord ++ tailWord_4163759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163759).length < 2 ^ (prefixWord ++ tailWord_4163759).sum := by decide
  have hdescent : baseEnd_4163759 < baseStart_4163759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163776 : List Nat := [2, 1, 1, 2, 5, 2, 1, 8]
def baseStart_4163776 : Nat := 118140960795 + 4163776 * 2 ^ 59
def prefixEnd_4163776 : Nat := 4983230072969 + 3 ^ 40 * 4163776 * 2
def baseEnd_4163776 : Nat := 158371735233718995626011

theorem tailTrace_4163776 : CollatzResearch.WordTrace tailWord_4163776 prefixEnd_4163776 158371735233718995626011 := by
  unfold tailWord_4163776
  simp only [CollatzResearch.WordTrace]
  refine ⟨75932693481679071585523591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101243591308905428780698121 75932693481679071585523591)
  ·
    refine ⟨113899040222518607378285387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75932693481679071585523591 113899040222518607378285387)
    ·
      refine ⟨170848560333777911067428081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113899040222518607378285387 170848560333777911067428081)
      ·
        refine ⟨128136420250333433300571061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170848560333777911067428081 128136420250333433300571061)
        ·
          refine ⟨12012789398468759371928537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128136420250333433300571061 12012789398468759371928537)
          ·
            refine ⟨9009592048851569528946403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12012789398468759371928537 9009592048851569528946403)
            ·
              refine ⟨13514388073277354293419605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009592048851569528946403 13514388073277354293419605)
              ·
                refine ⟨158371735233718995626011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13514388073277354293419605 158371735233718995626011)
                ·
                  rfl

theorem cell22_4163776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_4163776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163776 prefixEnd_4163776 := by exact prefixLift 4163776
  have htrace : WordTrace (prefixWord ++ tailWord_4163776) baseStart_4163776 baseEnd_4163776 := by
    simpa [prefixWord, tailWord_4163776, baseEnd_4163776] using wordTrace_append hprefix tailTrace_4163776
  have hstable : (prefixWord ++ tailWord_4163776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163776).length < 2 ^ (prefixWord ++ tailWord_4163776).sum := by decide
  have hdescent : baseEnd_4163776 < baseStart_4163776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163870 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4163870 : Nat := 118140960795 + 4163870 * 2 ^ 59
def prefixEnd_4163870 : Nat := 4983230072969 + 3 ^ 40 * 4163870 * 2
def baseEnd_4163870 : Nat := 1425377795224486048783811

theorem tailTrace_4163870 : CollatzResearch.WordTrace tailWord_4163870 prefixEnd_4163870 1425377795224486048783811 := by
  unfold tailWord_4163870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983601928127199653121133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101245876950011731483312709 18983601928127199653121133)
  ·
    refine ⟨7118850723047699869920425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18983601928127199653121133 7118850723047699869920425)
    ·
      refine ⟨5339138042285774902440319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7118850723047699869920425 5339138042285774902440319)
      ·
        refine ⟨8008707063428662353660479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339138042285774902440319 8008707063428662353660479)
        ·
          refine ⟨12013060595142993530490719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8008707063428662353660479 12013060595142993530490719)
          ·
            refine ⟨18019590892714490295736079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12013060595142993530490719 18019590892714490295736079)
            ·
              refine ⟨27029386339071735443604119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18019590892714490295736079 27029386339071735443604119)
              ·
                refine ⟨40544079508607603165406179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27029386339071735443604119 40544079508607603165406179)
                ·
                  refine ⟨60816119262911404748109269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40544079508607603165406179 60816119262911404748109269)
                  ·
                    refine ⟨1425377795224486048783811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60816119262911404748109269 1425377795224486048783811)
                    ·
                      rfl

theorem cell22_4163870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4163870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163870 prefixEnd_4163870 := by exact prefixLift 4163870
  have htrace : WordTrace (prefixWord ++ tailWord_4163870) baseStart_4163870 baseEnd_4163870 := by
    simpa [prefixWord, tailWord_4163870, baseEnd_4163870] using wordTrace_append hprefix tailTrace_4163870
  have hstable : (prefixWord ++ tailWord_4163870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163870).length < 2 ^ (prefixWord ++ tailWord_4163870).sum := by decide
  have hdescent : baseEnd_4163870 < baseStart_4163870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163898 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_4163898 : Nat := 118140960795 + 4163898 * 2 ^ 59
def prefixEnd_4163898 : Nat := 4983230072969 + 3 ^ 40 * 4163898 * 2
def baseEnd_4163898 : Nat := 1425387380196703309083725

theorem tailTrace_4163898 : CollatzResearch.WordTrace tailWord_4163898 prefixEnd_4163898 1425387380196703309083725 := by
  unfold tailWord_4163898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37967459167229039501747087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101246557779277438671325565 37967459167229039501747087)
  ·
    refine ⟨56951188750843559252620631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37967459167229039501747087 56951188750843559252620631)
    ·
      refine ⟨85426783126265338878930947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56951188750843559252620631 85426783126265338878930947)
      ·
        refine ⟨128140174689398008318396421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85426783126265338878930947 128140174689398008318396421)
        ·
          refine ⟨24026282754262126559699329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128140174689398008318396421 24026282754262126559699329)
          ·
            refine ⟨18019712065696594919774497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24026282754262126559699329 18019712065696594919774497)
            ·
              refine ⟨13514784049272446189830873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18019712065696594919774497 13514784049272446189830873)
              ·
                refine ⟨10136088036954334642373155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13514784049272446189830873 10136088036954334642373155)
                ·
                  refine ⟨15204132055431501963559733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10136088036954334642373155 15204132055431501963559733)
                  ·
                    refine ⟨1425387380196703309083725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15204132055431501963559733 1425387380196703309083725)
                    ·
                      rfl

theorem cell22_4163898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_4163898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163898 prefixEnd_4163898 := by exact prefixLift 4163898
  have htrace : WordTrace (prefixWord ++ tailWord_4163898) baseStart_4163898 baseEnd_4163898 := by
    simpa [prefixWord, tailWord_4163898, baseEnd_4163898] using wordTrace_append hprefix tailTrace_4163898
  have hstable : (prefixWord ++ tailWord_4163898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163898).length < 2 ^ (prefixWord ++ tailWord_4163898).sum := by decide
  have hdescent : baseEnd_4163898 < baseStart_4163898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163900 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 4]
def baseStart_4163900 : Nat := 118140960795 + 4163900 * 2 ^ 59
def prefixEnd_4163900 : Nat := 4983230072969 + 3 ^ 40 * 4163900 * 2
def baseEnd_4163900 : Nat := 475129354945858656844573

theorem tailTrace_4163900 : CollatzResearch.WordTrace tailWord_4163900 prefixEnd_4163900 475129354945858656844573 := by
  unfold tailWord_4163900
  simp only [CollatzResearch.WordTrace]
  refine ⟨75934954807454456174280577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101246606409939274899040769 75934954807454456174280577)
  ·
    refine ⟨56951216105590842130710433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75934954807454456174280577 56951216105590842130710433)
    ·
      refine ⟨42713412079193131598032825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56951216105590842130710433 42713412079193131598032825)
      ·
        refine ⟨32035059059394848698524619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42713412079193131598032825 32035059059394848698524619)
        ·
          refine ⟨48052588589092273047786929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32035059059394848698524619 48052588589092273047786929)
          ·
            refine ⟨36039441441819204785840197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48052588589092273047786929 36039441441819204785840197)
            ·
              refine ⟨6757395270341100897345037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36039441441819204785840197 6757395270341100897345037)
              ·
                refine ⟨2534023226377912836504389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6757395270341100897345037 2534023226377912836504389)
                ·
                  refine ⟨475129354945858656844573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534023226377912836504389 475129354945858656844573)
                  ·
                    rfl

theorem cell22_4163900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_4163900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163900 prefixEnd_4163900 := by exact prefixLift 4163900
  have htrace : WordTrace (prefixWord ++ tailWord_4163900) baseStart_4163900 baseEnd_4163900 := by
    simpa [prefixWord, tailWord_4163900, baseEnd_4163900] using wordTrace_append hprefix tailTrace_4163900
  have hstable : (prefixWord ++ tailWord_4163900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163900).length < 2 ^ (prefixWord ++ tailWord_4163900).sum := by decide
  have hdescent : baseEnd_4163900 < baseStart_4163900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163902 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_4163902 : Nat := 118140960795 + 4163902 * 2 ^ 59
def prefixEnd_4163902 : Nat := 4983230072969 + 3 ^ 40 * 4163902 * 2
def baseEnd_4163902 : Nat := 1425388749478448631983713

theorem tailTrace_4163902 : CollatzResearch.WordTrace tailWord_4163902 prefixEnd_4163902 1425388749478448631983713 := by
  unfold tailWord_4163902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983747820112708336266745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101246655040601111126755973 18983747820112708336266745)
  ·
    refine ⟨14237810865084531252200059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18983747820112708336266745 14237810865084531252200059)
    ·
      refine ⟨21356716297626796878300089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14237810865084531252200059 21356716297626796878300089)
      ·
        refine ⟨16017537223220097658725067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21356716297626796878300089 16017537223220097658725067)
        ·
          refine ⟨24026305834830146488087601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16017537223220097658725067 24026305834830146488087601)
          ·
            refine ⟨18019729376122609866065701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24026305834830146488087601 18019729376122609866065701)
            ·
              refine ⟨3378699258022989349887319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18019729376122609866065701 3378699258022989349887319)
              ·
                refine ⟨5068048887034484024830979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378699258022989349887319 5068048887034484024830979)
                ·
                  refine ⟨7602073330551726037246469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068048887034484024830979 7602073330551726037246469)
                  ·
                    refine ⟨1425388749478448631983713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7602073330551726037246469 1425388749478448631983713)
                    ·
                      rfl

theorem cell22_4163902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_4163902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163902 prefixEnd_4163902 := by exact prefixLift 4163902
  have htrace : WordTrace (prefixWord ++ tailWord_4163902) baseStart_4163902 baseEnd_4163902 := by
    simpa [prefixWord, tailWord_4163902, baseEnd_4163902] using wordTrace_append hprefix tailTrace_4163902
  have hstable : (prefixWord ++ tailWord_4163902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163902).length < 2 ^ (prefixWord ++ tailWord_4163902).sum := by decide
  have hdescent : baseEnd_4163902 < baseStart_4163902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163911 : List Nat := [1, 1, 4, 1, 2, 2, 11]
def baseStart_4163911 : Nat := 118140960795 + 4163911 * 2 ^ 59
def prefixEnd_4163911 : Nat := 4983230072969 + 3 ^ 40 * 4163911 * 2
def baseEnd_4163911 : Nat := 52792290013421318833655

theorem tailTrace_4163911 : CollatzResearch.WordTrace tailWord_4163911 prefixEnd_4163911 52792290013421318833655 := by
  unfold tailWord_4163911
  simp only [CollatzResearch.WordTrace]
  refine ⟨151870310817869061227211587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101246873878579374151474391 151870310817869061227211587)
  ·
    refine ⟨227805466226803591840817381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151870310817869061227211587 227805466226803591840817381)
    ·
      refine ⟨42713524917525673470153259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227805466226803591840817381 42713524917525673470153259)
      ·
        refine ⟨64070287376288510205229889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42713524917525673470153259 64070287376288510205229889)
        ·
          refine ⟨48052715532216382653922417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64070287376288510205229889 48052715532216382653922417)
          ·
            refine ⟨36039536649162286990441813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48052715532216382653922417 36039536649162286990441813)
            ·
              refine ⟨52792290013421318833655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 36039536649162286990441813 52792290013421318833655)
              ·
                rfl

theorem cell22_4163911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 11].length) (baseStart_4163911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163911 prefixEnd_4163911 := by exact prefixLift 4163911
  have htrace : WordTrace (prefixWord ++ tailWord_4163911) baseStart_4163911 baseEnd_4163911 := by
    simpa [prefixWord, tailWord_4163911, baseEnd_4163911] using wordTrace_append hprefix tailTrace_4163911
  have hstable : (prefixWord ++ tailWord_4163911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163911).length < 2 ^ (prefixWord ++ tailWord_4163911).sum := by decide
  have hdescent : baseEnd_4163911 < baseStart_4163911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163973 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 5]
def baseStart_4163973 : Nat := 118140960795 + 4163973 * 2 ^ 59
def prefixEnd_4163973 : Nat := 4983230072969 + 3 ^ 40 * 4163973 * 2
def baseEnd_4163973 : Nat := 475137684743142704486165

theorem tailTrace_4163973 : CollatzResearch.WordTrace tailWord_4163973 prefixEnd_4163973 475137684743142704486165 := by
  unfold tailWord_4163973
  simp only [CollatzResearch.WordTrace]
  refine ⟨151872572143644445815968573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101248381429096297210645715 151872572143644445815968573)
  ·
    refine ⟨56952214553866667180988215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151872572143644445815968573 56952214553866667180988215)
    ·
      refine ⟨85428321830800000771482323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56952214553866667180988215 85428321830800000771482323)
      ·
        refine ⟨128142482746200001157223485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85428321830800000771482323 128142482746200001157223485)
        ·
          refine ⟨48053431029825000433958807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128142482746200001157223485 48053431029825000433958807)
          ·
            refine ⟨72080146544737500650938211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48053431029825000433958807 72080146544737500650938211)
            ·
              refine ⟨108120219817106250976407317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72080146544737500650938211 108120219817106250976407317)
              ·
                refine ⟨5068135303926855514519093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108120219817106250976407317 5068135303926855514519093)
                ·
                  refine ⟨475137684743142704486165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068135303926855514519093 475137684743142704486165)
                  ·
                    rfl

theorem cell22_4163973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_4163973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163973 prefixEnd_4163973 := by exact prefixLift 4163973
  have htrace : WordTrace (prefixWord ++ tailWord_4163973) baseStart_4163973 baseEnd_4163973 := by
    simpa [prefixWord, tailWord_4163973, baseEnd_4163973] using wordTrace_append hprefix tailTrace_4163973
  have hstable : (prefixWord ++ tailWord_4163973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163973).length < 2 ^ (prefixWord ++ tailWord_4163973).sum := by decide
  have hdescent : baseEnd_4163973 < baseStart_4163973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163977 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_4163977 : Nat := 118140960795 + 4163977 * 2 ^ 59
def prefixEnd_4163977 : Nat := 4983230072969 + 3 ^ 40 * 4163977 * 2
def baseEnd_4163977 : Nat := 1425414423511173436358483

theorem tailTrace_4163977 : CollatzResearch.WordTrace tailWord_4163977 prefixEnd_4163977 1425414423511173436358483 := by
  unfold tailWord_4163977
  simp only [CollatzResearch.WordTrace]
  refine ⟨151872718035629954499114185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101248478690419969666076123 151872718035629954499114185)
  ·
    refine ⟨113904538526722465874335639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151872718035629954499114185 113904538526722465874335639)
    ·
      refine ⟨170856807790083698811503459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113904538526722465874335639 170856807790083698811503459)
      ·
        refine ⟨256285211685125548217255189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170856807790083698811503459 256285211685125548217255189)
        ·
          refine ⟨12013369297740260072683837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256285211685125548217255189 12013369297740260072683837)
          ·
            refine ⟨4505013486652597527256439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12013369297740260072683837 4505013486652597527256439)
            ·
              refine ⟨6757520229978896290884659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505013486652597527256439 6757520229978896290884659)
              ·
                refine ⟨10136280344968344436326989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757520229978896290884659 10136280344968344436326989)
                ·
                  refine ⟨3801105129363129163622621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10136280344968344436326989 3801105129363129163622621)
                  ·
                    refine ⟨1425414423511173436358483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801105129363129163622621 1425414423511173436358483)
                    ·
                      rfl

theorem cell22_4163977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_4163977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4163977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4163977 prefixEnd_4163977 := by exact prefixLift 4163977
  have htrace : WordTrace (prefixWord ++ tailWord_4163977) baseStart_4163977 baseEnd_4163977 := by
    simpa [prefixWord, tailWord_4163977, baseEnd_4163977] using wordTrace_append hprefix tailTrace_4163977
  have hstable : (prefixWord ++ tailWord_4163977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163977).length < 2 ^ (prefixWord ++ tailWord_4163977).sum := by decide
  have hdescent : baseEnd_4163977 < baseStart_4163977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164069 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 4]
def baseStart_4164069 : Nat := 118140960795 + 4164069 * 2 ^ 59
def prefixEnd_4164069 : Nat := 4983230072969 + 3 ^ 40 * 4164069 * 2
def baseEnd_4164069 : Nat := 475148638997105287686067

theorem tailTrace_4164069 : CollatzResearch.WordTrace tailWord_4164069 prefixEnd_4164069 475148638997105287686067 := by
  unfold tailWord_4164069
  simp only [CollatzResearch.WordTrace]
  refine ⟨151876073551296654211463261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101250715700864436140975507 151876073551296654211463261)
  ·
    refine ⟨56953527581736245329298723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151876073551296654211463261 56953527581736245329298723)
    ·
      refine ⟨85430291372604367993948085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56953527581736245329298723 85430291372604367993948085)
      ·
        refine ⟨8009089816181659499432633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85430291372604367993948085 8009089816181659499432633)
        ·
          refine ⟨6006817362136244624574475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8009089816181659499432633 6006817362136244624574475)
          ·
            refine ⟨9010226043204366936861713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006817362136244624574475 9010226043204366936861713)
            ·
              refine ⟨6757669532403275202646285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9010226043204366936861713 6757669532403275202646285)
              ·
                refine ⟨2534126074651228200992357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6757669532403275202646285 2534126074651228200992357)
                ·
                  refine ⟨475148638997105287686067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534126074651228200992357 475148638997105287686067)
                  ·
                    rfl

theorem cell22_4164069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_4164069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164069 prefixEnd_4164069 := by exact prefixLift 4164069
  have htrace : WordTrace (prefixWord ++ tailWord_4164069) baseStart_4164069 baseEnd_4164069 := by
    simpa [prefixWord, tailWord_4164069, baseEnd_4164069] using wordTrace_append hprefix tailTrace_4164069
  have hstable : (prefixWord ++ tailWord_4164069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164069).length < 2 ^ (prefixWord ++ tailWord_4164069).sum := by decide
  have hdescent : baseEnd_4164069 < baseStart_4164069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164125 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 7]
def baseStart_4164125 : Nat := 118140960795 + 4164125 * 2 ^ 59
def prefixEnd_4164125 : Nat := 4983230072969 + 3 ^ 40 * 4164125 * 2
def baseEnd_4164125 : Nat := 475155028978583461219343

theorem tailTrace_4164125 : CollatzResearch.WordTrace tailWord_4164125 prefixEnd_4164125 475155028978583461219343 := by
  unfold tailWord_4164125
  simp only [CollatzResearch.WordTrace]
  refine ⟨151878116039093775775501829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101252077359395850517001219 151878116039093775775501829)
  ·
    refine ⟨28477146757330082957906593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151878116039093775775501829 28477146757330082957906593)
    ·
      refine ⟨21357860067997562218429945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28477146757330082957906593 21357860067997562218429945)
      ·
        refine ⟨16018395050998171663822459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21357860067997562218429945 16018395050998171663822459)
        ·
          refine ⟨24027592576497257495733689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018395050998171663822459 24027592576497257495733689)
          ·
            refine ⟨18020694432372943121800267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24027592576497257495733689 18020694432372943121800267)
            ·
              refine ⟨27031041648559414682700401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18020694432372943121800267 27031041648559414682700401)
              ·
                refine ⟨20273281236419561012025301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27031041648559414682700401 20273281236419561012025301)
                ·
                  refine ⟨475155028978583461219343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20273281236419561012025301 475155028978583461219343)
                  ·
                    rfl

theorem cell22_4164125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_4164125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164125 prefixEnd_4164125 := by exact prefixLift 4164125
  have htrace : WordTrace (prefixWord ++ tailWord_4164125) baseStart_4164125 baseEnd_4164125 := by
    simpa [prefixWord, tailWord_4164125, baseEnd_4164125] using wordTrace_append hprefix tailTrace_4164125
  have hstable : (prefixWord ++ tailWord_4164125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164125).length < 2 ^ (prefixWord ++ tailWord_4164125).sum := by decide
  have hdescent : baseEnd_4164125 < baseStart_4164125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164204 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 4]
def baseStart_4164204 : Nat := 118140960795 + 4164204 * 2 ^ 59
def prefixEnd_4164204 : Nat := 4983230072969 + 3 ^ 40 * 4164204 * 2
def baseEnd_4164204 : Nat := 475164043416740170310929

theorem tailTrace_4164204 : CollatzResearch.WordTrace tailWord_4164204 prefixEnd_4164204 475164043416740170310929 := by
  unfold tailWord_4164204
  simp only [CollatzResearch.WordTrace]
  refine ⟨75940498702903786133813833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101253998270538381511751777 75940498702903786133813833)
  ·
    refine ⟨56955374027177839600360375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75940498702903786133813833 56955374027177839600360375)
    ·
      refine ⟨85433061040766759400540563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56955374027177839600360375 85433061040766759400540563)
      ·
        refine ⟨128149591561150139100810845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85433061040766759400540563 128149591561150139100810845)
        ·
          refine ⟨48056096835431302162804067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128149591561150139100810845 48056096835431302162804067)
          ·
            refine ⟨72084145253146953244206101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48056096835431302162804067 72084145253146953244206101)
            ·
              refine ⟨3378944308741263433322161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72084145253146953244206101 3378944308741263433322161)
              ·
                refine ⟨2534208231555947574991621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378944308741263433322161 2534208231555947574991621)
                ·
                  refine ⟨475164043416740170310929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534208231555947574991621 475164043416740170310929)
                  ·
                    rfl

theorem cell22_4164204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_4164204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164204 prefixEnd_4164204 := by exact prefixLift 4164204
  have htrace : WordTrace (prefixWord ++ tailWord_4164204) baseStart_4164204 baseEnd_4164204 := by
    simpa [prefixWord, tailWord_4164204, baseEnd_4164204] using wordTrace_append hprefix tailTrace_4164204
  have hstable : (prefixWord ++ tailWord_4164204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164204).length < 2 ^ (prefixWord ++ tailWord_4164204).sum := by decide
  have hdescent : baseEnd_4164204 < baseStart_4164204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164215 : List Nat := [1, 1, 3, 1, 1, 3, 5, 7]
def baseStart_4164215 : Nat := 118140960795 + 4164215 * 2 ^ 59
def prefixEnd_4164215 : Nat := 4983230072969 + 3 ^ 40 * 4164215 * 2
def baseEnd_4164215 : Nat := 158388432863891127656417

theorem tailTrace_4164215 : CollatzResearch.WordTrace tailWord_4164215 prefixEnd_4164215 158388432863891127656417 := by
  unfold tailWord_4164215
  simp only [CollatzResearch.WordTrace]
  refine ⟨151881398608767721146278099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101254265739178480764185399 151881398608767721146278099)
  ·
    refine ⟨227822097913151581719417149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151881398608767721146278099 227822097913151581719417149)
    ·
      refine ⟨85433286717431843144781431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227822097913151581719417149 85433286717431843144781431)
      ·
        refine ⟨128149930076147764717172147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85433286717431843144781431 128149930076147764717172147)
        ·
          refine ⟨192224895114221647075758221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128149930076147764717172147 192224895114221647075758221)
          ·
            refine ⟨72084335667833117653409333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192224895114221647075758221 72084335667833117653409333)
            ·
              refine ⟨6757906468859354780007125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72084335667833117653409333 6757906468859354780007125)
              ·
                refine ⟨158388432863891127656417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6757906468859354780007125 158388432863891127656417)
                ·
                  rfl

theorem cell22_4164215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 7].length) (baseStart_4164215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164215 prefixEnd_4164215 := by exact prefixLift 4164215
  have htrace : WordTrace (prefixWord ++ tailWord_4164215) baseStart_4164215 baseEnd_4164215 := by
    simpa [prefixWord, tailWord_4164215, baseEnd_4164215] using wordTrace_append hprefix tailTrace_4164215
  have hstable : (prefixWord ++ tailWord_4164215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164215).length < 2 ^ (prefixWord ++ tailWord_4164215).sum := by decide
  have hdescent : baseEnd_4164215 < baseStart_4164215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164247 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 5, 3]
def baseStart_4164247 : Nat := 118140960795 + 4164247 * 2 ^ 59
def prefixEnd_4164247 : Nat := 4983230072969 + 3 ^ 40 * 4164247 * 2
def baseEnd_4164247 : Nat := 1425506850028982732107655

theorem tailTrace_4164247 : CollatzResearch.WordTrace tailWord_4164247 prefixEnd_4164247 1425506850028982732107655 := by
  unfold tailWord_4164247
  simp only [CollatzResearch.WordTrace]
  refine ⟨151882565744651790611442995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101255043829767860407628663 151882565744651790611442995)
  ·
    refine ⟨227823848616977685917164493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151882565744651790611442995 227823848616977685917164493)
    ·
      refine ⟨85433943231366632218936685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227823848616977685917164493 85433943231366632218936685)
      ·
        refine ⟨32037728711762487082101257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85433943231366632218936685 32037728711762487082101257)
        ·
          refine ⟨24028296533821865311575943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32037728711762487082101257 24028296533821865311575943)
          ·
            refine ⟨36042444800732797967363915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24028296533821865311575943 36042444800732797967363915)
            ·
              refine ⟨54063667201099196951045873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36042444800732797967363915 54063667201099196951045873)
              ·
                refine ⟨40547750400824397713284405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54063667201099196951045873 40547750400824397713284405)
                ·
                  refine ⟨3801351600077287285620413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40547750400824397713284405 3801351600077287285620413)
                  ·
                    refine ⟨1425506850028982732107655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801351600077287285620413 1425506850028982732107655)
                    ·
                      rfl

theorem cell22_4164247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_4164247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164247 prefixEnd_4164247 := by exact prefixLift 4164247
  have htrace : WordTrace (prefixWord ++ tailWord_4164247) baseStart_4164247 baseEnd_4164247 := by
    simpa [prefixWord, tailWord_4164247, baseEnd_4164247] using wordTrace_append hprefix tailTrace_4164247
  have hstable : (prefixWord ++ tailWord_4164247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164247).length < 2 ^ (prefixWord ++ tailWord_4164247).sum := by decide
  have hdescent : baseEnd_4164247 < baseStart_4164247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164298 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_4164298 : Nat := 118140960795 + 4164298 * 2 ^ 59
def prefixEnd_4164298 : Nat := 4983230072969 + 3 ^ 40 * 4164298 * 2
def baseEnd_4164298 : Nat := 1425524308371235599082499

theorem tailTrace_4164298 : CollatzResearch.WordTrace tailWord_4164298 prefixEnd_4164298 1425524308371235599082499 := by
  unfold tailWord_4164298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37971106466866756580387387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101256283911644684214366365 37971106466866756580387387)
  ·
    refine ⟨56956659700300134870581081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37971106466866756580387387 56956659700300134870581081)
    ·
      refine ⟨42717494775225101152935811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56956659700300134870581081 42717494775225101152935811)
      ·
        refine ⟨64076242162837651729403717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42717494775225101152935811 64076242162837651729403717)
        ·
          refine ⟨12014295405532059699263197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64076242162837651729403717 12014295405532059699263197)
          ·
            refine ⟨4505360777074522387223699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12014295405532059699263197 4505360777074522387223699)
            ·
              refine ⟨6758041165611783580835549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505360777074522387223699 6758041165611783580835549)
              ·
                refine ⟨2534265437104418842813331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6758041165611783580835549 2534265437104418842813331)
                ·
                  refine ⟨3801398155656628264219997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534265437104418842813331 3801398155656628264219997)
                  ·
                    refine ⟨1425524308371235599082499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801398155656628264219997 1425524308371235599082499)
                    ·
                      rfl

theorem cell22_4164298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_4164298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164298 prefixEnd_4164298 := by exact prefixLift 4164298
  have htrace : WordTrace (prefixWord ++ tailWord_4164298) baseStart_4164298 baseEnd_4164298 := by
    simpa [prefixWord, tailWord_4164298, baseEnd_4164298] using wordTrace_append hprefix tailTrace_4164298
  have hstable : (prefixWord ++ tailWord_4164298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164298).length < 2 ^ (prefixWord ++ tailWord_4164298).sum := by decide
  have hdescent : baseEnd_4164298 < baseStart_4164298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164328 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 5]
def baseStart_4164328 : Nat := 118140960795 + 4164328 * 2 ^ 59
def prefixEnd_4164328 : Nat := 4983230072969 + 3 ^ 40 * 4164328 * 2
def baseEnd_4164328 : Nat := 475178192661441840277469

theorem tailTrace_4164328 : CollatzResearch.WordTrace tailWord_4164328 prefixEnd_4164328 475178192661441840277469 := by
  unfold tailWord_4164328
  simp only [CollatzResearch.WordTrace]
  refine ⟨75942760028679170722570819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101257013371572227630094425 75942760028679170722570819)
  ·
    refine ⟨113914140043018756083856229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75942760028679170722570819 113914140043018756083856229)
    ·
      refine ⟨21358901258066016765723043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113914140043018756083856229 21358901258066016765723043)
      ·
        refine ⟨32038351887099025148584565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21358901258066016765723043 32038351887099025148584565)
        ·
          refine ⟨3003595489415533607679803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32038351887099025148584565 3003595489415533607679803)
          ·
            refine ⟨4505393234123300411519705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003595489415533607679803 4505393234123300411519705)
            ·
              refine ⟨3379044925592475308639779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505393234123300411519705 3379044925592475308639779)
              ·
                refine ⟨5068567388388712962959669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379044925592475308639779 5068567388388712962959669)
                ·
                  refine ⟨475178192661441840277469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068567388388712962959669 475178192661441840277469)
                  ·
                    rfl

theorem cell22_4164328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_4164328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164328 prefixEnd_4164328 := by exact prefixLift 4164328
  have htrace : WordTrace (prefixWord ++ tailWord_4164328) baseStart_4164328 baseEnd_4164328 := by
    simpa [prefixWord, tailWord_4164328, baseEnd_4164328] using wordTrace_append hprefix tailTrace_4164328
  have hstable : (prefixWord ++ tailWord_4164328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164328).length < 2 ^ (prefixWord ++ tailWord_4164328).sum := by decide
  have hdescent : baseEnd_4164328 < baseStart_4164328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164337 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_4164337 : Nat := 118140960795 + 4164337 * 2 ^ 59
def prefixEnd_4164337 : Nat := 4983230072969 + 3 ^ 40 * 4164337 * 2
def baseEnd_4164337 : Nat := 1425537658868252497357379

theorem tailTrace_4164337 : CollatzResearch.WordTrace tailWord_4164337 prefixEnd_4164337 1425537658868252497357379 := by
  unfold tailWord_4164337
  simp only [CollatzResearch.WordTrace]
  refine ⟨151885848314325735982219265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101257232209550490654812843 151885848314325735982219265)
  ·
    refine ⟨113914386235744301986664449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151885848314325735982219265 113914386235744301986664449)
    ·
      refine ⟨85435789676808226489998337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113914386235744301986664449 85435789676808226489998337)
      ·
        refine ⟨64076842257606169867498753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85435789676808226489998337 64076842257606169867498753)
        ·
          refine ⟨48057631693204627400624065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64076842257606169867498753 48057631693204627400624065)
          ·
            refine ⟨36043223769903470550468049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48057631693204627400624065 36043223769903470550468049)
            ·
              refine ⟨27032417827427602912851037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36043223769903470550468049 27032417827427602912851037)
              ·
                refine ⟨10137156685285351092319139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27032417827427602912851037 10137156685285351092319139)
                ·
                  refine ⟨15205735027928026638478709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137156685285351092319139 15205735027928026638478709)
                  ·
                    refine ⟨1425537658868252497357379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15205735027928026638478709 1425537658868252497357379)
                    ·
                      rfl

theorem cell22_4164337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_4164337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164337 prefixEnd_4164337 := by exact prefixLift 4164337
  have htrace : WordTrace (prefixWord ++ tailWord_4164337) baseStart_4164337 baseEnd_4164337 := by
    simpa [prefixWord, tailWord_4164337, baseEnd_4164337] using wordTrace_append hprefix tailTrace_4164337
  have hstable : (prefixWord ++ tailWord_4164337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164337).length < 2 ^ (prefixWord ++ tailWord_4164337).sum := by decide
  have hdescent : baseEnd_4164337 < baseStart_4164337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164354 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4164354 : Nat := 118140960795 + 4164354 * 2 ^ 59
def prefixEnd_4164354 : Nat := 4983230072969 + 3 ^ 40 * 4164354 * 2
def baseEnd_4164354 : Nat := 1425543478315670119682327

theorem tailTrace_4164354 : CollatzResearch.WordTrace tailWord_4164354 prefixEnd_4164354 1425543478315670119682327 := by
  unfold tailWord_4164354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37971617088816036971397029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101257645570176098590392077 37971617088816036971397029)
  ·
    refine ⟨7119678204153006932136943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37971617088816036971397029 7119678204153006932136943)
    ·
      refine ⟨10679517306229510398205415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119678204153006932136943 10679517306229510398205415)
      ·
        refine ⟨16019275959344265597308123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679517306229510398205415 16019275959344265597308123)
        ·
          refine ⟨24028913939016398395962185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16019275959344265597308123 24028913939016398395962185)
          ·
            refine ⟨18021685454262298796971639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24028913939016398395962185 18021685454262298796971639)
            ·
              refine ⟨27032528181393448195457459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18021685454262298796971639 27032528181393448195457459)
              ·
                refine ⟨40548792272090172293186189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27032528181393448195457459 40548792272090172293186189)
                ·
                  refine ⟨15205797102033814609944821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40548792272090172293186189 15205797102033814609944821)
                  ·
                    refine ⟨1425543478315670119682327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15205797102033814609944821 1425543478315670119682327)
                    ·
                      rfl

theorem cell22_4164354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4164354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164354 prefixEnd_4164354 := by exact prefixLift 4164354
  have htrace : WordTrace (prefixWord ++ tailWord_4164354) baseStart_4164354 baseEnd_4164354 := by
    simpa [prefixWord, tailWord_4164354, baseEnd_4164354] using wordTrace_append hprefix tailTrace_4164354
  have hstable : (prefixWord ++ tailWord_4164354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164354).length < 2 ^ (prefixWord ++ tailWord_4164354).sum := by decide
  have hdescent : baseEnd_4164354 < baseStart_4164354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164384 : List Nat := [2, 1, 1, 5, 1, 4, 1, 7]
def baseStart_4164384 : Nat := 118140960795 + 4164384 * 2 ^ 59
def prefixEnd_4164384 : Nat := 4983230072969 + 3 ^ 40 * 4164384 * 2
def baseEnd_4164384 : Nat := 158394860880973337936915

theorem tailTrace_4164384 : CollatzResearch.WordTrace tailWord_4164384 prefixEnd_4164384 158394860880973337936915 := by
  unfold tailWord_4164384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75943781272577731504590103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101258375030103642006120137 75943781272577731504590103)
  ·
    refine ⟨113915671908866597256885155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75943781272577731504590103 113915671908866597256885155)
    ·
      refine ⟨170873507863299895885327733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113915671908866597256885155 170873507863299895885327733)
      ·
        refine ⟨16019391362184365239249475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170873507863299895885327733 16019391362184365239249475)
        ·
          refine ⟨24029087043276547858874213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16019391362184365239249475 24029087043276547858874213)
          ·
            refine ⟨4505453820614352723538915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24029087043276547858874213 4505453820614352723538915)
            ·
              refine ⟨6758180730921529085308373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505453820614352723538915 6758180730921529085308373)
              ·
                refine ⟨158394860880973337936915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6758180730921529085308373 158394860880973337936915)
                ·
                  rfl

theorem cell22_4164384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_4164384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164384 prefixEnd_4164384 := by exact prefixLift 4164384
  have htrace : WordTrace (prefixWord ++ tailWord_4164384) baseStart_4164384 baseEnd_4164384 := by
    simpa [prefixWord, tailWord_4164384, baseEnd_4164384] using wordTrace_append hprefix tailTrace_4164384
  have hstable : (prefixWord ++ tailWord_4164384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164384).length < 2 ^ (prefixWord ++ tailWord_4164384).sum := by decide
  have hdescent : baseEnd_4164384 < baseStart_4164384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164412 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_4164412 : Nat := 118140960795 + 4164412 * 2 ^ 59
def prefixEnd_4164412 : Nat := 4983230072969 + 3 ^ 40 * 4164412 * 2
def baseEnd_4164412 : Nat := 475187777633659100577383

theorem tailTrace_4164412 : CollatzResearch.WordTrace tailWord_4164412 prefixEnd_4164412 475187777633659100577383 := by
  unfold tailWord_4164412
  simp only [CollatzResearch.WordTrace]
  refine ⟨75944291894527011895599745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101259055859369349194132993 75944291894527011895599745)
  ·
    refine ⟨56958218920895258921699809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75944291894527011895599745 56958218920895258921699809)
    ·
      refine ⟨42718664190671444191274857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56958218920895258921699809 42718664190671444191274857)
      ·
        refine ⟨32038998143003583143456143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42718664190671444191274857 32038998143003583143456143)
        ·
          refine ⟨48058497214505374715184215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32038998143003583143456143 48058497214505374715184215)
          ·
            refine ⟨72087745821758062072776323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48058497214505374715184215 72087745821758062072776323)
            ·
              refine ⟨108131618732637093109164485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72087745821758062072776323 108131618732637093109164485)
              ·
                refine ⟨20274678512369454957968341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108131618732637093109164485 20274678512369454957968341)
                ·
                  refine ⟨475187777633659100577383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20274678512369454957968341 475187777633659100577383)
                  ·
                    rfl

theorem cell22_4164412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_4164412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164412 prefixEnd_4164412 := by exact prefixLift 4164412
  have htrace : WordTrace (prefixWord ++ tailWord_4164412) baseStart_4164412 baseEnd_4164412 := by
    simpa [prefixWord, tailWord_4164412, baseEnd_4164412] using wordTrace_append hprefix tailTrace_4164412
  have hstable : (prefixWord ++ tailWord_4164412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164412).length < 2 ^ (prefixWord ++ tailWord_4164412).sum := by decide
  have hdescent : baseEnd_4164412 < baseStart_4164412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164422 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4164422 : Nat := 118140960795 + 4164422 * 2 ^ 59
def prefixEnd_4164422 : Nat := 4983230072969 + 3 ^ 40 * 4164422 * 2
def baseEnd_4164422 : Nat := 1425566756105340608982119

theorem tailTrace_4164422 : CollatzResearch.WordTrace tailWord_4164422 prefixEnd_4164422 1425566756105340608982119 := by
  unfold tailWord_4164422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746529641219306109345735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101259299012678530332709013 4746529641219306109345735)
  ·
    refine ⟨7119794461828959164018603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746529641219306109345735 7119794461828959164018603)
    ·
      refine ⟨10679691692743438746027905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119794461828959164018603 10679691692743438746027905)
      ·
        refine ⟨8009768769557579059520929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10679691692743438746027905 8009768769557579059520929)
        ·
          refine ⟨6007326577168184294640697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8009768769557579059520929 6007326577168184294640697)
          ·
            refine ⟨4505494932876138220980523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6007326577168184294640697 4505494932876138220980523)
            ·
              refine ⟨6758242399314207331470785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505494932876138220980523 6758242399314207331470785)
              ·
                refine ⟨5068681799485655498603089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758242399314207331470785 5068681799485655498603089)
                ·
                  refine ⟨3801511349614241623952317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068681799485655498603089 3801511349614241623952317)
                  ·
                    refine ⟨1425566756105340608982119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801511349614241623952317 1425566756105340608982119)
                    ·
                      rfl

theorem cell22_4164422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4164422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164422 prefixEnd_4164422 := by exact prefixLift 4164422
  have htrace : WordTrace (prefixWord ++ tailWord_4164422) baseStart_4164422 baseEnd_4164422 := by
    simpa [prefixWord, tailWord_4164422, baseEnd_4164422] using wordTrace_append hprefix tailTrace_4164422
  have hstable : (prefixWord ++ tailWord_4164422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164422).length < 2 ^ (prefixWord ++ tailWord_4164422).sum := by decide
  have hdescent : baseEnd_4164422 < baseStart_4164422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164459 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 1, 4]
def baseStart_4164459 : Nat := 118140960795 + 4164459 * 2 ^ 59
def prefixEnd_4164459 : Nat := 4983230072969 + 3 ^ 40 * 4164459 * 2
def baseEnd_4164459 : Nat := 1425579421961484845807005

theorem tailTrace_4164459 : CollatzResearch.WordTrace tailWord_4164459 prefixEnd_4164459 1425579421961484845807005 := by
  unfold tailWord_4164459
  simp only [CollatzResearch.WordTrace]
  refine ⟨151890298019883750818160431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101260198679922500545440287 151890298019883750818160431)
  ·
    refine ⟨227835447029825626227240647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151890298019883750818160431 227835447029825626227240647)
    ·
      refine ⟨341753170544738439340860971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227835447029825626227240647 341753170544738439340860971)
      ·
        refine ⟨512629755817107659011291457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341753170544738439340860971 512629755817107659011291457)
        ·
          refine ⟨384472316862830744258468593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512629755817107659011291457 384472316862830744258468593)
          ·
            refine ⟨288354237647123058193851445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384472316862830744258468593 288354237647123058193851445)
            ·
              refine ⟨27033209779417786705673573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288354237647123058193851445 27033209779417786705673573)
              ·
                refine ⟨5068726833640835007313795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27033209779417786705673573 5068726833640835007313795)
                ·
                  refine ⟨7603090250461252510970693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068726833640835007313795 7603090250461252510970693)
                  ·
                    refine ⟨1425579421961484845807005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603090250461252510970693 1425579421961484845807005)
                    ·
                      rfl

theorem cell22_4164459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 4].length) (baseStart_4164459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164459 prefixEnd_4164459 := by exact prefixLift 4164459
  have htrace : WordTrace (prefixWord ++ tailWord_4164459) baseStart_4164459 baseEnd_4164459 := by
    simpa [prefixWord, tailWord_4164459, baseEnd_4164459] using wordTrace_append hprefix tailTrace_4164459
  have hstable : (prefixWord ++ tailWord_4164459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164459).length < 2 ^ (prefixWord ++ tailWord_4164459).sum := by decide
  have hdescent : baseEnd_4164459 < baseStart_4164459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164557 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4164557 : Nat := 118140960795 + 4164557 * 2 ^ 59
def prefixEnd_4164557 : Nat := 4983230072969 + 3 ^ 40 * 4164557 * 2
def baseEnd_4164557 : Nat := 1425612969364245256856705

theorem tailTrace_4164557 : CollatzResearch.WordTrace tailWord_4164557 prefixEnd_4164557 1425612969364245256856705 := by
  unfold tailWord_4164557
  simp only [CollatzResearch.WordTrace]
  refine ⟨151893872373528713555227925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101262581582352475703485283 151893872373528713555227925)
  ·
    refine ⟨7120025267509158447901309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151893872373528713555227925 7120025267509158447901309)
    ·
      refine ⟨2670009475315934417962991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7120025267509158447901309 2670009475315934417962991)
      ·
        refine ⟨4005014212973901626944487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670009475315934417962991 4005014212973901626944487)
        ·
          refine ⟨6007521319460852440416731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005014212973901626944487 6007521319460852440416731)
          ·
            refine ⟨9011281979191278660625097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007521319460852440416731 9011281979191278660625097)
            ·
              refine ⟨6758461484393458995468823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011281979191278660625097 6758461484393458995468823)
              ·
                refine ⟨10137692226590188493203235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758461484393458995468823 10137692226590188493203235)
                ·
                  refine ⟨15206538339885282739804853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137692226590188493203235 15206538339885282739804853)
                  ·
                    refine ⟨1425612969364245256856705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15206538339885282739804853 1425612969364245256856705)
                    ·
                      rfl

theorem cell22_4164557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4164557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164557 prefixEnd_4164557 := by exact prefixLift 4164557
  have htrace : WordTrace (prefixWord ++ tailWord_4164557) baseStart_4164557 baseEnd_4164557 := by
    simpa [prefixWord, tailWord_4164557, baseEnd_4164557] using wordTrace_append hprefix tailTrace_4164557
  have hstable : (prefixWord ++ tailWord_4164557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164557).length < 2 ^ (prefixWord ++ tailWord_4164557).sum := by decide
  have hdescent : baseEnd_4164557 < baseStart_4164557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164579 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_4164579 : Nat := 118140960795 + 4164579 * 2 ^ 59
def prefixEnd_4164579 : Nat := 4983230072969 + 3 ^ 40 * 4164579 * 2
def baseEnd_4164579 : Nat := 1425620500413844532806637

theorem tailTrace_4164579 : CollatzResearch.WordTrace tailWord_4164579 prefixEnd_4164579 1425620500413844532806637 := by
  unfold tailWord_4164579
  simp only [CollatzResearch.WordTrace]
  refine ⟨151894674779449011312528791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101263116519632674208352527 151894674779449011312528791)
  ·
    refine ⟨227842012169173516968793187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151894674779449011312528791 227842012169173516968793187)
    ·
      refine ⟨341763018253760275453189781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227842012169173516968793187 341763018253760275453189781)
      ·
        refine ⟨16020141480645012911868271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 341763018253760275453189781 16020141480645012911868271)
        ·
          refine ⟨24030212220967519367802407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020141480645012911868271 24030212220967519367802407)
          ·
            refine ⟨36045318331451279051703611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24030212220967519367802407 36045318331451279051703611)
            ·
              refine ⟨54067977497176918577555417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36045318331451279051703611 54067977497176918577555417)
              ·
                refine ⟨40550983122882688933166563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54067977497176918577555417 40550983122882688933166563)
                ·
                  refine ⟨60826474684324033399749845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40550983122882688933166563 60826474684324033399749845)
                  ·
                    refine ⟨1425620500413844532806637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60826474684324033399749845 1425620500413844532806637)
                    ·
                      rfl

theorem cell22_4164579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_4164579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164579 prefixEnd_4164579 := by exact prefixLift 4164579
  have htrace : WordTrace (prefixWord ++ tailWord_4164579) baseStart_4164579 baseEnd_4164579 := by
    simpa [prefixWord, tailWord_4164579, baseEnd_4164579] using wordTrace_append hprefix tailTrace_4164579
  have hstable : (prefixWord ++ tailWord_4164579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164579).length < 2 ^ (prefixWord ++ tailWord_4164579).sum := by decide
  have hdescent : baseEnd_4164579 < baseStart_4164579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164598 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4164598 : Nat := 118140960795 + 4164598 * 2 ^ 59
def prefixEnd_4164598 : Nat := 4983230072969 + 3 ^ 40 * 4164598 * 2
def baseEnd_4164598 : Nat := 475209001500711605527193

theorem tailTrace_4164598 : CollatzResearch.WordTrace tailWord_4164598 prefixEnd_4164598 475209001500711605527193 := by
  unfold tailWord_4164598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493460485398761097341903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101263578510920118371646965 9493460485398761097341903)
  ·
    refine ⟨14240190728098141646012855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9493460485398761097341903 14240190728098141646012855)
    ·
      refine ⟨21360286092147212469019283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14240190728098141646012855 21360286092147212469019283)
      ·
        refine ⟨32040429138220818703528925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21360286092147212469019283 32040429138220818703528925)
        ·
          refine ⟨12015160926832807013823347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32040429138220818703528925 12015160926832807013823347)
          ·
            refine ⟨18022741390249210520735021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12015160926832807013823347 18022741390249210520735021)
            ·
              refine ⟨6758528021343453945275633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18022741390249210520735021 6758528021343453945275633)
              ·
                refine ⟨5068896016007590458956725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758528021343453945275633 5068896016007590458956725)
                ·
                  refine ⟨475209001500711605527193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068896016007590458956725 475209001500711605527193)
                  ·
                    rfl

theorem cell22_4164598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4164598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164598 prefixEnd_4164598 := by exact prefixLift 4164598
  have htrace : WordTrace (prefixWord ++ tailWord_4164598) baseStart_4164598 baseEnd_4164598 := by
    simpa [prefixWord, tailWord_4164598, baseEnd_4164598] using wordTrace_append hprefix tailTrace_4164598
  have hstable : (prefixWord ++ tailWord_4164598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164598).length < 2 ^ (prefixWord ++ tailWord_4164598).sum := by decide
  have hdescent : baseEnd_4164598 < baseStart_4164598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164643 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 4]
def baseStart_4164643 : Nat := 118140960795 + 4164643 * 2 ^ 59
def prefixEnd_4164643 : Nat := 4983230072969 + 3 ^ 40 * 4164643 * 2
def baseEnd_4164643 : Nat := 475214136307256566402147

theorem tailTrace_4164643 : CollatzResearch.WordTrace tailWord_4164643 prefixEnd_4164643 475214136307256566402147 := by
  unfold tailWord_4164643
  simp only [CollatzResearch.WordTrace]
  refine ⟨151897009051217150242858583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101264672700811433495239055 151897009051217150242858583)
  ·
    refine ⟨227845513576825725364287875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151897009051217150242858583 227845513576825725364287875)
    ·
      refine ⟨341768270365238588046431813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227845513576825725364287875 341768270365238588046431813)
      ·
        refine ⟨64081550693482235258705965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341768270365238588046431813 64081550693482235258705965)
        ·
          refine ⟨24030581510055838222014737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64081550693482235258705965 24030581510055838222014737)
          ·
            refine ⟨18022936132541878666511053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24030581510055838222014737 18022936132541878666511053)
            ·
              refine ⟨6758601049703204499941645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18022936132541878666511053 6758601049703204499941645)
              ·
                refine ⟨2534475393638701687478117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6758601049703204499941645 2534475393638701687478117)
                ·
                  refine ⟨475214136307256566402147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534475393638701687478117 475214136307256566402147)
                  ·
                    rfl

theorem cell22_4164643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 4].length) (baseStart_4164643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164643 prefixEnd_4164643 := by exact prefixLift 4164643
  have htrace : WordTrace (prefixWord ++ tailWord_4164643) baseStart_4164643 baseEnd_4164643 := by
    simpa [prefixWord, tailWord_4164643, baseEnd_4164643] using wordTrace_append hprefix tailTrace_4164643
  have hstable : (prefixWord ++ tailWord_4164643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164643).length < 2 ^ (prefixWord ++ tailWord_4164643).sum := by decide
  have hdescent : baseEnd_4164643 < baseStart_4164643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164656 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_4164656 : Nat := 118140960795 + 4164656 * 2 ^ 59
def prefixEnd_4164656 : Nat := 4983230072969 + 3 ^ 40 * 4164656 * 2
def baseEnd_4164656 : Nat := 1425646859087441998631401

theorem tailTrace_4164656 : CollatzResearch.WordTrace tailWord_4164656 prefixEnd_4164656 1425646859087441998631401 := by
  unfold tailWord_4164656
  simp only [CollatzResearch.WordTrace]
  refine ⟨75948741600085026731540911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101264988800113368975387881 75948741600085026731540911)
  ·
    refine ⟨113923112400127540097311367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75948741600085026731540911 113923112400127540097311367)
    ·
      refine ⟨170884668600191310145967051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113923112400127540097311367 170884668600191310145967051)
      ·
        refine ⟨256327002900286965218950577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170884668600191310145967051 256327002900286965218950577)
        ·
          refine ⟨192245252175215223914212933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256327002900286965218950577 192245252175215223914212933)
          ·
            refine ⟨36045984782852854483914925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192245252175215223914212933 36045984782852854483914925)
            ·
              refine ⟨13517244293569820431468097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36045984782852854483914925 13517244293569820431468097)
              ·
                refine ⟨10137933220177365323601073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13517244293569820431468097 10137933220177365323601073)
                ·
                  refine ⟨7603449915133023992700805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137933220177365323601073 7603449915133023992700805)
                  ·
                    refine ⟨1425646859087441998631401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603449915133023992700805 1425646859087441998631401)
                    ·
                      rfl

theorem cell22_4164656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_4164656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164656 prefixEnd_4164656 := by exact prefixLift 4164656
  have htrace : WordTrace (prefixWord ++ tailWord_4164656) baseStart_4164656 baseEnd_4164656 := by
    simpa [prefixWord, tailWord_4164656, baseEnd_4164656] using wordTrace_append hprefix tailTrace_4164656
  have hstable : (prefixWord ++ tailWord_4164656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164656).length < 2 ^ (prefixWord ++ tailWord_4164656).sum := by decide
  have hdescent : baseEnd_4164656 < baseStart_4164656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164658 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_4164658 : Nat := 118140960795 + 4164658 * 2 ^ 59
def prefixEnd_4164658 : Nat := 4983230072969 + 3 ^ 40 * 4164658 * 2
def baseEnd_4164658 : Nat := 1425647543728314660081395

theorem tailTrace_4164658 : CollatzResearch.WordTrace tailWord_4164658 prefixEnd_4164658 1425647543728314660081395 := by
  unfold tailWord_4164658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37974389036540701951163657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101265037430775205203103085 37974389036540701951163657)
  ·
    refine ⟨28480791777405526463372743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37974389036540701951163657 28480791777405526463372743)
    ·
      refine ⟨42721187666108289695059115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28480791777405526463372743 42721187666108289695059115)
      ·
        refine ⟨64081781499162434542588673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42721187666108289695059115 64081781499162434542588673)
        ·
          refine ⟨48061336124371825906941505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64081781499162434542588673 48061336124371825906941505)
          ·
            refine ⟨36046002093278869430206129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48061336124371825906941505 36046002093278869430206129)
            ·
              refine ⟨27034501569959152072654597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36046002093278869430206129 27034501569959152072654597)
              ·
                refine ⟨5068969044367341013622737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27034501569959152072654597 5068969044367341013622737)
                ·
                  refine ⟨3801726783275505760217053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068969044367341013622737 3801726783275505760217053)
                  ·
                    refine ⟨1425647543728314660081395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801726783275505760217053 1425647543728314660081395)
                    ·
                      rfl

theorem cell22_4164658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_4164658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164658 prefixEnd_4164658 := by exact prefixLift 4164658
  have htrace : WordTrace (prefixWord ++ tailWord_4164658) baseStart_4164658 baseEnd_4164658 := by
    simpa [prefixWord, tailWord_4164658, baseEnd_4164658] using wordTrace_append hprefix tailTrace_4164658
  have hstable : (prefixWord ++ tailWord_4164658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164658).length < 2 ^ (prefixWord ++ tailWord_4164658).sum := by decide
  have hdescent : baseEnd_4164658 < baseStart_4164658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164660 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 6]
def baseStart_4164660 : Nat := 118140960795 + 4164660 * 2 ^ 59
def prefixEnd_4164660 : Nat := 4983230072969 + 3 ^ 40 * 4164660 * 2
def baseEnd_4164660 : Nat := 475216076123062440510463

theorem tailTrace_4164660 : CollatzResearch.WordTrace tailWord_4164660 prefixEnd_4164660 475216076123062440510463 := by
  unfold tailWord_4164660
  simp only [CollatzResearch.WordTrace]
  refine ⟨75948814546077781073113717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101265086061437041430818289 75948814546077781073113717)
  ·
    refine ⟨7120201363694791975604411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75948814546077781073113717 7120201363694791975604411)
    ·
      refine ⟨10680302045542187963406617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120201363694791975604411 10680302045542187963406617)
      ·
        refine ⟨8010226534156640972554963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10680302045542187963406617 8010226534156640972554963)
        ·
          refine ⟨12015339801234961458832445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010226534156640972554963 12015339801234961458832445)
          ·
            refine ⟨4505752425463110547062167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12015339801234961458832445 4505752425463110547062167)
            ·
              refine ⟨6758628638194665820593251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505752425463110547062167 6758628638194665820593251)
              ·
                refine ⟨10137942957291998730889877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758628638194665820593251 10137942957291998730889877)
                ·
                  refine ⟨475216076123062440510463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10137942957291998730889877 475216076123062440510463)
                  ·
                    rfl

theorem cell22_4164660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_4164660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164660 prefixEnd_4164660 := by exact prefixLift 4164660
  have htrace : WordTrace (prefixWord ++ tailWord_4164660) baseStart_4164660 baseEnd_4164660 := by
    simpa [prefixWord, tailWord_4164660, baseEnd_4164660] using wordTrace_append hprefix tailTrace_4164660
  have hstable : (prefixWord ++ tailWord_4164660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164660).length < 2 ^ (prefixWord ++ tailWord_4164660).sum := by decide
  have hdescent : baseEnd_4164660 < baseStart_4164660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164720 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 1, 3]
def baseStart_4164720 : Nat := 118140960795 + 4164720 * 2 ^ 59
def prefixEnd_4164720 : Nat := 4983230072969 + 3 ^ 40 * 4164720 * 2
def baseEnd_4164720 : Nat := 1425668767595367165031205

theorem tailTrace_4164720 : CollatzResearch.WordTrace tailWord_4164720 prefixEnd_4164720 1425668767595367165031205 := by
  unfold tailWord_4164720
  simp only [CollatzResearch.WordTrace]
  refine ⟨75949908735969096196705807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101266544981292128262274409 75949908735969096196705807)
  ·
    refine ⟨113924863103953644295058711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75949908735969096196705807 113924863103953644295058711)
    ·
      refine ⟨170887294655930466442588067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113924863103953644295058711 170887294655930466442588067)
      ·
        refine ⟨256330941983895699663882101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170887294655930466442588067 256330941983895699663882101)
        ·
          refine ⟨24031025810990221843488947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256330941983895699663882101 24031025810990221843488947)
          ·
            refine ⟨36046538716485332765233421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24031025810990221843488947 36046538716485332765233421)
            ·
              refine ⟨13517452018681999786962533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36046538716485332765233421 13517452018681999786962533)
              ·
                refine ⟨2534522253502874960055475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13517452018681999786962533 2534522253502874960055475)
                ·
                  refine ⟨3801783380254312440083213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534522253502874960055475 3801783380254312440083213)
                  ·
                    refine ⟨1425668767595367165031205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801783380254312440083213 1425668767595367165031205)
                    ·
                      rfl

theorem cell22_4164720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_4164720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164720 prefixEnd_4164720 := by exact prefixLift 4164720
  have htrace : WordTrace (prefixWord ++ tailWord_4164720) baseStart_4164720 baseEnd_4164720 := by
    simpa [prefixWord, tailWord_4164720, baseEnd_4164720] using wordTrace_append hprefix tailTrace_4164720
  have hstable : (prefixWord ++ tailWord_4164720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164720).length < 2 ^ (prefixWord ++ tailWord_4164720).sum := by decide
  have hdescent : baseEnd_4164720 < baseStart_4164720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164767 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 5]
def baseStart_4164767 : Nat := 118140960795 + 4164767 * 2 ^ 59
def prefixEnd_4164767 : Nat := 4983230072969 + 3 ^ 40 * 4164767 * 2
def baseEnd_4164767 : Nat := 475228285551958236368687

theorem tailTrace_4164767 : CollatzResearch.WordTrace tailWord_4164767 prefixEnd_4164767 475228285551958236368687 := by
  unfold tailWord_4164767
  simp only [CollatzResearch.WordTrace]
  refine ⟨151901531702767919420372555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101267687801845279613581703 151901531702767919420372555)
  ·
    refine ⟨227852297554151879130558833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151901531702767919420372555 227852297554151879130558833)
    ·
      refine ⟨170889223165613909347919125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227852297554151879130558833 170889223165613909347919125)
      ·
        refine ⟨8010432335888152000683709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170889223165613909347919125 8010432335888152000683709)
        ·
          refine ⟨3003912125958057000256391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8010432335888152000683709 3003912125958057000256391)
          ·
            refine ⟨4505868188937085500384587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003912125958057000256391 4505868188937085500384587)
            ·
              refine ⟨6758802283405628250576881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505868188937085500384587 6758802283405628250576881)
              ·
                refine ⟨5069101712554221187932661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758802283405628250576881 5069101712554221187932661)
                ·
                  refine ⟨475228285551958236368687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5069101712554221187932661 475228285551958236368687)
                  ·
                    rfl

theorem cell22_4164767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 5].length) (baseStart_4164767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164767 prefixEnd_4164767 := by exact prefixLift 4164767
  have htrace : WordTrace (prefixWord ++ tailWord_4164767) baseStart_4164767 baseEnd_4164767 := by
    simpa [prefixWord, tailWord_4164767, baseEnd_4164767] using wordTrace_append hprefix tailTrace_4164767
  have hstable : (prefixWord ++ tailWord_4164767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164767).length < 2 ^ (prefixWord ++ tailWord_4164767).sum := by decide
  have hdescent : baseEnd_4164767 < baseStart_4164767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164791 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_4164791 : Nat := 118140960795 + 4164791 * 2 ^ 59
def prefixEnd_4164791 : Nat := 4983230072969 + 3 ^ 40 * 4164791 * 2
def baseEnd_4164791 : Nat := 1425693072346346646505987

theorem tailTrace_4164791 : CollatzResearch.WordTrace tailWord_4164791 prefixEnd_4164791 1425693072346346646505987 := by
  unfold tailWord_4164791
  simp only [CollatzResearch.WordTrace]
  refine ⟨151902407054680971519246227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101268271369787314346164151 151902407054680971519246227)
  ·
    refine ⟨227853610582021457278869341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151902407054680971519246227 227853610582021457278869341)
    ·
      refine ⟨85445103968258046479576003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227853610582021457278869341 85445103968258046479576003)
      ·
        refine ⟨128167655952387069719364005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85445103968258046479576003 128167655952387069719364005)
        ·
          refine ⟨24031435491072575572380751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128167655952387069719364005 24031435491072575572380751)
          ·
            refine ⟨36047153236608863358571127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24031435491072575572380751 36047153236608863358571127)
            ·
              refine ⟨54070729854913295037856691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36047153236608863358571127 54070729854913295037856691)
              ·
                refine ⟨81106094782369942556785037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54070729854913295037856691 81106094782369942556785037)
                ·
                  refine ⟨30414785543388728458794389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81106094782369942556785037 30414785543388728458794389)
                  ·
                    refine ⟨1425693072346346646505987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30414785543388728458794389 1425693072346346646505987)
                    ·
                      rfl

theorem cell22_4164791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_4164791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164791 prefixEnd_4164791 := by exact prefixLift 4164791
  have htrace : WordTrace (prefixWord ++ tailWord_4164791) baseStart_4164791 baseEnd_4164791 := by
    simpa [prefixWord, tailWord_4164791, baseEnd_4164791] using wordTrace_append hprefix tailTrace_4164791
  have hstable : (prefixWord ++ tailWord_4164791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164791).length < 2 ^ (prefixWord ++ tailWord_4164791).sum := by decide
  have hdescent : baseEnd_4164791 < baseStart_4164791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164793 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_4164793 : Nat := 118140960795 + 4164793 * 2 ^ 59
def prefixEnd_4164793 : Nat := 4983230072969 + 3 ^ 40 * 4164793 * 2
def baseEnd_4164793 : Nat := 1425693756987219307955981

theorem tailTrace_4164793 : CollatzResearch.WordTrace tailWord_4164793 prefixEnd_4164793 1425693756987219307955981 := by
  unfold tailWord_4164793
  simp only [CollatzResearch.WordTrace]
  refine ⟨151902480000673725860819033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101268320000449150573879355 151902480000673725860819033)
  ·
    refine ⟨113926860000505294395614275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151902480000673725860819033 113926860000505294395614275)
    ·
      refine ⟨170890290000757941593421413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113926860000505294395614275 170890290000757941593421413)
      ·
        refine ⟨32041929375142114048766515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170890290000757941593421413 32041929375142114048766515)
        ·
          refine ⟨48062894062713171073149773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32041929375142114048766515 48062894062713171073149773)
          ·
            refine ⟨18023585273517439152431165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48062894062713171073149773 18023585273517439152431165)
            ·
              refine ⟨6758844477569039682161687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18023585273517439152431165 6758844477569039682161687)
              ·
                refine ⟨10138266716353559523242531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758844477569039682161687 10138266716353559523242531)
                ·
                  refine ⟨15207400074530339284863797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138266716353559523242531 15207400074530339284863797)
                  ·
                    refine ⟨1425693756987219307955981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15207400074530339284863797 1425693756987219307955981)
                    ·
                      rfl

theorem cell22_4164793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_4164793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164793 prefixEnd_4164793 := by exact prefixLift 4164793
  have htrace : WordTrace (prefixWord ++ tailWord_4164793) baseStart_4164793 baseEnd_4164793 := by
    simpa [prefixWord, tailWord_4164793, baseEnd_4164793] using wordTrace_append hprefix tailTrace_4164793
  have hstable : (prefixWord ++ tailWord_4164793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164793).length < 2 ^ (prefixWord ++ tailWord_4164793).sum := by decide
  have hdescent : baseEnd_4164793 < baseStart_4164793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164829 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 4]
def baseStart_4164829 : Nat := 118140960795 + 4164829 * 2 ^ 59
def prefixEnd_4164829 : Nat := 4983230072969 + 3 ^ 40 * 4164829 * 2
def baseEnd_4164829 : Nat := 475235360174309071351957

theorem tailTrace_4164829 : CollatzResearch.WordTrace tailWord_4164829 prefixEnd_4164829 475235360174309071351957 := by
  unfold tailWord_4164829
  simp only [CollatzResearch.WordTrace]
  refine ⟨151903793028543304009129541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101269195352362202672753027 151903793028543304009129541)
  ·
    refine ⟨28481961192851869501711789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151903793028543304009129541 28481961192851869501711789)
    ·
      refine ⟨10680735447319451063141921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28481961192851869501711789 10680735447319451063141921)
      ·
        refine ⟨8010551585489588297356441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10680735447319451063141921 8010551585489588297356441)
        ·
          refine ⟨6007913689117191223017331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8010551585489588297356441 6007913689117191223017331)
          ·
            refine ⟨9011870533675786834525997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007913689117191223017331 9011870533675786834525997)
            ·
              refine ⟨3379451450128420062947249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9011870533675786834525997 3379451450128420062947249)
              ·
                refine ⟨2534588587596315047210437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379451450128420062947249 2534588587596315047210437)
                ·
                  refine ⟨475235360174309071351957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534588587596315047210437 475235360174309071351957)
                  ·
                    rfl

theorem cell22_4164829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_4164829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164829 prefixEnd_4164829 := by exact prefixLift 4164829
  have htrace : WordTrace (prefixWord ++ tailWord_4164829) baseStart_4164829 baseEnd_4164829 := by
    simpa [prefixWord, tailWord_4164829, baseEnd_4164829] using wordTrace_append hprefix tailTrace_4164829
  have hstable : (prefixWord ++ tailWord_4164829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164829).length < 2 ^ (prefixWord ++ tailWord_4164829).sum := by decide
  have hdescent : baseEnd_4164829 < baseStart_4164829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164913 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 8]
def baseStart_4164913 : Nat := 118140960795 + 4164913 * 2 ^ 59
def prefixEnd_4164913 : Nat := 4983230072969 + 3 ^ 40 * 4164913 * 2
def baseEnd_4164913 : Nat := 475244945146526331651871

theorem tailTrace_4164913 : CollatzResearch.WordTrace tailWord_4164913 prefixEnd_4164913 475244945146526331651871 := by
  unfold tailWord_4164913
  simp only [CollatzResearch.WordTrace]
  refine ⟨151906856760238986355187393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101271237840159324236791595 151906856760238986355187393)
  ·
    refine ⟨113930142570179239766390545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151906856760238986355187393 113930142570179239766390545)
    ·
      refine ⟨85447606927634429824792909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113930142570179239766390545 85447606927634429824792909)
      ·
        refine ⟨32042852597862911184297341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85447606927634429824792909 32042852597862911184297341)
        ·
          refine ⟨12016069724198591694111503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32042852597862911184297341 12016069724198591694111503)
          ·
            refine ⟨18024104586297887541167255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12016069724198591694111503 18024104586297887541167255)
            ·
              refine ⟨27036156879446831311750883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18024104586297887541167255 27036156879446831311750883)
              ·
                refine ⟨40554235319170246967626325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27036156879446831311750883 40554235319170246967626325)
                ·
                  refine ⟨475244945146526331651871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40554235319170246967626325 475244945146526331651871)
                  ·
                    rfl

theorem cell22_4164913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_4164913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164913 prefixEnd_4164913 := by exact prefixLift 4164913
  have htrace : WordTrace (prefixWord ++ tailWord_4164913) baseStart_4164913 baseEnd_4164913 := by
    simpa [prefixWord, tailWord_4164913, baseEnd_4164913] using wordTrace_append hprefix tailTrace_4164913
  have hstable : (prefixWord ++ tailWord_4164913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164913).length < 2 ^ (prefixWord ++ tailWord_4164913).sum := by decide
  have hdescent : baseEnd_4164913 < baseStart_4164913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164928 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_4164928 : Nat := 118140960795 + 4164928 * 2 ^ 59
def prefixEnd_4164928 : Nat := 4983230072969 + 3 ^ 40 * 4164928 * 2
def baseEnd_4164928 : Nat := 1425739970246123955830567

theorem tailTrace_4164928 : CollatzResearch.WordTrace tailWord_4164928 prefixEnd_4164928 1425739970246123955830567 := by
  unfold tailWord_4164928
  simp only [CollatzResearch.WordTrace]
  refine ⟨75953701927592321958491719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101271602570123095944655625 75953701927592321958491719)
  ·
    refine ⟨113930552891388482937737579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75953701927592321958491719 113930552891388482937737579)
    ·
      refine ⟨170895829337082724406606369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113930552891388482937737579 170895829337082724406606369)
      ·
        refine ⟨128171872002812043304954777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170895829337082724406606369 128171872002812043304954777)
        ·
          refine ⟨96128904002109032478716083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128171872002812043304954777 96128904002109032478716083)
          ·
            refine ⟨144193356003163548718074125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96128904002109032478716083 144193356003163548718074125)
            ·
              refine ⟨54072508501186330769277797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144193356003163548718074125 54072508501186330769277797)
              ·
                refine ⟨10138595343972437019239587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54072508501186330769277797 10138595343972437019239587)
                ·
                  refine ⟨15207893015958655528859381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138595343972437019239587 15207893015958655528859381)
                  ·
                    refine ⟨1425739970246123955830567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15207893015958655528859381 1425739970246123955830567)
                    ·
                      rfl

theorem cell22_4164928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_4164928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164928 prefixEnd_4164928 := by exact prefixLift 4164928
  have htrace : WordTrace (prefixWord ++ tailWord_4164928) baseStart_4164928 baseEnd_4164928 := by
    simpa [prefixWord, tailWord_4164928, baseEnd_4164928] using wordTrace_append hprefix tailTrace_4164928
  have hstable : (prefixWord ++ tailWord_4164928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164928).length < 2 ^ (prefixWord ++ tailWord_4164928).sum := by decide
  have hdescent : baseEnd_4164928 < baseStart_4164928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164945 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_4164945 : Nat := 118140960795 + 4164945 * 2 ^ 59
def prefixEnd_4164945 : Nat := 4983230072969 + 3 ^ 40 * 4164945 * 2
def baseEnd_4164945 : Nat := 1425745789693541578155515

theorem tailTrace_4164945 : CollatzResearch.WordTrace tailWord_4164945 prefixEnd_4164945 1425745789693541578155515 := by
  unfold tailWord_4164945
  simp only [CollatzResearch.WordTrace]
  refine ⟨151908023896123055820352289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101272015930748703880234859 151908023896123055820352289)
  ·
    refine ⟨113931017922092291865264217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151908023896123055820352289 113931017922092291865264217)
    ·
      refine ⟨85448263441569218898948163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113931017922092291865264217 85448263441569218898948163)
      ·
        refine ⟨128172395162353828348422245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85448263441569218898948163 128172395162353828348422245)
        ·
          refine ⟨24032324092941342815329171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128172395162353828348422245 24032324092941342815329171)
          ·
            refine ⟨36048486139412014222993757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24032324092941342815329171 36048486139412014222993757)
            ·
              refine ⟨13518182302279505333622659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36048486139412014222993757 13518182302279505333622659)
              ·
                refine ⟨20277273453419258000433989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518182302279505333622659 20277273453419258000433989)
                ·
                  refine ⟨3801988772516110875081373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20277273453419258000433989 3801988772516110875081373)
                  ·
                    refine ⟨1425745789693541578155515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801988772516110875081373 1425745789693541578155515)
                    ·
                      rfl

theorem cell22_4164945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_4164945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164945 prefixEnd_4164945 := by exact prefixLift 4164945
  have htrace : WordTrace (prefixWord ++ tailWord_4164945) baseStart_4164945 baseEnd_4164945 := by
    simpa [prefixWord, tailWord_4164945, baseEnd_4164945] using wordTrace_append hprefix tailTrace_4164945
  have hstable : (prefixWord ++ tailWord_4164945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164945).length < 2 ^ (prefixWord ++ tailWord_4164945).sum := by decide
  have hdescent : baseEnd_4164945 < baseStart_4164945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164981 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 4]
def baseStart_4164981 : Nat := 118140960795 + 4164981 * 2 ^ 59
def prefixEnd_4164981 : Nat := 4983230072969 + 3 ^ 40 * 4164981 * 2
def baseEnd_4164981 : Nat := 475252704409749828085135

theorem tailTrace_4164981 : CollatzResearch.WordTrace tailWord_4164981 prefixEnd_4164981 475252704409749828085135 := by
  unfold tailWord_4164981
  simp only [CollatzResearch.WordTrace]
  refine ⟨151909336923992633968662797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101272891282661755979108531 151909336923992633968662797)
  ·
    refine ⟨56966001346497237738248549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151909336923992633968662797 56966001346497237738248549)
    ·
      refine ⟨10681125252468232075921603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56966001346497237738248549 10681125252468232075921603)
      ·
        refine ⟨16021687878702348113882405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10681125252468232075921603 16021687878702348113882405)
        ·
          refine ⟨3004066477256690271352951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16021687878702348113882405 3004066477256690271352951)
          ·
            refine ⟨4506099715885035407029427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004066477256690271352951 4506099715885035407029427)
            ·
              refine ⟨6759149573827553110544141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506099715885035407029427 6759149573827553110544141)
              ·
                refine ⟨2534681090185332416454053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6759149573827553110544141 2534681090185332416454053)
                ·
                  refine ⟨475252704409749828085135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534681090185332416454053 475252704409749828085135)
                  ·
                    rfl

theorem cell22_4164981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_4164981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164981 prefixEnd_4164981 := by exact prefixLift 4164981
  have htrace : WordTrace (prefixWord ++ tailWord_4164981) baseStart_4164981 baseEnd_4164981 := by
    simpa [prefixWord, tailWord_4164981, baseEnd_4164981] using wordTrace_append hprefix tailTrace_4164981
  have hstable : (prefixWord ++ tailWord_4164981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164981).length < 2 ^ (prefixWord ++ tailWord_4164981).sum := by decide
  have hdescent : baseEnd_4164981 < baseStart_4164981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164994 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4164994 : Nat := 118140960795 + 4164994 * 2 ^ 59
def prefixEnd_4164994 : Nat := 4983230072969 + 3 ^ 40 * 4164994 * 2
def baseEnd_4164994 : Nat := 1425762563394921783680365

theorem tailTrace_4164994 : CollatzResearch.WordTrace tailWord_4164994 prefixEnd_4164994 1425762563394921783680365 := by
  unfold tailWord_4164994
  simp only [CollatzResearch.WordTrace]
  refine ⟨37977452768236384297221509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101273207381963691459257357 37977452768236384297221509)
  ·
    refine ⟨7120772394044322055729033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37977452768236384297221509 7120772394044322055729033)
    ·
      refine ⟨5340579295533241541796775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7120772394044322055729033 5340579295533241541796775)
      ·
        refine ⟨8010868943299862312695163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340579295533241541796775 8010868943299862312695163)
        ·
          refine ⟨12016303414949793469042745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010868943299862312695163 12016303414949793469042745)
          ·
            refine ⟨9012227561212345101782059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12016303414949793469042745 9012227561212345101782059)
            ·
              refine ⟨13518341341818517652673089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012227561212345101782059 13518341341818517652673089)
              ·
                refine ⟨10138756006363888239504817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13518341341818517652673089 10138756006363888239504817)
                ·
                  refine ⟨7604067004772916179628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10138756006363888239504817 7604067004772916179628613)
                  ·
                    refine ⟨1425762563394921783680365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7604067004772916179628613 1425762563394921783680365)
                    ·
                      rfl

theorem cell22_4164994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4164994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4164994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4164994 prefixEnd_4164994 := by exact prefixLift 4164994
  have htrace : WordTrace (prefixWord ++ tailWord_4164994) baseStart_4164994 baseEnd_4164994 := by
    simpa [prefixWord, tailWord_4164994, baseEnd_4164994] using wordTrace_append hprefix tailTrace_4164994
  have hstable : (prefixWord ++ tailWord_4164994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164994).length < 2 ^ (prefixWord ++ tailWord_4164994).sum := by decide
  have hdescent : baseEnd_4164994 < baseStart_4164994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165003 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 7]
def baseStart_4165003 : Nat := 118140960795 + 4165003 * 2 ^ 59
def prefixEnd_4165003 : Nat := 4983230072969 + 3 ^ 40 * 4165003 * 2
def baseEnd_4165003 : Nat := 475255214759616253401779

theorem tailTrace_4165003 : CollatzResearch.WordTrace tailWord_4165003 prefixEnd_4165003 475255214759616253401779 := by
  unfold tailWord_4165003
  simp only [CollatzResearch.WordTrace]
  refine ⟨151910139329912931725963663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101273426219941954483975775 151910139329912931725963663)
  ·
    refine ⟨227865208994869397588945495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151910139329912931725963663 227865208994869397588945495)
    ·
      refine ⟨341797813492304096383418243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227865208994869397588945495 341797813492304096383418243)
      ·
        refine ⟨512696720238456144575127365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341797813492304096383418243 512696720238456144575127365)
        ·
          refine ⟨96130635044710527107836381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512696720238456144575127365 96130635044710527107836381)
          ·
            refine ⟨36048988141766447665438643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96130635044710527107836381 36048988141766447665438643)
            ·
              refine ⟨54073482212649671498157965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36048988141766447665438643 54073482212649671498157965)
              ·
                refine ⟨20277555829743626811809237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54073482212649671498157965 20277555829743626811809237)
                ·
                  refine ⟨475255214759616253401779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20277555829743626811809237 475255214759616253401779)
                  ·
                    rfl

theorem cell22_4165003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_4165003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165003 prefixEnd_4165003 := by exact prefixLift 4165003
  have htrace : WordTrace (prefixWord ++ tailWord_4165003) baseStart_4165003 baseEnd_4165003 := by
    simpa [prefixWord, tailWord_4165003, baseEnd_4165003] using wordTrace_append hprefix tailTrace_4165003
  have hstable : (prefixWord ++ tailWord_4165003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165003).length < 2 ^ (prefixWord ++ tailWord_4165003).sum := by decide
  have hdescent : baseEnd_4165003 < baseStart_4165003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165080 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_4165080 : Nat := 118140960795 + 4165080 * 2 ^ 59
def prefixEnd_4165080 : Nat := 4983230072969 + 3 ^ 40 * 4165080 * 2
def baseEnd_4165080 : Nat := 1425792002952446226030101

theorem tailTrace_4165080 : CollatzResearch.WordTrace tailWord_4165080 prefixEnd_4165080 1425792002952446226030101 := by
  unfold tailWord_4165080
  simp only [CollatzResearch.WordTrace]
  refine ⟨75956473875316986938258347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101275298500422649251011129 75956473875316986938258347)
  ·
    refine ⟨113934710812975480407387521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75956473875316986938258347 113934710812975480407387521)
    ·
      refine ⟨85451033109731610305540641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113934710812975480407387521 85451033109731610305540641)
      ·
        refine ⟨64088274832298707729155481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85451033109731610305540641 64088274832298707729155481)
        ·
          refine ⟨48066206124224030796866611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64088274832298707729155481 48066206124224030796866611)
          ·
            refine ⟨72099309186336046195299917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48066206124224030796866611 72099309186336046195299917)
            ·
              refine ⟨27037240944876017323237469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72099309186336046195299917 27037240944876017323237469)
              ·
                refine ⟨10138965354328506496214051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27037240944876017323237469 10138965354328506496214051)
                ·
                  refine ⟨15208448031492759744321077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138965354328506496214051 15208448031492759744321077)
                  ·
                    refine ⟨1425792002952446226030101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15208448031492759744321077 1425792002952446226030101)
                    ·
                      rfl

theorem cell22_4165080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_4165080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165080 prefixEnd_4165080 := by exact prefixLift 4165080
  have htrace : WordTrace (prefixWord ++ tailWord_4165080) baseStart_4165080 baseEnd_4165080 := by
    simpa [prefixWord, tailWord_4165080, baseEnd_4165080] using wordTrace_append hprefix tailTrace_4165080
  have hstable : (prefixWord ++ tailWord_4165080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165080).length < 2 ^ (prefixWord ++ tailWord_4165080).sum := by decide
  have hdescent : baseEnd_4165080 < baseStart_4165080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165131 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 2, 3]
def baseStart_4165131 : Nat := 118140960795 + 4165131 * 2 ^ 59
def prefixEnd_4165131 : Nat := 4983230072969 + 3 ^ 40 * 4165131 * 2
def baseEnd_4165131 : Nat := 1425809461294699093004945

theorem tailTrace_4165131 : CollatzResearch.WordTrace tailWord_4165131 prefixEnd_4165131 1425809461294699093004945 := by
  unfold tailWord_4165131
  simp only [CollatzResearch.WordTrace]
  refine ⟨151914807873449209586623247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101276538582299473057748831 151914807873449209586623247)
  ·
    refine ⟨227872211810173814379934871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151914807873449209586623247 227872211810173814379934871)
    ·
      refine ⟨341808317715260721569902307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227872211810173814379934871 341808317715260721569902307)
      ·
        refine ⟨512712476572891082354853461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341808317715260721569902307 512712476572891082354853461)
        ·
          refine ⟨6008349334838567371345939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 512712476572891082354853461 6008349334838567371345939)
          ·
            refine ⟨9012524002257851057018909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008349334838567371345939 9012524002257851057018909)
            ·
              refine ⟨3379696500846694146382091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9012524002257851057018909 3379696500846694146382091)
              ·
                refine ⟨5069544751270041219573137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379696500846694146382091 5069544751270041219573137)
                ·
                  refine ⟨3802158563452530914679853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5069544751270041219573137 3802158563452530914679853)
                  ·
                    refine ⟨1425809461294699093004945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802158563452530914679853 1425809461294699093004945)
                    ·
                      rfl

theorem cell22_4165131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 3].length) (baseStart_4165131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165131 prefixEnd_4165131 := by exact prefixLift 4165131
  have htrace : WordTrace (prefixWord ++ tailWord_4165131) baseStart_4165131 baseEnd_4165131 := by
    simpa [prefixWord, tailWord_4165131, baseEnd_4165131] using wordTrace_append hprefix tailTrace_4165131
  have hstable : (prefixWord ++ tailWord_4165131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165131).length < 2 ^ (prefixWord ++ tailWord_4165131).sum := by decide
  have hdescent : baseEnd_4165131 < baseStart_4165131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165144 : List Nat := [2, 1, 2, 3, 4, 2, 2, 6]
def baseStart_4165144 : Nat := 118140960795 + 4165144 * 2 ^ 59
def prefixEnd_4165144 : Nat := 4983230072969 + 3 ^ 40 * 4165144 * 2
def baseEnd_4165144 : Nat := 158423767940041265825545

theorem tailTrace_4165144 : CollatzResearch.WordTrace tailWord_4165144 prefixEnd_4165144 158423767940041265825545 := by
  unfold tailWord_4165144
  simp only [CollatzResearch.WordTrace]
  refine ⟨75957641011201056403423243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101276854681601408537897657 75957641011201056403423243)
  ·
    refine ⟨113936461516801584605134865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75957641011201056403423243 113936461516801584605134865)
    ·
      refine ⟨85452346137601188453851149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113936461516801584605134865 85452346137601188453851149)
      ·
        refine ⟨32044629801600445670194181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85452346137601188453851149 32044629801600445670194181)
        ·
          refine ⟨6008368087800083563161409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32044629801600445670194181 6008368087800083563161409)
          ·
            refine ⟨4506276065850062672371057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6008368087800083563161409 4506276065850062672371057)
            ·
              refine ⟨3379707049387547004278293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506276065850062672371057 3379707049387547004278293)
              ·
                refine ⟨158423767940041265825545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3379707049387547004278293 158423767940041265825545)
                ·
                  rfl

theorem cell22_4165144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_4165144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165144 prefixEnd_4165144 := by exact prefixLift 4165144
  have htrace : WordTrace (prefixWord ++ tailWord_4165144) baseStart_4165144 baseEnd_4165144 := by
    simpa [prefixWord, tailWord_4165144, baseEnd_4165144] using wordTrace_append hprefix tailTrace_4165144
  have hstable : (prefixWord ++ tailWord_4165144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165144).length < 2 ^ (prefixWord ++ tailWord_4165144).sum := by decide
  have hdescent : baseEnd_4165144 < baseStart_4165144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165200 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_4165200 : Nat := 118140960795 + 4165200 * 2 ^ 59
def prefixEnd_4165200 : Nat := 4983230072969 + 3 ^ 40 * 4165200 * 2
def baseEnd_4165200 : Nat := 475277693801601971009911

theorem tailTrace_4165200 : CollatzResearch.WordTrace tailWord_4165200 prefixEnd_4165200 475277693801601971009911 := by
  unfold tailWord_4165200
  simp only [CollatzResearch.WordTrace]
  refine ⟨75958662255099617185442527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101278216340132822913923369 75958662255099617185442527)
  ·
    refine ⟨113937993382649425778163791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75958662255099617185442527 113937993382649425778163791)
    ·
      refine ⟨170906990073974138667245687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113937993382649425778163791 170906990073974138667245687)
      ·
        refine ⟨256360485110961208000868531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170906990073974138667245687 256360485110961208000868531)
        ·
          refine ⟨384540727666441812001302797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256360485110961208000868531 384540727666441812001302797)
          ·
            refine ⟨144202772874915679500488549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384540727666441812001302797 144202772874915679500488549)
            ·
              refine ⟨27038019914046689906341603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144202772874915679500488549 27038019914046689906341603)
              ·
                refine ⟨40557029871070034859512405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27038019914046689906341603 40557029871070034859512405)
                ·
                  refine ⟨475277693801601971009911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40557029871070034859512405 475277693801601971009911)
                  ·
                    rfl

theorem cell22_4165200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_4165200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165200 prefixEnd_4165200 := by exact prefixLift 4165200
  have htrace : WordTrace (prefixWord ++ tailWord_4165200) baseStart_4165200 baseEnd_4165200 := by
    simpa [prefixWord, tailWord_4165200, baseEnd_4165200] using wordTrace_append hprefix tailTrace_4165200
  have hstable : (prefixWord ++ tailWord_4165200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165200).length < 2 ^ (prefixWord ++ tailWord_4165200).sum := by decide
  have hdescent : baseEnd_4165200 < baseStart_4165200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165249 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_4165249 : Nat := 118140960795 + 4165249 * 2 ^ 59
def prefixEnd_4165249 : Nat := 4983230072969 + 3 ^ 40 * 4165249 * 2
def baseEnd_4165249 : Nat := 1425849855106186118554583

theorem tailTrace_4165249 : CollatzResearch.WordTrace tailWord_4165249 prefixEnd_4165249 1425849855106186118554583 := by
  unfold tailWord_4165249
  simp only [CollatzResearch.WordTrace]
  refine ⟨151919111687021715739418801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101279407791347810492945867 151919111687021715739418801)
  ·
    refine ⟨113939333765266286804564101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151919111687021715739418801 113939333765266286804564101)
    ·
      refine ⟨21363625080987428775855769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113939333765266286804564101 21363625080987428775855769)
      ·
        refine ⟨16022718810740571581891827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21363625080987428775855769 16022718810740571581891827)
        ·
          refine ⟨24034078216110857372837741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16022718810740571581891827 24034078216110857372837741)
          ·
            refine ⟨9012779331041571514814153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24034078216110857372837741 9012779331041571514814153)
            ·
              refine ⟨6759584498281178636110615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9012779331041571514814153 6759584498281178636110615)
              ·
                refine ⟨10139376747421767954165923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759584498281178636110615 10139376747421767954165923)
                ·
                  refine ⟨15209065121132651931248885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139376747421767954165923 15209065121132651931248885)
                  ·
                    refine ⟨1425849855106186118554583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15209065121132651931248885 1425849855106186118554583)
                    ·
                      rfl

theorem cell22_4165249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_4165249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165249 prefixEnd_4165249 := by exact prefixLift 4165249
  have htrace : WordTrace (prefixWord ++ tailWord_4165249) baseStart_4165249 baseEnd_4165249 := by
    simpa [prefixWord, tailWord_4165249, baseEnd_4165249] using wordTrace_append hprefix tailTrace_4165249
  have hstable : (prefixWord ++ tailWord_4165249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165249).length < 2 ^ (prefixWord ++ tailWord_4165249).sum := by decide
  have hdescent : baseEnd_4165249 < baseStart_4165249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165268 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 4]
def baseStart_4165268 : Nat := 118140960795 + 4165268 * 2 ^ 59
def prefixEnd_4165268 : Nat := 4983230072969 + 3 ^ 40 * 4165268 * 2
def baseEnd_4165268 : Nat := 475285453064825467443175

theorem tailTrace_4165268 : CollatzResearch.WordTrace tailWord_4165268 prefixEnd_4165268 475285453064825467443175 := by
  unfold tailWord_4165268
  simp only [CollatzResearch.WordTrace]
  refine ⟨75959902336976440992180229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101279869782635254656240305 75959902336976440992180229)
  ·
    refine ⟨14242481688183082686033793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75959902336976440992180229 14242481688183082686033793)
    ·
      refine ⟨10681861266137312014525345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14242481688183082686033793 10681861266137312014525345)
      ·
        refine ⟨8011395949602984010894009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10681861266137312014525345 8011395949602984010894009)
        ·
          refine ⟨6008546962202238008170507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8011395949602984010894009 6008546962202238008170507)
          ·
            refine ⟨9012820443303357012255761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008546962202238008170507 9012820443303357012255761)
            ·
              refine ⟨6759615332477517759191821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9012820443303357012255761 6759615332477517759191821)
              ·
                refine ⟨2534855749679069159696933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6759615332477517759191821 2534855749679069159696933)
                ·
                  refine ⟨475285453064825467443175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534855749679069159696933 475285453064825467443175)
                  ·
                    rfl

theorem cell22_4165268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_4165268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165268 prefixEnd_4165268 := by exact prefixLift 4165268
  have htrace : WordTrace (prefixWord ++ tailWord_4165268) baseStart_4165268 baseEnd_4165268 := by
    simpa [prefixWord, tailWord_4165268, baseEnd_4165268] using wordTrace_append hprefix tailTrace_4165268
  have hstable : (prefixWord ++ tailWord_4165268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165268).length < 2 ^ (prefixWord ++ tailWord_4165268).sum := by decide
  have hdescent : baseEnd_4165268 < baseStart_4165268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165279 : List Nat := [1, 1, 2, 7, 1, 1, 9]
def baseStart_4165279 : Nat := 118140960795 + 4165279 * 2 ^ 59
def prefixEnd_4165279 : Nat := 4983230072969 + 3 ^ 40 * 4165279 * 2
def baseEnd_4165279 : Nat := 52809634248862075566833

theorem tailTrace_4165279 : CollatzResearch.WordTrace tailWord_4165279 prefixEnd_4165279 52809634248862075566833 := by
  unfold tailWord_4165279
  simp only [CollatzResearch.WordTrace]
  refine ⟨151920205876913030863010891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101280137251275353908673927 151920205876913030863010891)
  ·
    refine ⟨227880308815369546294516337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151920205876913030863010891 227880308815369546294516337)
    ·
      refine ⟨170910231611527159720887253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227880308815369546294516337 170910231611527159720887253)
      ·
        refine ⟨4005708553395167805958295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 170910231611527159720887253 4005708553395167805958295)
        ·
          refine ⟨6008562830092751708937443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005708553395167805958295 6008562830092751708937443)
          ·
            refine ⟨9012844245139127563406165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008562830092751708937443 9012844245139127563406165)
            ·
              refine ⟨52809634248862075566833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9012844245139127563406165 52809634248862075566833)
              ·
                rfl

theorem cell22_4165279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 9].length) (baseStart_4165279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165279 prefixEnd_4165279 := by exact prefixLift 4165279
  have htrace : WordTrace (prefixWord ++ tailWord_4165279) baseStart_4165279 baseEnd_4165279 := by
    simpa [prefixWord, tailWord_4165279, baseEnd_4165279] using wordTrace_append hprefix tailTrace_4165279
  have hstable : (prefixWord ++ tailWord_4165279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165279).length < 2 ^ (prefixWord ++ tailWord_4165279).sum := by decide
  have hdescent : baseEnd_4165279 < baseStart_4165279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165307 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 5]
def baseStart_4165307 : Nat := 118140960795 + 4165307 * 2 ^ 59
def prefixEnd_4165307 : Nat := 4983230072969 + 3 ^ 40 * 4165307 * 2
def baseEnd_4165307 : Nat := 475289903230497766868135

theorem tailTrace_4165307 : CollatzResearch.WordTrace tailWord_4165307 prefixEnd_4165307 475289903230497766868135 := by
  unfold tailWord_4165307
  simp only [CollatzResearch.WordTrace]
  refine ⟨151921227120811591645030175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101280818080541061096686783 151921227120811591645030175)
  ·
    refine ⟨227881840681217387467545263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151921227120811591645030175 227881840681217387467545263)
    ·
      refine ⟨341822761021826081201317895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227881840681217387467545263 341822761021826081201317895)
      ·
        refine ⟨512734141532739121801976843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341822761021826081201317895 512734141532739121801976843)
        ·
          refine ⟨769101212299108682702965265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512734141532739121801976843 769101212299108682702965265)
          ·
            refine ⟨576825909224331512027223949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769101212299108682702965265 576825909224331512027223949)
            ·
              refine ⟨216309715959124317010208981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576825909224331512027223949 216309715959124317010208981)
              ·
                refine ⟨5069758967791976179926773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 216309715959124317010208981 5069758967791976179926773)
                ·
                  refine ⟨475289903230497766868135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5069758967791976179926773 475289903230497766868135)
                  ·
                    rfl

theorem cell22_4165307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 5].length) (baseStart_4165307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165307 prefixEnd_4165307 := by exact prefixLift 4165307
  have htrace : WordTrace (prefixWord ++ tailWord_4165307) baseStart_4165307 baseEnd_4165307 := by
    simpa [prefixWord, tailWord_4165307, baseEnd_4165307] using wordTrace_append hprefix tailTrace_4165307
  have hstable : (prefixWord ++ tailWord_4165307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165307).length < 2 ^ (prefixWord ++ tailWord_4165307).sum := by decide
  have hdescent : baseEnd_4165307 < baseStart_4165307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165345 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 1, 3]
def baseStart_4165345 : Nat := 118140960795 + 4165345 * 2 ^ 59
def prefixEnd_4165345 : Nat := 4983230072969 + 3 ^ 40 * 4165345 * 2
def baseEnd_4165345 : Nat := 1425882717868073868154289

theorem tailTrace_4165345 : CollatzResearch.WordTrace tailWord_4165345 prefixEnd_4165345 1425882717868073868154289 := by
  unfold tailWord_4165345
  simp only [CollatzResearch.WordTrace]
  refine ⟨151922613094673924134913489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101281742063115949423275659 151922613094673924134913489)
  ·
    refine ⟨113941959821005443101185117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151922613094673924134913489 113941959821005443101185117)
    ·
      refine ⟨42728234932877041162944419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113941959821005443101185117 42728234932877041162944419)
      ·
        refine ⟨64092352399315561744416629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42728234932877041162944419 64092352399315561744416629)
        ·
          refine ⟨6008658037435833913539059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64092352399315561744416629 6008658037435833913539059)
          ·
            refine ⟨9012987056153750870308589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008658037435833913539059 9012987056153750870308589)
            ·
              refine ⟨3379870146057656576365721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9012987056153750870308589 3379870146057656576365721)
              ·
                refine ⟨2534902609543242432274291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379870146057656576365721 2534902609543242432274291)
                ·
                  refine ⟨3802353914314863648411437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534902609543242432274291 3802353914314863648411437)
                  ·
                    refine ⟨1425882717868073868154289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802353914314863648411437 1425882717868073868154289)
                    ·
                      rfl

theorem cell22_4165345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_4165345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165345 prefixEnd_4165345 := by exact prefixLift 4165345
  have htrace : WordTrace (prefixWord ++ tailWord_4165345) baseStart_4165345 baseEnd_4165345 := by
    simpa [prefixWord, tailWord_4165345, baseEnd_4165345] using wordTrace_append hprefix tailTrace_4165345
  have hstable : (prefixWord ++ tailWord_4165345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165345).length < 2 ^ (prefixWord ++ tailWord_4165345).sum := by decide
  have hdescent : baseEnd_4165345 < baseStart_4165345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165384 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_4165384 : Nat := 118140960795 + 4165384 * 2 ^ 59
def prefixEnd_4165384 : Nat := 4983230072969 + 3 ^ 40 * 4165384 * 2
def baseEnd_4165384 : Nat := 1425896068365090766429169

theorem tailTrace_4165384 : CollatzResearch.WordTrace tailWord_4165384 prefixEnd_4165384 1425896068365090766429169 := by
  unfold tailWord_4165384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75962017770766316897791603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101282690361021755863722137 75962017770766316897791603)
  ·
    refine ⟨113943026656149475346687405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75962017770766316897791603 113943026656149475346687405)
    ·
      refine ⟨42728634996056053255007777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113943026656149475346687405 42728634996056053255007777)
      ·
        refine ⟨32046476247042039941255833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42728634996056053255007777 32046476247042039941255833)
        ·
          refine ⟨24034857185281529955941875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32046476247042039941255833 24034857185281529955941875)
          ·
            refine ⟨36052285777922294933912813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24034857185281529955941875 36052285777922294933912813)
            ·
              refine ⟨13519607166720860600217305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36052285777922294933912813 13519607166720860600217305)
              ·
                refine ⟨10139705375040645450162979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13519607166720860600217305 10139705375040645450162979)
                ·
                  refine ⟨15209558062560968175244469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139705375040645450162979 15209558062560968175244469)
                  ·
                    refine ⟨1425896068365090766429169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15209558062560968175244469 1425896068365090766429169)
                    ·
                      rfl

theorem cell22_4165384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_4165384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165384 prefixEnd_4165384 := by exact prefixLift 4165384
  have htrace : WordTrace (prefixWord ++ tailWord_4165384) baseStart_4165384 baseEnd_4165384 := by
    simpa [prefixWord, tailWord_4165384, baseEnd_4165384] using wordTrace_append hprefix tailTrace_4165384
  have hstable : (prefixWord ++ tailWord_4165384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165384).length < 2 ^ (prefixWord ++ tailWord_4165384).sum := by decide
  have hdescent : baseEnd_4165384 < baseStart_4165384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165396 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4165396 : Nat := 118140960795 + 4165396 * 2 ^ 59
def prefixEnd_4165396 : Nat := 4983230072969 + 3 ^ 40 * 4165396 * 2
def baseEnd_4165396 : Nat := 1425900176210326735129133

theorem tailTrace_4165396 : CollatzResearch.WordTrace tailWord_4165396 prefixEnd_4165396 1425900176210326735129133 := by
  unfold tailWord_4165396
  simp only [CollatzResearch.WordTrace]
  refine ⟨75962236608744579922510021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101282982144992773230013361 75962236608744579922510021)
  ·
    refine ⟨14242919364139608735470629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75962236608744579922510021 14242919364139608735470629)
    ·
      refine ⟨2670547380776176637900743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14242919364139608735470629 2670547380776176637900743)
      ·
        refine ⟨4005821071164264956851115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670547380776176637900743 4005821071164264956851115)
        ·
          refine ⟨6008731606746397435276673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005821071164264956851115 6008731606746397435276673)
          ·
            refine ⟨4506548705059798076457505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6008731606746397435276673 4506548705059798076457505)
            ·
              refine ⟨3379911528794848557343129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506548705059798076457505 3379911528794848557343129)
              ·
                refine ⟨2534933646596136418007347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379911528794848557343129 2534933646596136418007347)
                ·
                  refine ⟨3802400469894204627011021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534933646596136418007347 3802400469894204627011021)
                  ·
                    refine ⟨1425900176210326735129133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802400469894204627011021 1425900176210326735129133)
                    ·
                      rfl

theorem cell22_4165396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4165396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165396 prefixEnd_4165396 := by exact prefixLift 4165396
  have htrace : WordTrace (prefixWord ++ tailWord_4165396) baseStart_4165396 baseEnd_4165396 := by
    simpa [prefixWord, tailWord_4165396, baseEnd_4165396] using wordTrace_append hprefix tailTrace_4165396
  have hstable : (prefixWord ++ tailWord_4165396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165396).length < 2 ^ (prefixWord ++ tailWord_4165396).sum := by decide
  have hdescent : baseEnd_4165396 < baseStart_4165396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165397 : List Nat := [1, 3, 2, 1, 2, 13]
def baseStart_4165397 : Nat := 118140960795 + 4165397 * 2 ^ 59
def prefixEnd_4165397 : Nat := 4983230072969 + 3 ^ 40 * 4165397 * 2
def baseEnd_4165397 : Nat := 17603710105318062541409

theorem tailTrace_4165397 : CollatzResearch.WordTrace tailWord_4165397 prefixEnd_4165397 17603710105318062541409 := by
  unfold tailWord_4165397
  simp only [CollatzResearch.WordTrace]
  refine ⟨151924509690485537015806445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101283006460323691343870963 151924509690485537015806445)
  ·
    refine ⟨56971691133932076380927417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151924509690485537015806445 56971691133932076380927417)
    ·
      refine ⟨42728768350449057285695563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56971691133932076380927417 42728768350449057285695563)
      ·
        refine ⟨64093152525673585928543345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42728768350449057285695563 64093152525673585928543345)
        ·
          refine ⟨48069864394255189446407509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64093152525673585928543345 48069864394255189446407509)
          ·
            refine ⟨17603710105318062541409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 48069864394255189446407509 17603710105318062541409)
            ·
              rfl

theorem cell22_4165397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 13].length) (baseStart_4165397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165397 prefixEnd_4165397 := by exact prefixLift 4165397
  have htrace : WordTrace (prefixWord ++ tailWord_4165397) baseStart_4165397 baseEnd_4165397 := by
    simpa [prefixWord, tailWord_4165397, baseEnd_4165397] using wordTrace_append hprefix tailTrace_4165397
  have hstable : (prefixWord ++ tailWord_4165397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165397).length < 2 ^ (prefixWord ++ tailWord_4165397).sum := by decide
  have hdescent : baseEnd_4165397 < baseStart_4165397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165463 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 3, 3]
def baseStart_4165463 : Nat := 118140960795 + 4165463 * 2 ^ 59
def prefixEnd_4165463 : Nat := 4983230072969 + 3 ^ 40 * 4165463 * 2
def baseEnd_4165463 : Nat := 1425923111679560893703927

theorem tailTrace_4165463 : CollatzResearch.WordTrace tailWord_4165463 prefixEnd_4165463 1425923111679560893703927 := by
  unfold tailWord_4165463
  simp only [CollatzResearch.WordTrace]
  refine ⟨151926916908246430287709043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101284611272164286858472695 151926916908246430287709043)
  ·
    refine ⟨227890375362369645431563565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151926916908246430287709043 227890375362369645431563565)
    ·
      refine ⟨85458890760888617036836337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227890375362369645431563565 85458890760888617036836337)
      ·
        refine ⟨64094168070666462777627253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85458890760888617036836337 64094168070666462777627253)
        ·
          refine ⟨6008828256624980885402555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64094168070666462777627253 6008828256624980885402555)
          ·
            refine ⟨9013242384937471328103833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008828256624980885402555 9013242384937471328103833)
            ·
              refine ⟨6759931788703103496077875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013242384937471328103833 6759931788703103496077875)
              ·
                refine ⟨10139897683054655244116813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759931788703103496077875 10139897683054655244116813)
                ·
                  refine ⟨3802461631145495716543805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10139897683054655244116813 3802461631145495716543805)
                  ·
                    refine ⟨1425923111679560893703927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802461631145495716543805 1425923111679560893703927)
                    ·
                      rfl

theorem cell22_4165463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_4165463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165463 prefixEnd_4165463 := by exact prefixLift 4165463
  have htrace : WordTrace (prefixWord ++ tailWord_4165463) baseStart_4165463 baseEnd_4165463 := by
    simpa [prefixWord, tailWord_4165463, baseEnd_4165463] using wordTrace_append hprefix tailTrace_4165463
  have hstable : (prefixWord ++ tailWord_4165463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165463).length < 2 ^ (prefixWord ++ tailWord_4165463).sum := by decide
  have hdescent : baseEnd_4165463 < baseStart_4165463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165521 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 4]
def baseStart_4165521 : Nat := 118140960795 + 4165521 * 2 ^ 59
def prefixEnd_4165521 : Nat := 4983230072969 + 3 ^ 40 * 4165521 * 2
def baseEnd_4165521 : Nat := 475314322088289358584583

theorem tailTrace_4165521 : CollatzResearch.WordTrace tailWord_4165521 prefixEnd_4165521 475314322088289358584583 := by
  unfold tailWord_4165521
  simp only [CollatzResearch.WordTrace]
  refine ⟨151929032342036306193320417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101286021561357537462213611 151929032342036306193320417)
  ·
    refine ⟨113946774256527229644990313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151929032342036306193320417 113946774256527229644990313)
    ·
      refine ⟨85460080692395422233742735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113946774256527229644990313 85460080692395422233742735)
      ·
        refine ⟨128190121038593133350614103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85460080692395422233742735 128190121038593133350614103)
        ·
          refine ⟨192285181557889700025921155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128190121038593133350614103 192285181557889700025921155)
          ·
            refine ⟨288427772336834550038881733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192285181557889700025921155 288427772336834550038881733)
            ·
              refine ⟨54080207313156478132290325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288427772336834550038881733 54080207313156478132290325)
              ·
                refine ⟨2535009717804209912451109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54080207313156478132290325 2535009717804209912451109)
                ·
                  refine ⟨475314322088289358584583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535009717804209912451109 475314322088289358584583)
                  ·
                    rfl

theorem cell22_4165521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_4165521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165521 prefixEnd_4165521 := by exact prefixLift 4165521
  have htrace : WordTrace (prefixWord ++ tailWord_4165521) baseStart_4165521 baseEnd_4165521 := by
    simpa [prefixWord, tailWord_4165521, baseEnd_4165521] using wordTrace_append hprefix tailTrace_4165521
  have hstable : (prefixWord ++ tailWord_4165521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165521).length < 2 ^ (prefixWord ++ tailWord_4165521).sum := by decide
  have hdescent : baseEnd_4165521 < baseStart_4165521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165551 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 2, 4]
def baseStart_4165551 : Nat := 118140960795 + 4165551 * 2 ^ 59
def prefixEnd_4165551 : Nat := 4983230072969 + 3 ^ 40 * 4165551 * 2
def baseEnd_4165551 : Nat := 1425953235877957997503657

theorem tailTrace_4165551 : CollatzResearch.WordTrace tailWord_4165551 prefixEnd_4165551 1425953235877957997503657 := by
  unfold tailWord_4165551
  simp only [CollatzResearch.WordTrace]
  refine ⟨151930126531927621316912507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101286751021285080877941671 151930126531927621316912507)
  ·
    refine ⟨227895189797891431975368761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151930126531927621316912507 227895189797891431975368761)
    ·
      refine ⟨170921392348418573981526571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227895189797891431975368761 170921392348418573981526571)
      ·
        refine ⟨256382088522627860972289857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170921392348418573981526571 256382088522627860972289857)
        ·
          refine ⟨192286566391970895729217393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256382088522627860972289857 192286566391970895729217393)
          ·
            refine ⟨144214924793978171796913045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192286566391970895729217393 144214924793978171796913045)
            ·
              refine ⟨6760074599717726802980299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144214924793978171796913045 6760074599717726802980299)
              ·
                refine ⟨10140111899576590204470449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760074599717726802980299 10140111899576590204470449)
                ·
                  refine ⟨7605083924682442653352837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10140111899576590204470449 7605083924682442653352837)
                  ·
                    refine ⟨1425953235877957997503657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7605083924682442653352837 1425953235877957997503657)
                    ·
                      rfl

theorem cell22_4165551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_4165551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165551 prefixEnd_4165551 := by exact prefixLift 4165551
  have htrace : WordTrace (prefixWord ++ tailWord_4165551) baseStart_4165551 baseEnd_4165551 := by
    simpa [prefixWord, tailWord_4165551, baseEnd_4165551] using wordTrace_append hprefix tailTrace_4165551
  have hstable : (prefixWord ++ tailWord_4165551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165551).length < 2 ^ (prefixWord ++ tailWord_4165551).sum := by decide
  have hdescent : baseEnd_4165551 < baseStart_4165551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165579 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_4165579 : Nat := 118140960795 + 4165579 * 2 ^ 59
def prefixEnd_4165579 : Nat := 4983230072969 + 3 ^ 40 * 4165579 * 2
def baseEnd_4165579 : Nat := 1425962820850175257803571

theorem tailTrace_4165579 : CollatzResearch.WordTrace tailWord_4165579 prefixEnd_4165579 1425962820850175257803571 := by
  unfold tailWord_4165579
  simp only [CollatzResearch.WordTrace]
  refine ⟨151931147775826182098931791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101287431850550788065954527 151931147775826182098931791)
  ·
    refine ⟨227896721663739273148397687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151931147775826182098931791 227896721663739273148397687)
    ·
      refine ⟨341845082495608909722596531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227896721663739273148397687 341845082495608909722596531)
      ·
        refine ⟨512767623743413364583894797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341845082495608909722596531 512767623743413364583894797)
        ·
          refine ⟨192287858903780011718960549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512767623743413364583894797 192287858903780011718960549)
          ·
            refine ⟨36053973544458752197305103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192287858903780011718960549 36053973544458752197305103)
            ·
              refine ⟨54080960316688128295957655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36053973544458752197305103 54080960316688128295957655)
              ·
                refine ⟨81121440475032192443936483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54080960316688128295957655 81121440475032192443936483)
                ·
                  refine ⟨121682160712548288665904725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81121440475032192443936483 121682160712548288665904725)
                  ·
                    refine ⟨1425962820850175257803571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121682160712548288665904725 1425962820850175257803571)
                    ·
                      rfl

theorem cell22_4165579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_4165579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165579 prefixEnd_4165579 := by exact prefixLift 4165579
  have htrace : WordTrace (prefixWord ++ tailWord_4165579) baseStart_4165579 baseEnd_4165579 := by
    simpa [prefixWord, tailWord_4165579, baseEnd_4165579] using wordTrace_append hprefix tailTrace_4165579
  have hstable : (prefixWord ++ tailWord_4165579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165579).length < 2 ^ (prefixWord ++ tailWord_4165579).sum := by decide
  have hdescent : baseEnd_4165579 < baseStart_4165579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165602 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4165602 : Nat := 118140960795 + 4165602 * 2 ^ 59
def prefixEnd_4165602 : Nat := 4983230072969 + 3 ^ 40 * 4165602 * 2
def baseEnd_4165602 : Nat := 1425970694220210864478501

theorem tailTrace_4165602 : CollatzResearch.WordTrace tailWord_4165602 prefixEnd_4165602 1425970694220210864478501 := by
  unfold tailWord_4165602
  simp only [CollatzResearch.WordTrace]
  refine ⟨37982996663685714256754765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101287991103161904684679373 37982996663685714256754765)
  ·
    refine ⟨14243623748882142846283037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37982996663685714256754765 14243623748882142846283037)
    ·
      refine ⟨5341358905830803567356139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14243623748882142846283037 5341358905830803567356139)
      ·
        refine ⟨8012038358746205351034209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341358905830803567356139 8012038358746205351034209)
        ·
          refine ⟨6009028769059654013275657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8012038358746205351034209 6009028769059654013275657)
          ·
            refine ⟨4506771576794740509956743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6009028769059654013275657 4506771576794740509956743)
            ·
              refine ⟨6760157365192110764935115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506771576794740509956743 6760157365192110764935115)
              ·
                refine ⟨10140236047788166147402673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760157365192110764935115 10140236047788166147402673)
                ·
                  refine ⟨7605177035841124610552005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10140236047788166147402673 7605177035841124610552005)
                  ·
                    refine ⟨1425970694220210864478501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7605177035841124610552005 1425970694220210864478501)
                    ·
                      rfl

theorem cell22_4165602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4165602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165602 prefixEnd_4165602 := by exact prefixLift 4165602
  have htrace : WordTrace (prefixWord ++ tailWord_4165602) baseStart_4165602 baseEnd_4165602 := by
    simpa [prefixWord, tailWord_4165602, baseEnd_4165602] using wordTrace_append hprefix tailTrace_4165602
  have hstable : (prefixWord ++ tailWord_4165602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165602).length < 2 ^ (prefixWord ++ tailWord_4165602).sum := by decide
  have hdescent : baseEnd_4165602 < baseStart_4165602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165615 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 1, 3]
def baseStart_4165615 : Nat := 118140960795 + 4165615 * 2 ^ 59
def prefixEnd_4165615 : Nat := 4983230072969 + 3 ^ 40 * 4165615 * 2
def baseEnd_4165615 : Nat := 1425975144385883163903461

theorem tailTrace_4165615 : CollatzResearch.WordTrace tailWord_4165615 prefixEnd_4165615 1425975144385883163903461 := by
  unfold tailWord_4165615
  simp only [CollatzResearch.WordTrace]
  refine ⟨151932460803695760247242299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101288307202463840164828199 151932460803695760247242299)
  ·
    refine ⟨227898691205543640370863449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151932460803695760247242299 227898691205543640370863449)
    ·
      refine ⟨170924018404157730278147587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227898691205543640370863449 170924018404157730278147587)
      ·
        refine ⟨256386027606236595417221381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170924018404157730278147587 256386027606236595417221381)
        ·
          refine ⟨48072380176169361640729009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256386027606236595417221381 48072380176169361640729009)
          ·
            refine ⟨36054285132127021230546757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48072380176169361640729009 36054285132127021230546757)
            ·
              refine ⟨6760178462273816480727517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36054285132127021230546757 6760178462273816480727517)
              ·
                refine ⟨2535066923352681180272819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6760178462273816480727517 2535066923352681180272819)
                ·
                  refine ⟨3802600385029021770409229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535066923352681180272819 3802600385029021770409229)
                  ·
                    refine ⟨1425975144385883163903461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802600385029021770409229 1425975144385883163903461)
                    ·
                      rfl

theorem cell22_4165615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_4165615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165615 prefixEnd_4165615 := by exact prefixLift 4165615
  have htrace : WordTrace (prefixWord ++ tailWord_4165615) baseStart_4165615 baseEnd_4165615 := by
    simpa [prefixWord, tailWord_4165615, baseEnd_4165615] using wordTrace_append hprefix tailTrace_4165615
  have hstable : (prefixWord ++ tailWord_4165615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165615).length < 2 ^ (prefixWord ++ tailWord_4165615).sum := by decide
  have hdescent : baseEnd_4165615 < baseStart_4165615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165638 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4165638 : Nat := 118140960795 + 4165638 * 2 ^ 59
def prefixEnd_4165638 : Nat := 4983230072969 + 3 ^ 40 * 4165638 * 2
def baseEnd_4165638 : Nat := 1425983017755918770578391

theorem tailTrace_4165638 : CollatzResearch.WordTrace tailWord_4165638 prefixEnd_4165638 1425983017755918770578391 := by
  unfold tailWord_4165638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747915615081638599229049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101288866455074956783553045 4747915615081638599229049)
  ·
    refine ⟨3560936711311228949421787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4747915615081638599229049 3560936711311228949421787)
    ·
      refine ⟨5341405066966843424132681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560936711311228949421787 5341405066966843424132681)
      ·
        refine ⟨4006053800225132568099511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5341405066966843424132681 4006053800225132568099511)
        ·
          refine ⟨6009080700337698852149267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006053800225132568099511 6009080700337698852149267)
          ·
            refine ⟨9013621050506548278223901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009080700337698852149267 9013621050506548278223901)
            ·
              refine ⟨3380107893939955604333963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9013621050506548278223901 3380107893939955604333963)
              ·
                refine ⟨5070161840909933406500945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380107893939955604333963 5070161840909933406500945)
                ·
                  refine ⟨3802621380682450054875709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070161840909933406500945 3802621380682450054875709)
                  ·
                    refine ⟨1425983017755918770578391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802621380682450054875709 1425983017755918770578391)
                    ·
                      rfl

theorem cell22_4165638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4165638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165638 prefixEnd_4165638 := by exact prefixLift 4165638
  have htrace : WordTrace (prefixWord ++ tailWord_4165638) baseStart_4165638 baseEnd_4165638 := by
    simpa [prefixWord, tailWord_4165638, baseEnd_4165638] using wordTrace_append hprefix tailTrace_4165638
  have hstable : (prefixWord ++ tailWord_4165638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165638).length < 2 ^ (prefixWord ++ tailWord_4165638).sum := by decide
  have hdescent : baseEnd_4165638 < baseStart_4165638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165656 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_4165656 : Nat := 118140960795 + 4165656 * 2 ^ 59
def prefixEnd_4165656 : Nat := 4983230072969 + 3 ^ 40 * 4165656 * 2
def baseEnd_4165656 : Nat := 475329726507924241209445

theorem tailTrace_4165656 : CollatzResearch.WordTrace tailWord_4165656 prefixEnd_4165656 475329726507924241209445 := by
  unfold tailWord_4165656
  simp only [CollatzResearch.WordTrace]
  refine ⟨75966978098273612124742411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101289304131031482832989881 75966978098273612124742411)
  ·
    refine ⟨113950467147410418187113617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75966978098273612124742411 113950467147410418187113617)
    ·
      refine ⟨85462850360557813640335213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113950467147410418187113617 85462850360557813640335213)
      ·
        refine ⟨32048568885209180115125705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85462850360557813640335213 32048568885209180115125705)
        ·
          refine ⟨24036426663906885086344279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32048568885209180115125705 24036426663906885086344279)
          ·
            refine ⟨36054639995860327629516419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24036426663906885086344279 36054639995860327629516419)
            ·
              refine ⟨54081959993790491444274629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36054639995860327629516419 54081959993790491444274629)
              ·
                refine ⟨10140367498835717145801493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54081959993790491444274629 10140367498835717145801493)
                ·
                  refine ⟨475329726507924241209445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10140367498835717145801493 475329726507924241209445)
                  ·
                    rfl

theorem cell22_4165656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_4165656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165656 prefixEnd_4165656 := by exact prefixLift 4165656
  have htrace : WordTrace (prefixWord ++ tailWord_4165656) baseStart_4165656 baseEnd_4165656 := by
    simpa [prefixWord, tailWord_4165656, baseEnd_4165656] using wordTrace_append hprefix tailTrace_4165656
  have hstable : (prefixWord ++ tailWord_4165656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165656).length < 2 ^ (prefixWord ++ tailWord_4165656).sum := by decide
  have hdescent : baseEnd_4165656 < baseStart_4165656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165658 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_4165658 : Nat := 118140960795 + 4165658 * 2 ^ 59
def prefixEnd_4165658 : Nat := 4983230072969 + 3 ^ 40 * 4165658 * 2
def baseEnd_4165658 : Nat := 1425989864164645385078329

theorem tailTrace_4165658 : CollatzResearch.WordTrace tailWord_4165658 prefixEnd_4165658 1425989864164645385078329 := by
  unfold tailWord_4165658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37983507285634994647764407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101289352761693319060705085 37983507285634994647764407)
  ·
    refine ⟨56975260928452491971646611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37983507285634994647764407 56975260928452491971646611)
    ·
      refine ⟨85462891392678737957469917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56975260928452491971646611 85462891392678737957469917)
      ·
        refine ⟨32048584272254526734051219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85462891392678737957469917 32048584272254526734051219)
        ·
          refine ⟨48072876408381790101076829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32048584272254526734051219 48072876408381790101076829)
          ·
            refine ⟨18027328653143171287903811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48072876408381790101076829 18027328653143171287903811)
            ·
              refine ⟨27040992979714756931855717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18027328653143171287903811 27040992979714756931855717)
              ·
                refine ⟨5070186183696516924722947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27040992979714756931855717 5070186183696516924722947)
                ·
                  refine ⟨7605279275544775387084421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070186183696516924722947 7605279275544775387084421)
                  ·
                    refine ⟨1425989864164645385078329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7605279275544775387084421 1425989864164645385078329)
                    ·
                      rfl

theorem cell22_4165658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_4165658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165658 prefixEnd_4165658 := by exact prefixLift 4165658
  have htrace : WordTrace (prefixWord ++ tailWord_4165658) baseStart_4165658 baseEnd_4165658 := by
    simpa [prefixWord, tailWord_4165658, baseEnd_4165658] using wordTrace_append hprefix tailTrace_4165658
  have hstable : (prefixWord ++ tailWord_4165658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165658).length < 2 ^ (prefixWord ++ tailWord_4165658).sum := by decide
  have hdescent : baseEnd_4165658 < baseStart_4165658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165726 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4165726 : Nat := 118140960795 + 4165726 * 2 ^ 59
def prefixEnd_4165726 : Nat := 4983230072969 + 3 ^ 40 * 4165726 * 2
def baseEnd_4165726 : Nat := 1426013141954315874378121

theorem tailTrace_4165726 : CollatzResearch.WordTrace tailWord_4165726 prefixEnd_4165726 1426013141954315874378121 := by
  unfold tailWord_4165726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992063663286703275566629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101291006204195750803022021 18992063663286703275566629)
  ·
    refine ⟨3561011936866256864168743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18992063663286703275566629 3561011936866256864168743)
    ·
      refine ⟨5341517905299385296253115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3561011936866256864168743 5341517905299385296253115)
      ·
        refine ⟨8012276857949077944379673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341517905299385296253115 8012276857949077944379673)
        ·
          refine ⟨6009207643461808458284755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8012276857949077944379673 6009207643461808458284755)
          ·
            refine ⟨9013811465192712687427133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009207643461808458284755 9013811465192712687427133)
            ·
              refine ⟨3380179299447267257785175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9013811465192712687427133 3380179299447267257785175)
              ·
                refine ⟨5070268949170900886677763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380179299447267257785175 5070268949170900886677763)
                ·
                  refine ⟨7605403423756351330016645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070268949170900886677763 7605403423756351330016645)
                  ·
                    refine ⟨1426013141954315874378121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7605403423756351330016645 1426013141954315874378121)
                    ·
                      rfl

theorem cell22_4165726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4165726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165726 prefixEnd_4165726 := by exact prefixLift 4165726
  have htrace : WordTrace (prefixWord ++ tailWord_4165726) baseStart_4165726 baseEnd_4165726 := by
    simpa [prefixWord, tailWord_4165726, baseEnd_4165726] using wordTrace_append hprefix tailTrace_4165726
  have hstable : (prefixWord ++ tailWord_4165726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165726).length < 2 ^ (prefixWord ++ tailWord_4165726).sum := by decide
  have hdescent : baseEnd_4165726 < baseStart_4165726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165763 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 5]
def baseStart_4165763 : Nat := 118140960795 + 4165763 * 2 ^ 59
def prefixEnd_4165763 : Nat := 4983230072969 + 3 ^ 40 * 4165763 * 2
def baseEnd_4165763 : Nat := 475341935936820037067669

theorem tailTrace_4165763 : CollatzResearch.WordTrace tailWord_4165763 prefixEnd_4165763 475341935936820037067669 := by
  unfold tailWord_4165763
  simp only [CollatzResearch.WordTrace]
  refine ⟨151937858807159581523629943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101291905871439721015753295 151937858807159581523629943)
  ·
    refine ⟨227906788210739372285444915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151937858807159581523629943 227906788210739372285444915)
    ·
      refine ⟨341860182316109058428167373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227906788210739372285444915 341860182316109058428167373)
      ·
        refine ⟨128197568368540896910562765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341860182316109058428167373 128197568368540896910562765)
        ·
          refine ⟨48074088138202836341461037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128197568368540896910562765 48074088138202836341461037)
          ·
            refine ⟨18027783051826063628047889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48074088138202836341461037 18027783051826063628047889)
            ·
              refine ⟨13520837288869547721035917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18027783051826063628047889 13520837288869547721035917)
              ·
                refine ⟨5070313983326080395388469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13520837288869547721035917 5070313983326080395388469)
                ·
                  refine ⟨475341935936820037067669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5070313983326080395388469 475341935936820037067669)
                  ·
                    rfl

theorem cell22_4165763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 5].length) (baseStart_4165763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165763 prefixEnd_4165763 := by exact prefixLift 4165763
  have htrace : WordTrace (prefixWord ++ tailWord_4165763) baseStart_4165763 baseEnd_4165763 := by
    simpa [prefixWord, tailWord_4165763, baseEnd_4165763] using wordTrace_append hprefix tailTrace_4165763
  have hstable : (prefixWord ++ tailWord_4165763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165763).length < 2 ^ (prefixWord ++ tailWord_4165763).sum := by decide
  have hdescent : baseEnd_4165763 < baseStart_4165763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165778 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4165778 : Nat := 118140960795 + 4165778 * 2 ^ 59
def prefixEnd_4165778 : Nat := 4983230072969 + 3 ^ 40 * 4165778 * 2
def baseEnd_4165778 : Nat := 1426030942617005072077961

theorem tailTrace_4165778 : CollatzResearch.WordTrace tailWord_4165778 prefixEnd_4165778 1426030942617005072077961 := by
  unfold tailWord_4165778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37984601475526309771356497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101292270601403492723617325 37984601475526309771356497)
  ·
    refine ⟨28488451106644732328517373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37984601475526309771356497 28488451106644732328517373)
    ·
      refine ⟨10683169164991774623194015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28488451106644732328517373 10683169164991774623194015)
      ·
        refine ⟨16024753747487661934791023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683169164991774623194015 16024753747487661934791023)
        ·
          refine ⟨24037130621231492902186535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16024753747487661934791023 24037130621231492902186535)
          ·
            refine ⟨36055695931847239353279803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24037130621231492902186535 36055695931847239353279803)
            ·
              refine ⟨54083543897770859029919705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36055695931847239353279803 54083543897770859029919705)
              ·
                refine ⟨40562657923328144272439779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54083543897770859029919705 40562657923328144272439779)
                ·
                  refine ⟨60843986884992216408659669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40562657923328144272439779 60843986884992216408659669)
                  ·
                    refine ⟨1426030942617005072077961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60843986884992216408659669 1426030942617005072077961)
                    ·
                      rfl

theorem cell22_4165778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4165778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165778 prefixEnd_4165778 := by exact prefixLift 4165778
  have htrace : WordTrace (prefixWord ++ tailWord_4165778) baseStart_4165778 baseEnd_4165778 := by
    simpa [prefixWord, tailWord_4165778, baseEnd_4165778] using wordTrace_append hprefix tailTrace_4165778
  have hstable : (prefixWord ++ tailWord_4165778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165778).length < 2 ^ (prefixWord ++ tailWord_4165778).sum := by decide
  have hdescent : baseEnd_4165778 < baseStart_4165778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165784 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 1, 3]
def baseStart_4165784 : Nat := 118140960795 + 4165784 * 2 ^ 59
def prefixEnd_4165784 : Nat := 4983230072969 + 3 ^ 40 * 4165784 * 2
def baseEnd_4165784 : Nat := 1426032996539623056427943

theorem tailTrace_4165784 : CollatzResearch.WordTrace tailWord_4165784 prefixEnd_4165784 1426032996539623056427943 := by
  unfold tailWord_4165784
  simp only [CollatzResearch.WordTrace]
  refine ⟨75969312370041751055072203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101292416493389001406762937 75969312370041751055072203)
  ·
    refine ⟨113953968555062626582608305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75969312370041751055072203 113953968555062626582608305)
    ·
      refine ⟨85465476416296969936956229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113953968555062626582608305 85465476416296969936956229)
      ·
        refine ⟨16024776828055681863179293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85465476416296969936956229 16024776828055681863179293)
        ·
          refine ⟨6009291310520880698692235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16024776828055681863179293 6009291310520880698692235)
          ·
            refine ⟨9013936965781321048038353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009291310520880698692235 9013936965781321048038353)
            ·
              refine ⟨6760452724335990786028765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013936965781321048038353 6760452724335990786028765)
              ·
                refine ⟨2535169771625996544760787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6760452724335990786028765 2535169771625996544760787)
                ·
                  refine ⟨3802754657438994817141181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535169771625996544760787 3802754657438994817141181)
                  ·
                    refine ⟨1426032996539623056427943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802754657438994817141181 1426032996539623056427943)
                    ·
                      rfl

theorem cell22_4165784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_4165784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165784 prefixEnd_4165784 := by exact prefixLift 4165784
  have htrace : WordTrace (prefixWord ++ tailWord_4165784) baseStart_4165784 baseEnd_4165784 := by
    simpa [prefixWord, tailWord_4165784, baseEnd_4165784] using wordTrace_append hprefix tailTrace_4165784
  have hstable : (prefixWord ++ tailWord_4165784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165784).length < 2 ^ (prefixWord ++ tailWord_4165784).sum := by decide
  have hdescent : baseEnd_4165784 < baseStart_4165784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165842 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_4165842 : Nat := 118140960795 + 4165842 * 2 ^ 59
def prefixEnd_4165842 : Nat := 4983230072969 + 3 ^ 40 * 4165842 * 2
def baseEnd_4165842 : Nat := 475350950374976746159255

theorem tailTrace_4165842 : CollatzResearch.WordTrace tailWord_4165842 prefixEnd_4165842 475350950374976746159255 := by
  unfold tailWord_4165842
  simp only [CollatzResearch.WordTrace]
  refine ⟨37985185043468344503938945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101293826782582252010503853 37985185043468344503938945)
  ·
    refine ⟨28488888782601258377954209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37985185043468344503938945 28488888782601258377954209)
    ·
      refine ⟨21366666586950943783465657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28488888782601258377954209 21366666586950943783465657)
      ·
        refine ⟨16024999940213207837599243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21366666586950943783465657 16024999940213207837599243)
        ·
          refine ⟨24037499910319811756398865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16024999940213207837599243 24037499910319811756398865)
          ·
            refine ⟨18028124932739858817299149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24037499910319811756398865 18028124932739858817299149)
            ·
              refine ⟨6760546849777447056487181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18028124932739858817299149 6760546849777447056487181)
              ·
                refine ⟨2535205068666542646182693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6760546849777447056487181 2535205068666542646182693)
                ·
                  refine ⟨475350950374976746159255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535205068666542646182693 475350950374976746159255)
                  ·
                    rfl

theorem cell22_4165842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_4165842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165842 prefixEnd_4165842 := by exact prefixLift 4165842
  have htrace : WordTrace (prefixWord ++ tailWord_4165842) baseStart_4165842 baseEnd_4165842 := by
    simpa [prefixWord, tailWord_4165842, baseEnd_4165842] using wordTrace_append hprefix tailTrace_4165842
  have hstable : (prefixWord ++ tailWord_4165842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165842).length < 2 ^ (prefixWord ++ tailWord_4165842).sum := by decide
  have hdescent : baseEnd_4165842 < baseStart_4165842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165859 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 6]
def baseStart_4165859 : Nat := 118140960795 + 4165859 * 2 ^ 59
def prefixEnd_4165859 : Nat := 4983230072969 + 3 ^ 40 * 4165859 * 2
def baseEnd_4165859 : Nat := 475352890190782620267571

theorem tailTrace_4165859 : CollatzResearch.WordTrace tailWord_4165859 prefixEnd_4165859 475352890190782620267571 := by
  unfold tailWord_4165859
  simp only [CollatzResearch.WordTrace]
  refine ⟨151941360214811789919124631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101294240143207859946083087 151941360214811789919124631)
  ·
    refine ⟨227912040322217684878686947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151941360214811789919124631 227912040322217684878686947)
    ·
      refine ⟨341868060483326527318030421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227912040322217684878686947 341868060483326527318030421)
      ·
        refine ⟨4006266333788982742008169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 341868060483326527318030421 4006266333788982742008169)
        ·
          refine ⟨3004699750341737056506127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4006266333788982742008169 3004699750341737056506127)
          ·
            refine ⟨4507049625512605584759191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004699750341737056506127 4507049625512605584759191)
            ·
              refine ⟨6760574438268908377138787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507049625512605584759191 6760574438268908377138787)
              ·
                refine ⟨10140861657403362565708181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760574438268908377138787 10140861657403362565708181)
                ·
                  refine ⟨475352890190782620267571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10140861657403362565708181 475352890190782620267571)
                  ·
                    rfl

theorem cell22_4165859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 6].length) (baseStart_4165859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165859 prefixEnd_4165859 := by exact prefixLift 4165859
  have htrace : WordTrace (prefixWord ++ tailWord_4165859) baseStart_4165859 baseEnd_4165859 := by
    simpa [prefixWord, tailWord_4165859, baseEnd_4165859] using wordTrace_append hprefix tailTrace_4165859
  have hstable : (prefixWord ++ tailWord_4165859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165859).length < 2 ^ (prefixWord ++ tailWord_4165859).sum := by decide
  have hdescent : baseEnd_4165859 < baseStart_4165859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165874 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_4165874 : Nat := 118140960795 + 4165874 * 2 ^ 59
def prefixEnd_4165874 : Nat := 4983230072969 + 3 ^ 40 * 4165874 * 2
def baseEnd_4165874 : Nat := 1426063805378892821677667

theorem tailTrace_4165874 : CollatzResearch.WordTrace tailWord_4165874 prefixEnd_4165874 1426063805378892821677667 := by
  unfold tailWord_4165874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37985476827439361870230169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101294604873171631653947117 37985476827439361870230169)
  ·
    refine ⟨28489107620579521402672627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37985476827439361870230169 28489107620579521402672627)
    ·
      refine ⟨42733661430869282104008941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28489107620579521402672627 42733661430869282104008941)
      ·
        refine ⟨16025123036575980789003353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42733661430869282104008941 16025123036575980789003353)
        ·
          refine ⟨12018842277431985591752515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16025123036575980789003353 12018842277431985591752515)
          ·
            refine ⟨18028263416147978387628773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018842277431985591752515 18028263416147978387628773)
            ·
              refine ⟨3380299390527745947680395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18028263416147978387628773 3380299390527745947680395)
              ·
                refine ⟨5070449085791618921520593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380299390527745947680395 5070449085791618921520593)
                ·
                  refine ⟨3802836814343714191140445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070449085791618921520593 3802836814343714191140445)
                  ·
                    refine ⟨1426063805378892821677667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802836814343714191140445 1426063805378892821677667)
                    ·
                      rfl

theorem cell22_4165874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_4165874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165874 prefixEnd_4165874 := by exact prefixLift 4165874
  have htrace : WordTrace (prefixWord ++ tailWord_4165874) baseStart_4165874 baseEnd_4165874 := by
    simpa [prefixWord, tailWord_4165874, baseEnd_4165874] using wordTrace_append hprefix tailTrace_4165874
  have hstable : (prefixWord ++ tailWord_4165874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165874).length < 2 ^ (prefixWord ++ tailWord_4165874).sum := by decide
  have hdescent : baseEnd_4165874 < baseStart_4165874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165885 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_4165885 : Nat := 118140960795 + 4165885 * 2 ^ 59
def prefixEnd_4165885 : Nat := 4983230072969 + 3 ^ 40 * 4165885 * 2
def baseEnd_4165885 : Nat := 1426067570903692459652633

theorem tailTrace_4165885 : CollatzResearch.WordTrace tailWord_4165885 prefixEnd_4165885 1426067570903692459652633 := by
  unfold tailWord_4165885
  simp only [CollatzResearch.WordTrace]
  refine ⟨151942308512717596359571109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101294872341811730906380739 151942308512717596359571109)
  ·
    refine ⟨28489182846134549317419583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151942308512717596359571109 28489182846134549317419583)
    ·
      refine ⟨42733774269201823976129375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28489182846134549317419583 42733774269201823976129375)
      ·
        refine ⟨64100661403802735964194063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42733774269201823976129375 64100661403802735964194063)
        ·
          refine ⟨96150992105704103946291095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64100661403802735964194063 96150992105704103946291095)
          ·
            refine ⟨144226488158556155919436643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96150992105704103946291095 144226488158556155919436643)
            ·
              refine ⟨216339732237834233879154965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144226488158556155919436643 216339732237834233879154965)
              ·
                refine ⟨10140924948648479713085389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 216339732237834233879154965 10140924948648479713085389)
                ·
                  refine ⟨3802846855743179892407021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10140924948648479713085389 3802846855743179892407021)
                  ·
                    refine ⟨1426067570903692459652633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802846855743179892407021 1426067570903692459652633)
                    ·
                      rfl

theorem cell22_4165885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_4165885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165885 prefixEnd_4165885 := by exact prefixLift 4165885
  have htrace : WordTrace (prefixWord ++ tailWord_4165885) baseStart_4165885 baseEnd_4165885 := by
    simpa [prefixWord, tailWord_4165885, baseEnd_4165885] using wordTrace_append hprefix tailTrace_4165885
  have hstable : (prefixWord ++ tailWord_4165885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165885).length < 2 ^ (prefixWord ++ tailWord_4165885).sum := by decide
  have hdescent : baseEnd_4165885 < baseStart_4165885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165898 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_4165898 : Nat := 118140960795 + 4165898 * 2 ^ 59
def prefixEnd_4165898 : Nat := 4983230072969 + 3 ^ 40 * 4165898 * 2
def baseEnd_4165898 : Nat := 475357340356454919692531

theorem tailTrace_4165898 : CollatzResearch.WordTrace tailWord_4165898 prefixEnd_4165898 475357340356454919692531 := by
  unfold tailWord_4165898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37985695665417624894948587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101295188441113666386529565 37985695665417624894948587)
  ·
    refine ⟨56978543498126437342422881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37985695665417624894948587 56978543498126437342422881)
    ·
      refine ⟨42733907623594828006817161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56978543498126437342422881 42733907623594828006817161)
      ·
        refine ⟨32050430717696121005112871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42733907623594828006817161 32050430717696121005112871)
        ·
          refine ⟨48075646076544181507669307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32050430717696121005112871 48075646076544181507669307)
          ·
            refine ⟨72113469114816272261503961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48075646076544181507669307 72113469114816272261503961)
            ·
              refine ⟨54085101836112204196127971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72113469114816272261503961 54085101836112204196127971)
              ·
                refine ⟨81127652754168306294191957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54085101836112204196127971 81127652754168306294191957)
                ·
                  refine ⟨475357340356454919692531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81127652754168306294191957 475357340356454919692531)
                  ·
                    rfl

theorem cell22_4165898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_4165898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165898 prefixEnd_4165898 := by exact prefixLift 4165898
  have htrace : WordTrace (prefixWord ++ tailWord_4165898) baseStart_4165898 baseEnd_4165898 := by
    simpa [prefixWord, tailWord_4165898, baseEnd_4165898] using wordTrace_append hprefix tailTrace_4165898
  have hstable : (prefixWord ++ tailWord_4165898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165898).length < 2 ^ (prefixWord ++ tailWord_4165898).sum := by decide
  have hdescent : baseEnd_4165898 < baseStart_4165898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165919 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 1, 3]
def baseStart_4165919 : Nat := 118140960795 + 4165919 * 2 ^ 59
def prefixEnd_4165919 : Nat := 4983230072969 + 3 ^ 40 * 4165919 * 2
def baseEnd_4165919 : Nat := 1426079209798527704302529

theorem tailTrace_4165919 : CollatzResearch.WordTrace tailWord_4165919 prefixEnd_4165919 1426079209798527704302529 := by
  unfold tailWord_4165919
  simp only [CollatzResearch.WordTrace]
  refine ⟨151943548594594420166308811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101295699063062946777539207 151943548594594420166308811)
  ·
    refine ⟨227915322891891630249463217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151943548594594420166308811 227915322891891630249463217)
    ·
      refine ⟨170936492168918722687097413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227915322891891630249463217 170936492168918722687097413)
      ·
        refine ⟨32050592281672260503830765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170936492168918722687097413 32050592281672260503830765)
        ·
          refine ⟨12018972105627097688936537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32050592281672260503830765 12018972105627097688936537)
          ·
            refine ⟨9014229079220323266702403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12018972105627097688936537 9014229079220323266702403)
            ·
              refine ⟨13521343618830484900053605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014229079220323266702403 13521343618830484900053605)
              ·
                refine ⟨2535251928530715918760051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13521343618830484900053605 2535251928530715918760051)
                ·
                  refine ⟨3802877892796073878140077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535251928530715918760051 3802877892796073878140077)
                  ·
                    refine ⟨1426079209798527704302529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3802877892796073878140077 1426079209798527704302529)
                    ·
                      rfl

theorem cell22_4165919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_4165919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165919 prefixEnd_4165919 := by exact prefixLift 4165919
  have htrace : WordTrace (prefixWord ++ tailWord_4165919) baseStart_4165919 baseEnd_4165919 := by
    simpa [prefixWord, tailWord_4165919, baseEnd_4165919] using wordTrace_append hprefix tailTrace_4165919
  have hstable : (prefixWord ++ tailWord_4165919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165919).length < 2 ^ (prefixWord ++ tailWord_4165919).sum := by decide
  have hdescent : baseEnd_4165919 < baseStart_4165919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165992 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_4165992 : Nat := 118140960795 + 4165992 * 2 ^ 59
def prefixEnd_4165992 : Nat := 4983230072969 + 3 ^ 40 * 4165992 * 2
def baseEnd_4165992 : Nat := 1426104199190379847227305

theorem tailTrace_4165992 : CollatzResearch.WordTrace tailWord_4165992 prefixEnd_4165992 1426104199190379847227305 := by
  unfold tailWord_4165992
  simp only [CollatzResearch.WordTrace]
  refine ⟨75973105561664976816858115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101297474082219969089144153 75973105561664976816858115)
  ·
    refine ⟨113959658342497465225287173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75973105561664976816858115 113959658342497465225287173)
    ·
      refine ⟨21367435939218274729741345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113959658342497465225287173 21367435939218274729741345)
      ·
        refine ⟨16025576954413706047306009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21367435939218274729741345 16025576954413706047306009)
        ·
          refine ⟨12019182715810279535479507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16025576954413706047306009 12019182715810279535479507)
          ·
            refine ⟨18028774073715419303219261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12019182715810279535479507 18028774073715419303219261)
            ·
              refine ⟨6760790277643282238707223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18028774073715419303219261 6760790277643282238707223)
              ·
                refine ⟨10141185416464923358060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760790277643282238707223 10141185416464923358060835)
                ·
                  refine ⟨15211778124697385037091253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141185416464923358060835 15211778124697385037091253)
                  ·
                    refine ⟨1426104199190379847227305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15211778124697385037091253 1426104199190379847227305)
                    ·
                      rfl

theorem cell22_4165992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_4165992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4165992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4165992 prefixEnd_4165992 := by exact prefixLift 4165992
  have htrace : WordTrace (prefixWord ++ tailWord_4165992) baseStart_4165992 baseEnd_4165992 := by
    simpa [prefixWord, tailWord_4165992, baseEnd_4165992] using wordTrace_append hprefix tailTrace_4165992
  have hstable : (prefixWord ++ tailWord_4165992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165992).length < 2 ^ (prefixWord ++ tailWord_4165992).sum := by decide
  have hdescent : baseEnd_4165992 < baseStart_4165992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166058 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4166058 : Nat := 118140960795 + 4166058 * 2 ^ 59
def prefixEnd_4166058 : Nat := 4983230072969 + 3 ^ 40 * 4166058 * 2
def baseEnd_4166058 : Nat := 1426126792339177675077103

theorem tailTrace_4166058 : CollatzResearch.WordTrace tailWord_4166058 prefixEnd_4166058 1426126792339177675077103 := by
  unfold tailWord_4166058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37987154585272711726404707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101299078894060564603745885 37987154585272711726404707)
  ·
    refine ⟨56980731877909067589607061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37987154585272711726404707 56980731877909067589607061)
    ·
      refine ⟨2670971806776987543262831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56980731877909067589607061 2670971806776987543262831)
      ·
        refine ⟨4006457710165481314894247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670971806776987543262831 4006457710165481314894247)
        ·
          refine ⟨6009686565248221972341371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006457710165481314894247 6009686565248221972341371)
          ·
            refine ⟨9014529847872332958512057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009686565248221972341371 9014529847872332958512057)
            ·
              refine ⟨6760897385904249718884043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014529847872332958512057 6760897385904249718884043)
              ·
                refine ⟨10141346078856374578326065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760897385904249718884043 10141346078856374578326065)
                ·
                  refine ⟨7606009559142280933744549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141346078856374578326065 7606009559142280933744549)
                  ·
                    refine ⟨1426126792339177675077103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606009559142280933744549 1426126792339177675077103)
                    ·
                      rfl

theorem cell22_4166058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4166058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166058 prefixEnd_4166058 := by exact prefixLift 4166058
  have htrace : WordTrace (prefixWord ++ tailWord_4166058) baseStart_4166058 baseEnd_4166058 := by
    simpa [prefixWord, tailWord_4166058, baseEnd_4166058] using wordTrace_append hprefix tailTrace_4166058
  have hstable : (prefixWord ++ tailWord_4166058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166058).length < 2 ^ (prefixWord ++ tailWord_4166058).sum := by decide
  have hdescent : baseEnd_4166058 < baseStart_4166058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166088 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 1, 3]
def baseStart_4166088 : Nat := 118140960795 + 4166088 * 2 ^ 59
def prefixEnd_4166088 : Nat := 4983230072969 + 3 ^ 40 * 4166088 * 2
def baseEnd_4166088 : Nat := 1426137061952267596827011

theorem tailTrace_4166088 : CollatzResearch.WordTrace tailWord_4166088 prefixEnd_4166088 1426137061952267596827011 := by
  unfold tailWord_4166088
  simp only [CollatzResearch.WordTrace]
  refine ⟨75974856265491081014605459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101299808353988108019473945 75974856265491081014605459)
  ·
    refine ⟨113962284398236621521908189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75974856265491081014605459 113962284398236621521908189)
    ·
      refine ⟨42735856649338733070715571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113962284398236621521908189 42735856649338733070715571)
      ·
        refine ⟨64103784974008099606073357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42735856649338733070715571 64103784974008099606073357)
        ·
          refine ⟨24038919365253037352277509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64103784974008099606073357 24038919365253037352277509)
          ·
            refine ⟨4507297380984944503552033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24038919365253037352277509 4507297380984944503552033)
            ·
              refine ⟨3380473035738708377664025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507297380984944503552033 3380473035738708377664025)
              ·
                refine ⟨2535354776804031283248019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380473035738708377664025 2535354776804031283248019)
                ·
                  refine ⟨3803032165206046924872029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535354776804031283248019 3803032165206046924872029)
                  ·
                    refine ⟨1426137061952267596827011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803032165206046924872029 1426137061952267596827011)
                    ·
                      rfl

theorem cell22_4166088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_4166088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166088 prefixEnd_4166088 := by exact prefixLift 4166088
  have htrace : WordTrace (prefixWord ++ tailWord_4166088) baseStart_4166088 baseEnd_4166088 := by
    simpa [prefixWord, tailWord_4166088, baseEnd_4166088] using wordTrace_append hprefix tailTrace_4166088
  have hstable : (prefixWord ++ tailWord_4166088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166088).length < 2 ^ (prefixWord ++ tailWord_4166088).sum := by decide
  have hdescent : baseEnd_4166088 < baseStart_4166088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166095 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 6]
def baseStart_4166095 : Nat := 118140960795 + 4166095 * 2 ^ 59
def prefixEnd_4166095 : Nat := 4983230072969 + 3 ^ 40 * 4166095 * 2
def baseEnd_4166095 : Nat := 475379819398440637300663

theorem tailTrace_4166095 : CollatzResearch.WordTrace tailWord_4166095 prefixEnd_4166095 475379819398440637300663 := by
  unfold tailWord_4166095
  simp only [CollatzResearch.WordTrace]
  refine ⟨151949967841956802224715739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101299978561304534816477159 151949967841956802224715739)
  ·
    refine ⟨227924951762935203337073609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151949967841956802224715739 227924951762935203337073609)
    ·
      refine ⟨170943713822201402502805207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227924951762935203337073609 170943713822201402502805207)
      ·
        refine ⟨256415570733302103754207811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170943713822201402502805207 256415570733302103754207811)
        ·
          refine ⟨384623356099953155631311717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256415570733302103754207811 384623356099953155631311717)
          ·
            refine ⟨72116879268741216680870947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384623356099953155631311717 72116879268741216680870947)
            ·
              refine ⟨108175318903111825021306421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72116879268741216680870947 108175318903111825021306421)
              ·
                refine ⟨10141436147166733595747477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108175318903111825021306421 10141436147166733595747477)
                ·
                  refine ⟨475379819398440637300663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10141436147166733595747477 475379819398440637300663)
                  ·
                    rfl

theorem cell22_4166095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 6].length) (baseStart_4166095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166095 prefixEnd_4166095 := by exact prefixLift 4166095
  have htrace : WordTrace (prefixWord ++ tailWord_4166095) baseStart_4166095 baseEnd_4166095 := by
    simpa [prefixWord, tailWord_4166095, baseEnd_4166095] using wordTrace_append hprefix tailTrace_4166095
  have hstable : (prefixWord ++ tailWord_4166095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166095).length < 2 ^ (prefixWord ++ tailWord_4166095).sum := by decide
  have hdescent : baseEnd_4166095 < baseStart_4166095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166127 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 4, 3]
def baseStart_4166127 : Nat := 118140960795 + 4166127 * 2 ^ 59
def prefixEnd_4166127 : Nat := 4983230072969 + 3 ^ 40 * 4166127 * 2
def baseEnd_4166127 : Nat := 1426150412449284495101891

theorem tailTrace_4166127 : CollatzResearch.WordTrace tailWord_4166127 prefixEnd_4166127 1426150412449284495101891 := by
  unfold tailWord_4166127
  simp only [CollatzResearch.WordTrace]
  refine ⟨151951134977840871689880635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101300756651893914459920423 151951134977840871689880635)
  ·
    refine ⟨227926702466761307534820953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151951134977840871689880635 227926702466761307534820953)
    ·
      refine ⟨170945026850070980651115715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227926702466761307534820953 170945026850070980651115715)
      ·
        refine ⟨256417540275106470976673573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170945026850070980651115715 256417540275106470976673573)
        ·
          refine ⟨48078288801582463308126295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256417540275106470976673573 48078288801582463308126295)
          ·
            refine ⟨72117433202373694962189443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48078288801582463308126295 72117433202373694962189443)
            ·
              refine ⟨108176149803560542443284165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72117433202373694962189443 108176149803560542443284165)
              ·
                refine ⟨20283028088167601708115781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108176149803560542443284165 20283028088167601708115781)
                ·
                  refine ⟨3803067766531425320271709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20283028088167601708115781 3803067766531425320271709)
                  ·
                    refine ⟨1426150412449284495101891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803067766531425320271709 1426150412449284495101891)
                    ·
                      rfl

theorem cell22_4166127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_4166127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166127 prefixEnd_4166127 := by exact prefixLift 4166127
  have htrace : WordTrace (prefixWord ++ tailWord_4166127) baseStart_4166127 baseEnd_4166127 := by
    simpa [prefixWord, tailWord_4166127, baseEnd_4166127] using wordTrace_append hprefix tailTrace_4166127
  have hstable : (prefixWord ++ tailWord_4166127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166127).length < 2 ^ (prefixWord ++ tailWord_4166127).sum := by decide
  have hdescent : baseEnd_4166127 < baseStart_4166127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166129 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 4]
def baseStart_4166129 : Nat := 118140960795 + 4166129 * 2 ^ 59
def prefixEnd_4166129 : Nat := 4983230072969 + 3 ^ 40 * 4166129 * 2
def baseEnd_4166129 : Nat := 475383699030052385517295

theorem tailTrace_4166129 : CollatzResearch.WordTrace tailWord_4166129 prefixEnd_4166129 475383699030052385517295 := by
  unfold tailWord_4166129
  simp only [CollatzResearch.WordTrace]
  refine ⟨151951207923833626031453441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101300805282555750687635627 151951207923833626031453441)
  ·
    refine ⟨113963405942875219523590081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151951207923833626031453441 113963405942875219523590081)
    ·
      refine ⟨85472554457156414642692561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113963405942875219523590081 85472554457156414642692561)
      ·
        refine ⟨64104415842867310982019421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85472554457156414642692561 64104415842867310982019421)
        ·
          refine ⟨24039155941075241618257283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64104415842867310982019421 24039155941075241618257283)
          ·
            refine ⟨36058733911612862427385925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24039155941075241618257283 36058733911612862427385925)
            ·
              refine ⟨6761012608427411705134861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36058733911612862427385925 6761012608427411705134861)
              ·
                refine ⟨2535379728160279389425573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6761012608427411705134861 2535379728160279389425573)
                ·
                  refine ⟨475383699030052385517295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535379728160279389425573 475383699030052385517295)
                  ·
                    rfl

theorem cell22_4166129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_4166129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166129 prefixEnd_4166129 := by exact prefixLift 4166129
  have htrace : WordTrace (prefixWord ++ tailWord_4166129) baseStart_4166129 baseEnd_4166129 := by
    simpa [prefixWord, tailWord_4166129, baseEnd_4166129] using wordTrace_append hprefix tailTrace_4166129
  have hstable : (prefixWord ++ tailWord_4166129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166129).length < 2 ^ (prefixWord ++ tailWord_4166129).sum := by decide
  have hdescent : baseEnd_4166129 < baseStart_4166129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166146 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4166146 : Nat := 118140960795 + 4166146 * 2 ^ 59
def prefixEnd_4166146 : Nat := 4983230072969 + 3 ^ 40 * 4166146 * 2
def baseEnd_4166146 : Nat := 475385638845858259625611

theorem tailTrace_4166146 : CollatzResearch.WordTrace tailWord_4166146 prefixEnd_4166146 475385638845858259625611 := by
  unfold tailWord_4166146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37987956991193009483705573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101301218643181358623214861 37987956991193009483705573)
  ·
    refine ⟨7122741935848689278194795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37987956991193009483705573 7122741935848689278194795)
    ·
      refine ⟨10684112903773033917292193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122741935848689278194795 10684112903773033917292193)
      ·
        refine ⟨8013084677829775437969145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10684112903773033917292193 8013084677829775437969145)
        ·
          refine ⟨6009813508372331578476859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8013084677829775437969145 6009813508372331578476859)
          ·
            refine ⟨9014720262558497367715289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009813508372331578476859 9014720262558497367715289)
            ·
              refine ⟨6761040196918873025786467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014720262558497367715289 6761040196918873025786467)
              ·
                refine ⟨10141560295378309538679701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761040196918873025786467 10141560295378309538679701)
                ·
                  refine ⟨475385638845858259625611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10141560295378309538679701 475385638845858259625611)
                  ·
                    rfl

theorem cell22_4166146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4166146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166146 prefixEnd_4166146 := by exact prefixLift 4166146
  have htrace : WordTrace (prefixWord ++ tailWord_4166146) baseStart_4166146 baseEnd_4166146 := by
    simpa [prefixWord, tailWord_4166146, baseEnd_4166146] using wordTrace_append hprefix tailTrace_4166146
  have hstable : (prefixWord ++ tailWord_4166146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166146).length < 2 ^ (prefixWord ++ tailWord_4166146).sum := by decide
  have hdescent : baseEnd_4166146 < baseStart_4166146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166180 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 4]
def baseStart_4166180 : Nat := 118140960795 + 4166180 * 2 ^ 59
def prefixEnd_4166180 : Nat := 4983230072969 + 3 ^ 40 * 4166180 * 2
def baseEnd_4166180 : Nat := 475389518477470007842243

theorem tailTrace_4166180 : CollatzResearch.WordTrace tailWord_4166180 prefixEnd_4166180 475389518477470007842243 := by
  unfold tailWord_4166180
  simp only [CollatzResearch.WordTrace]
  refine ⟨75976534023324430870779997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101302045364432574494373329 75976534023324430870779997)
  ·
    refine ⟨28491200258746661576542499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75976534023324430870779997 28491200258746661576542499)
    ·
      refine ⟨42736800388119992364813749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28491200258746661576542499 42736800388119992364813749)
      ·
        refine ⟨4006575036386249284201289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42736800388119992364813749 4006575036386249284201289)
        ·
          refine ⟨3004931277289686963150967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4006575036386249284201289 3004931277289686963150967)
          ·
            refine ⟨4507396915934530444726451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004931277289686963150967 4507396915934530444726451)
            ·
              refine ⟨6761095373901795667089677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507396915934530444726451 6761095373901795667089677)
              ·
                refine ⟨2535410765213173375158629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6761095373901795667089677 2535410765213173375158629)
                ·
                  refine ⟨475389518477470007842243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535410765213173375158629 475389518477470007842243)
                  ·
                    rfl

theorem cell22_4166180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_4166180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166180 prefixEnd_4166180 := by exact prefixLift 4166180
  have htrace : WordTrace (prefixWord ++ tailWord_4166180) baseStart_4166180 baseEnd_4166180 := by
    simpa [prefixWord, tailWord_4166180, baseEnd_4166180] using wordTrace_append hprefix tailTrace_4166180
  have hstable : (prefixWord ++ tailWord_4166180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166180).length < 2 ^ (prefixWord ++ tailWord_4166180).sum := by decide
  have hdescent : baseEnd_4166180 < baseStart_4166180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166202 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_4166202 : Nat := 118140960795 + 4166202 * 2 ^ 59
def prefixEnd_4166202 : Nat := 4983230072969 + 3 ^ 40 * 4166202 * 2
def baseEnd_4166202 : Nat := 475392028827336433158887

theorem tailTrace_4166202 : CollatzResearch.WordTrace tailWord_4166202 prefixEnd_4166202 475392028827336433158887 := by
  unfold tailWord_4166202
  simp only [CollatzResearch.WordTrace]
  refine ⟨37988467613142289874715215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101302580301712772999240573 37988467613142289874715215)
  ·
    refine ⟨56982701419713434812072823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37988467613142289874715215 56982701419713434812072823)
    ·
      refine ⟨85474052129570152218109235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56982701419713434812072823 85474052129570152218109235)
      ·
        refine ⟨128211078194355228327163853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85474052129570152218109235 128211078194355228327163853)
        ·
          refine ⟨48079154322883210622686445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128211078194355228327163853 48079154322883210622686445)
          ·
            refine ⟨18029682871081203983507417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48079154322883210622686445 18029682871081203983507417)
            ·
              refine ⟨13522262153310902987630563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18029682871081203983507417 13522262153310902987630563)
              ·
                refine ⟨20283393229966354481445845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13522262153310902987630563 20283393229966354481445845)
                ·
                  refine ⟨475392028827336433158887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20283393229966354481445845 475392028827336433158887)
                  ·
                    rfl

theorem cell22_4166202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_4166202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166202 prefixEnd_4166202 := by exact prefixLift 4166202
  have htrace : WordTrace (prefixWord ++ tailWord_4166202) baseStart_4166202 baseEnd_4166202 := by
    simpa [prefixWord, tailWord_4166202, baseEnd_4166202] using wordTrace_append hprefix tailTrace_4166202
  have hstable : (prefixWord ++ tailWord_4166202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166202).length < 2 ^ (prefixWord ++ tailWord_4166202).sum := by decide
  have hdescent : baseEnd_4166202 < baseStart_4166202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166219 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 5]
def baseStart_4166219 : Nat := 118140960795 + 4166219 * 2 ^ 59
def prefixEnd_4166219 : Nat := 4983230072969 + 3 ^ 40 * 4166219 * 2
def baseEnd_4166219 : Nat := 475393968643142307267203

theorem tailTrace_4166219 : CollatzResearch.WordTrace tailWord_4166219 prefixEnd_4166219 475393968643142307267203 := by
  unfold tailWord_4166219
  simp only [CollatzResearch.WordTrace]
  refine ⟨151954490493507571402229711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101302993662338380934819807 151954490493507571402229711)
  ·
    refine ⟨227931735740261357103344567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151954490493507571402229711 227931735740261357103344567)
    ·
      refine ⟨341897603610392035655016851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227931735740261357103344567 341897603610392035655016851)
      ·
        refine ⟨512846405415588053482525277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341897603610392035655016851 512846405415588053482525277)
        ·
          refine ⟨192317402030845520055946979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512846405415588053482525277 192317402030845520055946979)
          ·
            refine ⟨288476103046268280083920469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192317402030845520055946979 288476103046268280083920469)
            ·
              refine ⟨3380579332573456407233443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 288476103046268280083920469 3380579332573456407233443)
              ·
                refine ⟨5070868998860184610850165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380579332573456407233443 5070868998860184610850165)
                ·
                  refine ⟨475393968643142307267203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5070868998860184610850165 475393968643142307267203)
                  ·
                    rfl

theorem cell22_4166219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 5].length) (baseStart_4166219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166219 prefixEnd_4166219 := by exact prefixLift 4166219
  have htrace : WordTrace (prefixWord ++ tailWord_4166219) baseStart_4166219 baseEnd_4166219 := by
    simpa [prefixWord, tailWord_4166219, baseEnd_4166219] using wordTrace_append hprefix tailTrace_4166219
  have hstable : (prefixWord ++ tailWord_4166219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166219).length < 2 ^ (prefixWord ++ tailWord_4166219).sum := by decide
  have hdescent : baseEnd_4166219 < baseStart_4166219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166264 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 4]
def baseStart_4166264 : Nat := 118140960795 + 4166264 * 2 ^ 59
def prefixEnd_4166264 : Nat := 4983230072969 + 3 ^ 40 * 4166264 * 2
def baseEnd_4166264 : Nat := 475399103449687268142157

theorem tailTrace_4166264 : CollatzResearch.WordTrace tailWord_4166264 prefixEnd_4166264 475399103449687268142157 := by
  unfold tailWord_4166264
  simp only [CollatzResearch.WordTrace]
  refine ⟨75978065889172272043808923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101304087852229696058411897 75978065889172272043808923)
  ·
    refine ⟨113967098833758408065713385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75978065889172272043808923 113967098833758408065713385)
    ·
      refine ⟨85475324125318806049285039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113967098833758408065713385 85475324125318806049285039)
      ·
        refine ⟨128212986187978209073927559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85475324125318806049285039 128212986187978209073927559)
        ·
          refine ⟨192319479281967313610891339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128212986187978209073927559 192319479281967313610891339)
          ·
            refine ⟨288479218922950970416337009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192319479281967313610891339 288479218922950970416337009)
            ·
              refine ⟨216359414192213227812252757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288479218922950970416337009 216359414192213227812252757)
              ·
                refine ⟨2535461885064998763424837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 216359414192213227812252757 2535461885064998763424837)
                ·
                  refine ⟨475399103449687268142157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535461885064998763424837 475399103449687268142157)
                  ·
                    rfl

theorem cell22_4166264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_4166264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166264 prefixEnd_4166264 := by exact prefixLift 4166264
  have htrace : WordTrace (prefixWord ++ tailWord_4166264) baseStart_4166264 baseEnd_4166264 := by
    simpa [prefixWord, tailWord_4166264, baseEnd_4166264] using wordTrace_append hprefix tailTrace_4166264
  have hstable : (prefixWord ++ tailWord_4166264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166264).length < 2 ^ (prefixWord ++ tailWord_4166264).sum := by decide
  have hdescent : baseEnd_4166264 < baseStart_4166264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166279 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 1, 5]
def baseStart_4166279 : Nat := 118140960795 + 4166279 * 2 ^ 59
def prefixEnd_4166279 : Nat := 4983230072969 + 3 ^ 40 * 4166279 * 2
def baseEnd_4166279 : Nat := 1426202445155606765301425

theorem tailTrace_4166279 : CollatzResearch.WordTrace tailWord_4166279 prefixEnd_4166279 1426202445155606765301425 := by
  unfold tailWord_4166279
  simp only [CollatzResearch.WordTrace]
  refine ⟨151956678873290201649413891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101304452582193467766275927 151956678873290201649413891)
  ·
    refine ⟨227935018309935302474120837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151956678873290201649413891 227935018309935302474120837)
    ·
      refine ⟨42737815933112869213897657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227935018309935302474120837 42737815933112869213897657)
      ·
        refine ⟨32053361949834651910423243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42737815933112869213897657 32053361949834651910423243)
        ·
          refine ⟨48080042924751977865634865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32053361949834651910423243 48080042924751977865634865)
          ·
            refine ⟨36060032193563983399226149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48080042924751977865634865 36060032193563983399226149)
            ·
              refine ⟨6761256036293246887354903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36060032193563983399226149 6761256036293246887354903)
              ·
                refine ⟨10141884054439870331032355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761256036293246887354903 10141884054439870331032355)
                ·
                  refine ⟨15212826081659805496548533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141884054439870331032355 15212826081659805496548533)
                  ·
                    refine ⟨1426202445155606765301425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15212826081659805496548533 1426202445155606765301425)
                    ·
                      rfl

theorem cell22_4166279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_4166279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166279 prefixEnd_4166279 := by exact prefixLift 4166279
  have htrace : WordTrace (prefixWord ++ tailWord_4166279) baseStart_4166279 baseEnd_4166279 := by
    simpa [prefixWord, tailWord_4166279, baseEnd_4166279] using wordTrace_append hprefix tailTrace_4166279
  have hstable : (prefixWord ++ tailWord_4166279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166279).length < 2 ^ (prefixWord ++ tailWord_4166279).sum := by decide
  have hdescent : baseEnd_4166279 < baseStart_4166279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166384 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_4166384 : Nat := 118140960795 + 4166384 * 2 ^ 59
def prefixEnd_4166384 : Nat := 4983230072969 + 3 ^ 40 * 4166384 * 2
def baseEnd_4166384 : Nat := 1426238388801421491426103

theorem tailTrace_4166384 : CollatzResearch.WordTrace tailWord_4166384 prefixEnd_4166384 1426238388801421491426103 := by
  unfold tailWord_4166384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75980254268954902290993103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101307005691939869721324137 75980254268954902290993103)
  ·
    refine ⟨113970381403432353436489655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75980254268954902290993103 113970381403432353436489655)
    ·
      refine ⟨170955572105148530154734483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113970381403432353436489655 170955572105148530154734483)
      ·
        refine ⟨256433358157722795232101725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170955572105148530154734483 256433358157722795232101725)
        ·
          refine ⟨96162509309146048212038147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256433358157722795232101725 96162509309146048212038147)
          ·
            refine ⟨144243763963719072318057221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96162509309146048212038147 144243763963719072318057221)
            ·
              refine ⟨27045705743197326059635729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144243763963719072318057221 27045705743197326059635729)
              ·
                refine ⟨20284279307397994544726797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27045705743197326059635729 20284279307397994544726797)
                ·
                  refine ⟨7606604740274247954272549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20284279307397994544726797 7606604740274247954272549)
                  ·
                    refine ⟨1426238388801421491426103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606604740274247954272549 1426238388801421491426103)
                    ·
                      rfl

theorem cell22_4166384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_4166384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166384 prefixEnd_4166384 := by exact prefixLift 4166384
  have htrace : WordTrace (prefixWord ++ tailWord_4166384) baseStart_4166384 baseEnd_4166384 := by
    simpa [prefixWord, tailWord_4166384, baseEnd_4166384] using wordTrace_append hprefix tailTrace_4166384
  have hstable : (prefixWord ++ tailWord_4166384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166384).length < 2 ^ (prefixWord ++ tailWord_4166384).sum := by decide
  have hdescent : baseEnd_4166384 < baseStart_4166384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166463 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 2, 4]
def baseStart_4166463 : Nat := 118140960795 + 4166463 * 2 ^ 59
def prefixEnd_4166463 : Nat := 4983230072969 + 3 ^ 40 * 4166463 * 2
def baseEnd_4166463 : Nat := 1426265432115891618700861

theorem tailTrace_4166463 : CollatzResearch.WordTrace tailWord_4166463 prefixEnd_4166463 1426265432115891618700861 := by
  unfold tailWord_4166463
  simp only [CollatzResearch.WordTrace]
  refine ⟨151963389904623601074112043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101308926603082400716074695 151963389904623601074112043)
  ·
    refine ⟨227945084856935401611168065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151963389904623601074112043 227945084856935401611168065)
    ·
      refine ⟨170958813642701551208376049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227945084856935401611168065 170958813642701551208376049)
      ·
        refine ⟨128219110232026163406282037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170958813642701551208376049 128219110232026163406282037)
        ·
          refine ⟨12020541584252452819338941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128219110232026163406282037 12020541584252452819338941)
          ·
            refine ⟨4507703094094669807252103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12020541584252452819338941 4507703094094669807252103)
            ·
              refine ⟨6761554641142004710878155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507703094094669807252103 6761554641142004710878155)
              ·
                refine ⟨10142331961713007066317233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761554641142004710878155 10142331961713007066317233)
                ·
                  refine ⟨7606748971284755299737925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142331961713007066317233 7606748971284755299737925)
                  ·
                    refine ⟨1426265432115891618700861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606748971284755299737925 1426265432115891618700861)
                    ·
                      rfl

theorem cell22_4166463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_4166463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166463 prefixEnd_4166463 := by exact prefixLift 4166463
  have htrace : WordTrace (prefixWord ++ tailWord_4166463) baseStart_4166463 baseEnd_4166463 := by
    simpa [prefixWord, tailWord_4166463, baseEnd_4166463] using wordTrace_append hprefix tailTrace_4166463
  have hstable : (prefixWord ++ tailWord_4166463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166463).length < 2 ^ (prefixWord ++ tailWord_4166463).sum := by decide
  have hdescent : baseEnd_4166463 < baseStart_4166463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166474 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_4166474 : Nat := 118140960795 + 4166474 * 2 ^ 59
def prefixEnd_4166474 : Nat := 4983230072969 + 3 ^ 40 * 4166474 * 2
def baseEnd_4166474 : Nat := 1426269197640691256675827

theorem tailTrace_4166474 : CollatzResearch.WordTrace tailWord_4166474 prefixEnd_4166474 1426269197640691256675827 := by
  unfold tailWord_4166474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37990947776895937488190619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101309194071722499968508317 37990947776895937488190619)
  ·
    refine ⟨56986421665343906232285929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37990947776895937488190619 56986421665343906232285929)
    ·
      refine ⟨42739816249007929674214447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56986421665343906232285929 42739816249007929674214447)
      ·
        refine ⟨64109724373511894511321671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42739816249007929674214447 64109724373511894511321671)
        ·
          refine ⟨96164586560267841766982507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64109724373511894511321671 96164586560267841766982507)
          ·
            refine ⟨144246879840401762650473761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96164586560267841766982507 144246879840401762650473761)
            ·
              refine ⟨108185159880301321987855321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144246879840401762650473761 108185159880301321987855321)
              ·
                refine ⟨81138869910225991490891491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108185159880301321987855321 81138869910225991490891491)
                ·
                  refine ⟨121708304865338987236337237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81138869910225991490891491 121708304865338987236337237)
                  ·
                    refine ⟨1426269197640691256675827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121708304865338987236337237 1426269197640691256675827)
                    ·
                      rfl

theorem cell22_4166474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_4166474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166474 prefixEnd_4166474 := by exact prefixLift 4166474
  have htrace : WordTrace (prefixWord ++ tailWord_4166474) baseStart_4166474 baseEnd_4166474 := by
    simpa [prefixWord, tailWord_4166474, baseEnd_4166474] using wordTrace_append hprefix tailTrace_4166474
  have hstable : (prefixWord ++ tailWord_4166474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166474).length < 2 ^ (prefixWord ++ tailWord_4166474).sum := by decide
  have hdescent : baseEnd_4166474 < baseStart_4166474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166519 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_4166519 : Nat := 118140960795 + 4166519 * 2 ^ 59
def prefixEnd_4166519 : Nat := 4983230072969 + 3 ^ 40 * 4166519 * 2
def baseEnd_4166519 : Nat := 1426284602060326139300689

theorem tailTrace_4166519 : CollatzResearch.WordTrace tailWord_4166519 prefixEnd_4166519 1426284602060326139300689 := by
  unfold tailWord_4166519
  simp only [CollatzResearch.WordTrace]
  refine ⟨151965432392420722638150611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101310288261613815092100407 151965432392420722638150611)
  ·
    refine ⟨227948148588631083957225917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151965432392420722638150611 227948148588631083957225917)
    ·
      refine ⟨85480555720736656483959719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227948148588631083957225917 85480555720736656483959719)
      ·
        refine ⟨128220833581104984725939579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85480555720736656483959719 128220833581104984725939579)
        ·
          refine ⟨192331250371657477088909369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128220833581104984725939579 192331250371657477088909369)
          ·
            refine ⟨144248437778743107816682027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192331250371657477088909369 144248437778743107816682027)
            ·
              refine ⟨216372656668114661725023041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144248437778743107816682027 216372656668114661725023041)
              ·
                refine ⟨162279492501085996293767281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216372656668114661725023041 162279492501085996293767281)
                ·
                  refine ⟨121709619375814497220325461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162279492501085996293767281 121709619375814497220325461)
                  ·
                    refine ⟨1426284602060326139300689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121709619375814497220325461 1426284602060326139300689)
                    ·
                      rfl

theorem cell22_4166519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_4166519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166519 prefixEnd_4166519 := by exact prefixLift 4166519
  have htrace : WordTrace (prefixWord ++ tailWord_4166519) baseStart_4166519 baseEnd_4166519 := by
    simpa [prefixWord, tailWord_4166519, baseEnd_4166519] using wordTrace_append hprefix tailTrace_4166519
  have hstable : (prefixWord ++ tailWord_4166519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166519).length < 2 ^ (prefixWord ++ tailWord_4166519).sum := by decide
  have hdescent : baseEnd_4166519 < baseStart_4166519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166748 : List Nat := [2, 2, 4, 1, 1, 1, 1, 10]
def baseStart_4166748 : Nat := 118140960795 + 4166748 * 2 ^ 59
def prefixEnd_4166748 : Nat := 4983230072969 + 3 ^ 40 * 4166748 * 2
def baseEnd_4166748 : Nat := 158484777048916208369443

theorem tailTrace_4166748 : CollatzResearch.WordTrace tailWord_4166748 prefixEnd_4166748 158484777048916208369443 := by
  unfold tailWord_4166748
  simp only [CollatzResearch.WordTrace]
  refine ⟨75986892354295547374118449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101315856472394063165491265 75986892354295547374118449)
  ·
    refine ⟨56990169265721660530588837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75986892354295547374118449 56990169265721660530588837)
    ·
      refine ⟨10685656737322811349485407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56990169265721660530588837 10685656737322811349485407)
      ·
        refine ⟨16028485105984217024228111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685656737322811349485407 16028485105984217024228111)
        ·
          refine ⟨24042727658976325536342167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16028485105984217024228111 24042727658976325536342167)
          ·
            refine ⟨36064091488464488304513251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24042727658976325536342167 36064091488464488304513251)
            ·
              refine ⟨54096137232696732456769877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36064091488464488304513251 54096137232696732456769877)
              ·
                refine ⟨158484777048916208369443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54096137232696732456769877 158484777048916208369443)
                ·
                  rfl

theorem cell22_4166748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_4166748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166748 prefixEnd_4166748 := by exact prefixLift 4166748
  have htrace : WordTrace (prefixWord ++ tailWord_4166748) baseStart_4166748 baseEnd_4166748 := by
    simpa [prefixWord, tailWord_4166748, baseEnd_4166748] using wordTrace_append hprefix tailTrace_4166748
  have hstable : (prefixWord ++ tailWord_4166748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166748).length < 2 ^ (prefixWord ++ tailWord_4166748).sum := by decide
  have hdescent : baseEnd_4166748 < baseStart_4166748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166780 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_4166780 : Nat := 118140960795 + 4166780 * 2 ^ 59
def prefixEnd_4166780 : Nat := 4983230072969 + 3 ^ 40 * 4166780 * 2
def baseEnd_4166780 : Nat := 1426373947694208458524889

theorem tailTrace_4166780 : CollatzResearch.WordTrace tailWord_4166780 prefixEnd_4166780 1426373947694208458524889 := by
  unfold tailWord_4166780
  simp only [CollatzResearch.WordTrace]
  refine ⟨75987475922237582106700897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101316634562983442808934529 75987475922237582106700897)
  ·
    refine ⟨56990606941678186580025673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75987475922237582106700897 56990606941678186580025673)
    ·
      refine ⟨42742955206258639935019255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56990606941678186580025673 42742955206258639935019255)
      ·
        refine ⟨64114432809387959902528883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42742955206258639935019255 64114432809387959902528883)
        ·
          refine ⟨96171649214081939853793325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64114432809387959902528883 96171649214081939853793325)
          ·
            refine ⟨36064368455280727445172497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96171649214081939853793325 36064368455280727445172497)
            ·
              refine ⟨27048276341460545583879373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36064368455280727445172497 27048276341460545583879373)
              ·
                refine ⟨10143103628047704593954765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27048276341460545583879373 10143103628047704593954765)
                ·
                  refine ⟨3803663860517889222733037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10143103628047704593954765 3803663860517889222733037)
                  ·
                    refine ⟨1426373947694208458524889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803663860517889222733037 1426373947694208458524889)
                    ·
                      rfl

theorem cell22_4166780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_4166780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166780 prefixEnd_4166780 := by exact prefixLift 4166780
  have htrace : WordTrace (prefixWord ++ tailWord_4166780) baseStart_4166780 baseEnd_4166780 := by
    simpa [prefixWord, tailWord_4166780, baseEnd_4166780] using wordTrace_append hprefix tailTrace_4166780
  have hstable : (prefixWord ++ tailWord_4166780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166780).length < 2 ^ (prefixWord ++ tailWord_4166780).sum := by decide
  have hdescent : baseEnd_4166780 < baseStart_4166780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166960 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_4166960 : Nat := 118140960795 + 4166960 * 2 ^ 59
def prefixEnd_4166960 : Nat := 4983230072969 + 3 ^ 40 * 4166960 * 2
def baseEnd_4166960 : Nat := 1426435565372747989024337

theorem tailTrace_4166960 : CollatzResearch.WordTrace tailWord_4166960 prefixEnd_4166960 1426435565372747989024337 := by
  unfold tailWord_4166960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75990758491911527477477167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101321011322548703303302889 75990758491911527477477167)
  ·
    refine ⟨113986137737867291216215751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75990758491911527477477167 113986137737867291216215751)
    ·
      refine ⟨170979206606800936824323627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113986137737867291216215751 170979206606800936824323627)
      ·
        refine ⟨256468809910201405236485441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170979206606800936824323627 256468809910201405236485441)
        ·
          refine ⟨192351607432651053927364081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256468809910201405236485441 192351607432651053927364081)
          ·
            refine ⟨144263705574488290445523061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192351607432651053927364081 144263705574488290445523061)
            ·
              refine ⟨13524722397608277229267787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144263705574488290445523061 13524722397608277229267787)
              ·
                refine ⟨20287083596412415843901681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13524722397608277229267787 20287083596412415843901681)
                ·
                  refine ⟨15215312697309311882926261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20287083596412415843901681 15215312697309311882926261)
                  ·
                    refine ⟨1426435565372747989024337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15215312697309311882926261 1426435565372747989024337)
                    ·
                      rfl

theorem cell22_4166960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_4166960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166960 prefixEnd_4166960 := by exact prefixLift 4166960
  have htrace : WordTrace (prefixWord ++ tailWord_4166960) baseStart_4166960 baseEnd_4166960 := by
    simpa [prefixWord, tailWord_4166960, baseEnd_4166960] using wordTrace_append hprefix tailTrace_4166960
  have hstable : (prefixWord ++ tailWord_4166960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166960).length < 2 ^ (prefixWord ++ tailWord_4166960).sum := by decide
  have hdescent : baseEnd_4166960 < baseStart_4166960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166962 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_4166962 : Nat := 118140960795 + 4166962 * 2 ^ 59
def prefixEnd_4166962 : Nat := 4983230072969 + 3 ^ 40 * 4166962 * 2
def baseEnd_4166962 : Nat := 475478750004540216824777

theorem tailTrace_4166962 : CollatzResearch.WordTrace tailWord_4166962 prefixEnd_4166962 475478750004540216824777 := by
  unfold tailWord_4166962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37995397482453952324131785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101321059953210539531018093 37995397482453952324131785)
  ·
    refine ⟨28496548111840464243098839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37995397482453952324131785 28496548111840464243098839)
    ·
      refine ⟨42744822167760696364648259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28496548111840464243098839 42744822167760696364648259)
      ·
        refine ⟨64117233251641044546972389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42744822167760696364648259 64117233251641044546972389)
        ·
          refine ⟨12021981234682695852557323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64117233251641044546972389 12021981234682695852557323)
          ·
            refine ⟨18032971852024043778835985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12021981234682695852557323 18032971852024043778835985)
            ·
              refine ⟨13524728889018032834126989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18032971852024043778835985 13524728889018032834126989)
              ·
                refine ⟨5071773333381762312797621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13524728889018032834126989 5071773333381762312797621)
                ·
                  refine ⟨475478750004540216824777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071773333381762312797621 475478750004540216824777)
                  ·
                    rfl

theorem cell22_4166962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_4166962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166962 prefixEnd_4166962 := by exact prefixLift 4166962
  have htrace : WordTrace (prefixWord ++ tailWord_4166962) baseStart_4166962 baseEnd_4166962 := by
    simpa [prefixWord, tailWord_4166962, baseEnd_4166962] using wordTrace_append hprefix tailTrace_4166962
  have hstable : (prefixWord ++ tailWord_4166962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166962).length < 2 ^ (prefixWord ++ tailWord_4166962).sum := by decide
  have hdescent : baseEnd_4166962 < baseStart_4166962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166990 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_4166990 : Nat := 118140960795 + 4166990 * 2 ^ 59
def prefixEnd_4166990 : Nat := 4983230072969 + 3 ^ 40 * 4166990 * 2
def baseEnd_4166990 : Nat := 475481944995279303591415

theorem tailTrace_4166990 : CollatzResearch.WordTrace tailWord_4166990 prefixEnd_4166990 475481944995279303591415 := by
  unfold tailWord_4166990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997826396714296259818303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101321740782476246719030949 18997826396714296259818303)
  ·
    refine ⟨28496739595071444389727455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18997826396714296259818303 28496739595071444389727455)
    ·
      refine ⟨42745109392607166584591183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28496739595071444389727455 42745109392607166584591183)
      ·
        refine ⟨64117664088910749876886775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42745109392607166584591183 64117664088910749876886775)
        ·
          refine ⟨96176496133366124815330163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64117664088910749876886775 96176496133366124815330163)
          ·
            refine ⟨144264744200049187222995245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96176496133366124815330163 144264744200049187222995245)
            ·
              refine ⟨54099279075018445208623217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144264744200049187222995245 54099279075018445208623217)
              ·
                refine ⟨40574459306263833906467413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54099279075018445208623217 40574459306263833906467413)
                ·
                  refine ⟨475481944995279303591415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40574459306263833906467413 475481944995279303591415)
                  ·
                    rfl

theorem cell22_4166990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_4166990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166990 prefixEnd_4166990 := by exact prefixLift 4166990
  have htrace : WordTrace (prefixWord ++ tailWord_4166990) baseStart_4166990 baseEnd_4166990 := by
    simpa [prefixWord, tailWord_4166990, baseEnd_4166990] using wordTrace_append hprefix tailTrace_4166990
  have hstable : (prefixWord ++ tailWord_4166990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166990).length < 2 ^ (prefixWord ++ tailWord_4166990).sum := by decide
  have hdescent : baseEnd_4166990 < baseStart_4166990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166992 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_4166992 : Nat := 118140960795 + 4166992 * 2 ^ 59
def prefixEnd_4166992 : Nat := 4983230072969 + 3 ^ 40 * 4166992 * 2
def baseEnd_4166992 : Nat := 1426446519626710572224239

theorem tailTrace_4166992 : CollatzResearch.WordTrace tailWord_4166992 prefixEnd_4166992 1426446519626710572224239 := by
  unfold tailWord_4166992
  simp only [CollatzResearch.WordTrace]
  refine ⟨75991342059853562210059615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101321789413138082946746153 75991342059853562210059615)
  ·
    refine ⟨113987013089780343315089423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75991342059853562210059615 113987013089780343315089423)
    ·
      refine ⟨170980519634670514972634135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113987013089780343315089423 170980519634670514972634135)
      ·
        refine ⟨256470779452005772458951203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170980519634670514972634135 256470779452005772458951203)
        ·
          refine ⟨384706169178008658688426805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256470779452005772458951203 384706169178008658688426805)
          ·
            refine ⟨36066203360438311752040013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384706169178008658688426805 36066203360438311752040013)
            ·
              refine ⟨13524826260164366907015005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36066203360438311752040013 13524826260164366907015005)
              ·
                refine ⟨5071809847561637590130627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13524826260164366907015005 5071809847561637590130627)
                ·
                  refine ⟨7607714771342456385195941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071809847561637590130627 7607714771342456385195941)
                  ·
                    refine ⟨1426446519626710572224239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7607714771342456385195941 1426446519626710572224239)
                    ·
                      rfl

theorem cell22_4166992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_4166992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4166992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4166992 prefixEnd_4166992 := by exact prefixLift 4166992
  have htrace : WordTrace (prefixWord ++ tailWord_4166992) baseStart_4166992 baseEnd_4166992 := by
    simpa [prefixWord, tailWord_4166992, baseEnd_4166992] using wordTrace_append hprefix tailTrace_4166992
  have hstable : (prefixWord ++ tailWord_4166992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166992).length < 2 ^ (prefixWord ++ tailWord_4166992).sum := by decide
  have hdescent : baseEnd_4166992 < baseStart_4166992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167035 : List Nat := [1, 1, 1, 1, 1, 6, 3, 8]
def baseStart_4167035 : Nat := 118140960795 + 4167035 * 2 ^ 59
def prefixEnd_4167035 : Nat := 4983230072969 + 3 ^ 40 * 4167035 * 2
def baseEnd_4167035 : Nat := 158495693267274754822123

theorem tailTrace_4167035 : CollatzResearch.WordTrace tailWord_4167035 prefixEnd_4167035 158495693267274754822123 := by
  unfold tailWord_4167035
  simp only [CollatzResearch.WordTrace]
  refine ⟨151984252458551342763934559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101322834972367561842623039 151984252458551342763934559)
  ·
    refine ⟨227976378687827014145901839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151984252458551342763934559 227976378687827014145901839)
    ·
      refine ⟨341964568031740521218852759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227976378687827014145901839 341964568031740521218852759)
      ·
        refine ⟨512946852047610781828279139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341964568031740521218852759 512946852047610781828279139)
        ·
          refine ⟨769420278071416172742418709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512946852047610781828279139 769420278071416172742418709)
          ·
            refine ⟨36066575534597633097300877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 769420278071416172742418709 36066575534597633097300877)
            ·
              refine ⟨13524965825474112411487829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36066575534597633097300877 13524965825474112411487829)
              ·
                refine ⟨158495693267274754822123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13524965825474112411487829 158495693267274754822123)
                ·
                  rfl

theorem cell22_4167035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 8].length) (baseStart_4167035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167035 prefixEnd_4167035 := by exact prefixLift 4167035
  have htrace : WordTrace (prefixWord ++ tailWord_4167035) baseStart_4167035 baseEnd_4167035 := by
    simpa [prefixWord, tailWord_4167035, baseEnd_4167035] using wordTrace_append hprefix tailTrace_4167035
  have hstable : (prefixWord ++ tailWord_4167035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167035).length < 2 ^ (prefixWord ++ tailWord_4167035).sum := by decide
  have hdescent : baseEnd_4167035 < baseStart_4167035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167037 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4167037 : Nat := 118140960795 + 4167037 * 2 ^ 59
def prefixEnd_4167037 : Nat := 4983230072969 + 3 ^ 40 * 4167037 * 2
def baseEnd_4167037 : Nat := 1426461924046345454849101

theorem tailTrace_4167037 : CollatzResearch.WordTrace tailWord_4167037 prefixEnd_4167037 1426461924046345454849101 := by
  unfold tailWord_4167037
  simp only [CollatzResearch.WordTrace]
  refine ⟨151984325404544097105507365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101322883603029398070338243 151984325404544097105507365)
  ·
    refine ⟨28497061013352018207282631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151984325404544097105507365 28497061013352018207282631)
    ·
      refine ⟨42745591520028027310923947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28497061013352018207282631 42745591520028027310923947)
      ·
        refine ⟨64118387280042040966385921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42745591520028027310923947 64118387280042040966385921)
        ·
          refine ⟨48088790460031530724789441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64118387280042040966385921 48088790460031530724789441)
          ·
            refine ⟨36066592845023648043592081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48088790460031530724789441 36066592845023648043592081)
            ·
              refine ⟨27049944633767736032694061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36066592845023648043592081 27049944633767736032694061)
              ·
                refine ⟨10143729237662901012260273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27049944633767736032694061 10143729237662901012260273)
                ·
                  refine ⟨7607796928247175759195205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10143729237662901012260273 7607796928247175759195205)
                  ·
                    refine ⟨1426461924046345454849101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7607796928247175759195205 1426461924046345454849101)
                    ·
                      rfl

theorem cell22_4167037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4167037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167037 prefixEnd_4167037 := by exact prefixLift 4167037
  have htrace : WordTrace (prefixWord ++ tailWord_4167037) baseStart_4167037 baseEnd_4167037 := by
    simpa [prefixWord, tailWord_4167037, baseEnd_4167037] using wordTrace_append hprefix tailTrace_4167037
  have hstable : (prefixWord ++ tailWord_4167037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167037).length < 2 ^ (prefixWord ++ tailWord_4167037).sum := by decide
  have hdescent : baseEnd_4167037 < baseStart_4167037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167058 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_4167058 : Nat := 118140960795 + 4167058 * 2 ^ 59
def prefixEnd_4167058 : Nat := 4983230072969 + 3 ^ 40 * 4167058 * 2
def baseEnd_4167058 : Nat := 475489704258502800024679

theorem tailTrace_4167058 : CollatzResearch.WordTrace tailWord_4167058 prefixEnd_4167058 475489704258502800024679 := by
  unfold tailWord_4167058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37996272834367004423005457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101323394224978678461347885 37996272834367004423005457)
  ·
    refine ⟨28497204625775253317254093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37996272834367004423005457 28497204625775253317254093)
    ·
      refine ⟨10686451734665719993970285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28497204625775253317254093 10686451734665719993970285)
      ·
        refine ⟨4007419400499644997738857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10686451734665719993970285 4007419400499644997738857)
        ·
          refine ⟨3005564550374733748304143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007419400499644997738857 3005564550374733748304143)
          ·
            refine ⟨4508346825562100622456215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005564550374733748304143 4508346825562100622456215)
            ·
              refine ⟨6762520238343150933684323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508346825562100622456215 6762520238343150933684323)
              ·
                refine ⟨10143780357514726400526485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762520238343150933684323 10143780357514726400526485)
                ·
                  refine ⟨475489704258502800024679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10143780357514726400526485 475489704258502800024679)
                  ·
                    rfl

theorem cell22_4167058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_4167058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167058 prefixEnd_4167058 := by exact prefixLift 4167058
  have htrace : WordTrace (prefixWord ++ tailWord_4167058) baseStart_4167058 baseEnd_4167058 := by
    simpa [prefixWord, tailWord_4167058, baseEnd_4167058] using wordTrace_append hprefix tailTrace_4167058
  have hstable : (prefixWord ++ tailWord_4167058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167058).length < 2 ^ (prefixWord ++ tailWord_4167058).sum := by decide
  have hdescent : baseEnd_4167058 < baseStart_4167058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167101 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_4167101 : Nat := 118140960795 + 4167101 * 2 ^ 59
def prefixEnd_4167101 : Nat := 4983230072969 + 3 ^ 40 * 4167101 * 2
def baseEnd_4167101 : Nat := 1426483832554270621248905

theorem tailTrace_4167101 : CollatzResearch.WordTrace tailWord_4167101 prefixEnd_4167101 1426483832554270621248905 := by
  unfold tailWord_4167101
  simp only [CollatzResearch.WordTrace]
  refine ⟨151986659676312236035837157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101324439784208157357224771 151986659676312236035837157)
  ·
    refine ⟨28497498689308544256719467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151986659676312236035837157 28497498689308544256719467)
    ·
      refine ⟨42746248033962816385079201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28497498689308544256719467 42746248033962816385079201)
      ·
        refine ⟨32059686025472112288809401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42746248033962816385079201 32059686025472112288809401)
        ·
          refine ⟨24044764519104084216607051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32059686025472112288809401 24044764519104084216607051)
          ·
            refine ⟨36067146778656126324910577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24044764519104084216607051 36067146778656126324910577)
            ·
              refine ⟨27050360083992094743682933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36067146778656126324910577 27050360083992094743682933)
              ·
                refine ⟨2535971257874258882220275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27050360083992094743682933 2535971257874258882220275)
                ·
                  refine ⟨3803956886811388323330413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535971257874258882220275 3803956886811388323330413)
                  ·
                    refine ⟨1426483832554270621248905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803956886811388323330413 1426483832554270621248905)
                    ·
                      rfl

theorem cell22_4167101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_4167101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167101 prefixEnd_4167101 := by exact prefixLift 4167101
  have htrace : WordTrace (prefixWord ++ tailWord_4167101) baseStart_4167101 baseEnd_4167101 := by
    simpa [prefixWord, tailWord_4167101, baseEnd_4167101] using wordTrace_append hprefix tailTrace_4167101
  have hstable : (prefixWord ++ tailWord_4167101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167101).length < 2 ^ (prefixWord ++ tailWord_4167101).sum := by decide
  have hdescent : baseEnd_4167101 < baseStart_4167101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167112 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_4167112 : Nat := 118140960795 + 4167112 * 2 ^ 59
def prefixEnd_4167112 : Nat := 4983230072969 + 3 ^ 40 * 4167112 * 2
def baseEnd_4167112 : Nat := 1426487598079070259223871

theorem tailTrace_4167112 : CollatzResearch.WordTrace tailWord_4167112 prefixEnd_4167112 1426487598079070259223871 := by
  unfold tailWord_4167112
  simp only [CollatzResearch.WordTrace]
  refine ⟨75993530439636192457243795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101324707252848256609658393 75993530439636192457243795)
  ·
    refine ⟨113990295659454288685865693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75993530439636192457243795 113990295659454288685865693)
    ·
      refine ⟨42746360872295358257199635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113990295659454288685865693 42746360872295358257199635)
      ·
        refine ⟨64119541308443037385799453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42746360872295358257199635 64119541308443037385799453)
        ·
          refine ⟨24044827990666139019674795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64119541308443037385799453 24044827990666139019674795)
          ·
            refine ⟨36067241985999208529512193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24044827990666139019674795 36067241985999208529512193)
            ·
              refine ⟨27050431489499406397134145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36067241985999208529512193 27050431489499406397134145)
              ·
                refine ⟨20287823617124554797850609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27050431489499406397134145 20287823617124554797850609)
                ·
                  refine ⟨15215867712843416098387957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20287823617124554797850609 15215867712843416098387957)
                  ·
                    refine ⟨1426487598079070259223871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15215867712843416098387957 1426487598079070259223871)
                    ·
                      rfl

theorem cell22_4167112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_4167112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167112 prefixEnd_4167112 := by exact prefixLift 4167112
  have htrace : WordTrace (prefixWord ++ tailWord_4167112) baseStart_4167112 baseEnd_4167112 := by
    simpa [prefixWord, tailWord_4167112, baseEnd_4167112] using wordTrace_append hprefix tailTrace_4167112
  have hstable : (prefixWord ++ tailWord_4167112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167112).length < 2 ^ (prefixWord ++ tailWord_4167112).sum := by decide
  have hdescent : baseEnd_4167112 < baseStart_4167112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167114 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_4167114 : Nat := 118140960795 + 4167114 * 2 ^ 59
def prefixEnd_4167114 : Nat := 4983230072969 + 3 ^ 40 * 4167114 * 2
def baseEnd_4167114 : Nat := 475496094239980973557955

theorem tailTrace_4167114 : CollatzResearch.WordTrace tailWord_4167114 prefixEnd_4167114 475496094239980973557955 := by
  unfold tailWord_4167114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37996783456316284814015099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101324755883510092837373597 37996783456316284814015099)
  ·
    refine ⟨56995175184474427221022649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37996783456316284814015099 56995175184474427221022649)
    ·
      refine ⟨42746381388355820415766987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56995175184474427221022649 42746381388355820415766987)
      ·
        refine ⟨64119572082533730623650481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42746381388355820415766987 64119572082533730623650481)
        ·
          refine ⟨48089679061900297967737861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64119572082533730623650481 48089679061900297967737861)
          ·
            refine ⟨9016814824106305868950849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48089679061900297967737861 9016814824106305868950849)
            ·
              refine ⟨6762611118079729401713137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9016814824106305868950849 6762611118079729401713137)
              ·
                refine ⟨5071958338559797051284853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762611118079729401713137 5071958338559797051284853)
                ·
                  refine ⟨475496094239980973557955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071958338559797051284853 475496094239980973557955)
                  ·
                    rfl

theorem cell22_4167114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_4167114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167114 prefixEnd_4167114 := by exact prefixLift 4167114
  have htrace : WordTrace (prefixWord ++ tailWord_4167114) baseStart_4167114 baseEnd_4167114 := by
    simpa [prefixWord, tailWord_4167114, baseEnd_4167114] using wordTrace_append hprefix tailTrace_4167114
  have hstable : (prefixWord ++ tailWord_4167114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167114).length < 2 ^ (prefixWord ++ tailWord_4167114).sum := by decide
  have hdescent : baseEnd_4167114 < baseStart_4167114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167118 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_4167118 : Nat := 118140960795 + 4167118 * 2 ^ 59
def prefixEnd_4167118 : Nat := 4983230072969 + 3 ^ 40 * 4167118 * 2
def baseEnd_4167118 : Nat := 1426489652001688243573853

theorem tailTrace_4167118 : CollatzResearch.WordTrace tailWord_4167118 prefixEnd_4167118 1426489652001688243573853 := by
  unfold tailWord_4167118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998409964656330992400751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101324853144833765292804005 18998409964656330992400751)
  ·
    refine ⟨28497614946984496488601127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18998409964656330992400751 28497614946984496488601127)
    ·
      refine ⟨42746422420476744732901691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28497614946984496488601127 42746422420476744732901691)
      ·
        refine ⟨64119633630715117099352537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42746422420476744732901691 64119633630715117099352537)
        ·
          refine ⟨48089725223036337824514403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64119633630715117099352537 48089725223036337824514403)
          ·
            refine ⟨72134587834554506736771605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48089725223036337824514403 72134587834554506736771605)
            ·
              refine ⟨3381308804744742503286169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72134587834554506736771605 3381308804744742503286169)
              ·
                refine ⟨2535981603558556877464627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381308804744742503286169 2535981603558556877464627)
                ·
                  refine ⟨3803972405337835316196941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535981603558556877464627 3803972405337835316196941)
                  ·
                    refine ⟨1426489652001688243573853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803972405337835316196941 1426489652001688243573853)
                    ·
                      rfl

theorem cell22_4167118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_4167118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167118 prefixEnd_4167118 := by exact prefixLift 4167118
  have htrace : WordTrace (prefixWord ++ tailWord_4167118) baseStart_4167118 baseEnd_4167118 := by
    simpa [prefixWord, tailWord_4167118, baseEnd_4167118] using wordTrace_append hprefix tailTrace_4167118
  have hstable : (prefixWord ++ tailWord_4167118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167118).length < 2 ^ (prefixWord ++ tailWord_4167118).sum := by decide
  have hdescent : baseEnd_4167118 < baseStart_4167118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167144 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_4167144 : Nat := 118140960795 + 4167144 * 2 ^ 59
def prefixEnd_4167144 : Nat := 4983230072969 + 3 ^ 40 * 4167144 * 2
def baseEnd_4167144 : Nat := 1426498552333032842423773

theorem tailTrace_4167144 : CollatzResearch.WordTrace tailWord_4167144 prefixEnd_4167144 1426498552333032842423773 := by
  unfold tailWord_4167144
  simp only [CollatzResearch.WordTrace]
  refine ⟨75994114007578227189826243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101325485343437636253101657 75994114007578227189826243)
  ·
    refine ⟨113991171011367340784739365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75994114007578227189826243 113991171011367340784739365)
    ·
      refine ⟨21373344564631376397138631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113991171011367340784739365 21373344564631376397138631)
      ·
        refine ⟨32060016846947064595707947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21373344564631376397138631 32060016846947064595707947)
        ·
          refine ⟨48090025270420596893561921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32060016846947064595707947 48090025270420596893561921)
          ·
            refine ⟨36067518952815447670171441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48090025270420596893561921 36067518952815447670171441)
            ·
              refine ⟨27050639214611585752628581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36067518952815447670171441 27050639214611585752628581)
              ·
                refine ⟨5071994852739672328617859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27050639214611585752628581 5071994852739672328617859)
                ·
                  refine ⟨7607992279109508492926789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071994852739672328617859 7607992279109508492926789)
                  ·
                    refine ⟨1426498552333032842423773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7607992279109508492926789 1426498552333032842423773)
                    ·
                      rfl

theorem cell22_4167144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_4167144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167144 prefixEnd_4167144 := by exact prefixLift 4167144
  have htrace : WordTrace (prefixWord ++ tailWord_4167144) baseStart_4167144 baseEnd_4167144 := by
    simpa [prefixWord, tailWord_4167144, baseEnd_4167144] using wordTrace_append hprefix tailTrace_4167144
  have hstable : (prefixWord ++ tailWord_4167144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167144).length < 2 ^ (prefixWord ++ tailWord_4167144).sum := by decide
  have hdescent : baseEnd_4167144 < baseStart_4167144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167217 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_4167217 : Nat := 118140960795 + 4167217 * 2 ^ 59
def prefixEnd_4167217 : Nat := 4983230072969 + 3 ^ 40 * 4167217 * 2
def baseEnd_4167217 : Nat := 1426523541724884985348549

theorem tailTrace_4167217 : CollatzResearch.WordTrace tailWord_4167217 prefixEnd_4167217 1426523541724884985348549 := by
  unfold tailWord_4167217
  simp only [CollatzResearch.WordTrace]
  refine ⟨151990890543891987847059905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101327260362594658564706603 151990890543891987847059905)
  ·
    refine ⟨113993167907918990885294929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151990890543891987847059905 113993167907918990885294929)
    ·
      refine ⟨85494875930939243163971197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113993167907918990885294929 85494875930939243163971197)
      ·
        refine ⟨32060578474102216186489199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85494875930939243163971197 32060578474102216186489199)
        ·
          refine ⟨48090867711153324279733799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32060578474102216186489199 48090867711153324279733799)
          ·
            refine ⟨72136301566729986419600699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48090867711153324279733799 72136301566729986419600699)
            ·
              refine ⟨108204452350094979629401049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72136301566729986419600699 108204452350094979629401049)
              ·
                refine ⟨81153339262571234722050787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108204452350094979629401049 81153339262571234722050787)
                ·
                  refine ⟨121730008893856852083076181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81153339262571234722050787 121730008893856852083076181)
                  ·
                    refine ⟨1426523541724884985348549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121730008893856852083076181 1426523541724884985348549)
                    ·
                      rfl

theorem cell22_4167217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_4167217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167217 prefixEnd_4167217 := by exact prefixLift 4167217
  have htrace : WordTrace (prefixWord ++ tailWord_4167217) baseStart_4167217 baseEnd_4167217 := by
    simpa [prefixWord, tailWord_4167217, baseEnd_4167217] using wordTrace_append hprefix tailTrace_4167217
  have hstable : (prefixWord ++ tailWord_4167217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167217).length < 2 ^ (prefixWord ++ tailWord_4167217).sum := by decide
  have hdescent : baseEnd_4167217 < baseStart_4167217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167238 : List Nat := [6, 1, 1, 1, 3, 1, 2, 7]
def baseStart_4167238 : Nat := 118140960795 + 4167238 * 2 ^ 59
def prefixEnd_4167238 : Nat := 4983230072969 + 3 ^ 40 * 4167238 * 2
def baseEnd_4167238 : Nat := 158503414494894214508165

theorem tailTrace_4167238 : CollatzResearch.WordTrace tailWord_4167238 prefixEnd_4167238 158503414494894214508165 := by
  unfold tailWord_4167238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749739264900497138549199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101327770984543938955716245 4749739264900497138549199)
  ·
    refine ⟨7124608897350745707823799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4749739264900497138549199 7124608897350745707823799)
    ·
      refine ⟨10686913346026118561735699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124608897350745707823799 10686913346026118561735699)
      ·
        refine ⟨16030370019039177842603549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686913346026118561735699 16030370019039177842603549)
        ·
          refine ⟨6011388757139691690976331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16030370019039177842603549 6011388757139691690976331)
          ·
            refine ⟨9017083135709537536464497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011388757139691690976331 9017083135709537536464497)
            ·
              refine ⟨6762812351782153152348373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9017083135709537536464497 6762812351782153152348373)
              ·
                refine ⟨158503414494894214508165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6762812351782153152348373 158503414494894214508165)
                ·
                  rfl

theorem cell22_4167238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_4167238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167238 prefixEnd_4167238 := by exact prefixLift 4167238
  have htrace : WordTrace (prefixWord ++ tailWord_4167238) baseStart_4167238 baseEnd_4167238 := by
    simpa [prefixWord, tailWord_4167238, baseEnd_4167238] using wordTrace_append hprefix tailTrace_4167238
  have hstable : (prefixWord ++ tailWord_4167238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167238).length < 2 ^ (prefixWord ++ tailWord_4167238).sum := by decide
  have hdescent : baseEnd_4167238 < baseStart_4167238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167247 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_4167247 : Nat := 118140960795 + 4167247 * 2 ^ 59
def prefixEnd_4167247 : Nat := 4983230072969 + 3 ^ 40 * 4167247 * 2
def baseEnd_4167247 : Nat := 1426533811337974907098457

theorem tailTrace_4167247 : CollatzResearch.WordTrace tailWord_4167247 prefixEnd_4167247 1426533811337974907098457 := by
  unfold tailWord_4167247
  simp only [CollatzResearch.WordTrace]
  refine ⟨151991984733783302970651995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101327989822522201980434663 151991984733783302970651995)
  ·
    refine ⟨227987977100674954455977993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151991984733783302970651995 227987977100674954455977993)
    ·
      refine ⟨170990982825506215841983495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227987977100674954455977993 170990982825506215841983495)
      ·
        refine ⟨256486474238259323762975243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170990982825506215841983495 256486474238259323762975243)
        ·
          refine ⟨384729711357388985644462865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256486474238259323762975243 384729711357388985644462865)
          ·
            refine ⟨288547283518041739233347149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384729711357388985644462865 288547283518041739233347149)
            ·
              refine ⟨108205231319265652212505181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288547283518041739233347149 108205231319265652212505181)
              ·
                refine ⟨40576961744724619579689443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108205231319265652212505181 40576961744724619579689443)
                ·
                  refine ⟨60865442617086929369534165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40576961744724619579689443 60865442617086929369534165)
                  ·
                    refine ⟨1426533811337974907098457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60865442617086929369534165 1426533811337974907098457)
                    ·
                      rfl

theorem cell22_4167247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_4167247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167247 prefixEnd_4167247 := by exact prefixLift 4167247
  have htrace : WordTrace (prefixWord ++ tailWord_4167247) baseStart_4167247 baseEnd_4167247 := by
    simpa [prefixWord, tailWord_4167247, baseEnd_4167247] using wordTrace_append hprefix tailTrace_4167247
  have hstable : (prefixWord ++ tailWord_4167247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167247).length < 2 ^ (prefixWord ++ tailWord_4167247).sum := by decide
  have hdescent : baseEnd_4167247 < baseStart_4167247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167249 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 5]
def baseStart_4167249 : Nat := 118140960795 + 4167249 * 2 ^ 59
def prefixEnd_4167249 : Nat := 4983230072969 + 3 ^ 40 * 4167249 * 2
def baseEnd_4167249 : Nat := 475511498659615856182817

theorem tailTrace_4167249 : CollatzResearch.WordTrace tailWord_4167249 prefixEnd_4167249 475511498659615856182817 := by
  unfold tailWord_4167249
  simp only [CollatzResearch.WordTrace]
  refine ⟨151992057679776057312224801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101328038453184038208149867 151992057679776057312224801)
  ·
    refine ⟨113994043259832042984168601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151992057679776057312224801 113994043259832042984168601)
    ·
      refine ⟨85495532444874032238126451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113994043259832042984168601 85495532444874032238126451)
      ·
        refine ⟨128243298667311048357189677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85495532444874032238126451 128243298667311048357189677)
        ·
          refine ⟨48091237000241643133946129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128243298667311048357189677 48091237000241643133946129)
          ·
            refine ⟨36068427750181232350459597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48091237000241643133946129 36068427750181232350459597)
            ·
              refine ⟨13525660406317962131422349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36068427750181232350459597 13525660406317962131422349)
              ·
                refine ⟨5072122652369235799283381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13525660406317962131422349 5072122652369235799283381)
                ·
                  refine ⟨475511498659615856182817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5072122652369235799283381 475511498659615856182817)
                  ·
                    rfl

theorem cell22_4167249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_4167249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167249 prefixEnd_4167249 := by exact prefixLift 4167249
  have htrace : WordTrace (prefixWord ++ tailWord_4167249) baseStart_4167249 baseEnd_4167249 := by
    simpa [prefixWord, tailWord_4167249, baseEnd_4167249] using wordTrace_append hprefix tailTrace_4167249
  have hstable : (prefixWord ++ tailWord_4167249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167249).length < 2 ^ (prefixWord ++ tailWord_4167249).sum := by decide
  have hdescent : baseEnd_4167249 < baseStart_4167249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167328 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 4]
def baseStart_4167328 : Nat := 118140960795 + 4167328 * 2 ^ 59
def prefixEnd_4167328 : Nat := 4983230072969 + 3 ^ 40 * 4167328 * 2
def baseEnd_4167328 : Nat := 475520513097772565274403

theorem tailTrace_4167328 : CollatzResearch.WordTrace tailWord_4167328 prefixEnd_4167328 475520513097772565274403 := by
  unfold tailWord_4167328
  simp only [CollatzResearch.WordTrace]
  refine ⟨75997469523244926902175319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101329959364326569202900425 75997469523244926902175319)
  ·
    refine ⟨113996204284867390353262979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75997469523244926902175319 113996204284867390353262979)
    ·
      refine ⟨170994306427301085529894469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113996204284867390353262979 170994306427301085529894469)
      ·
        refine ⟨32061432455118953536855213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170994306427301085529894469 32061432455118953536855213)
        ·
          refine ⟨12023037170669607576320705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32061432455118953536855213 12023037170669607576320705)
          ·
            refine ⟨9017277878002205682240529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12023037170669607576320705 9017277878002205682240529)
            ·
              refine ⟨6762958408501654261680397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9017277878002205682240529 6762958408501654261680397)
              ·
                refine ⟨2536109403188120348130149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6762958408501654261680397 2536109403188120348130149)
                ·
                  refine ⟨475520513097772565274403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536109403188120348130149 475520513097772565274403)
                  ·
                    rfl

theorem cell22_4167328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_4167328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167328 prefixEnd_4167328 := by exact prefixLift 4167328
  have htrace : WordTrace (prefixWord ++ tailWord_4167328) baseStart_4167328 baseEnd_4167328 := by
    simpa [prefixWord, tailWord_4167328, baseEnd_4167328] using wordTrace_append hprefix tailTrace_4167328
  have hstable : (prefixWord ++ tailWord_4167328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167328).length < 2 ^ (prefixWord ++ tailWord_4167328).sum := by decide
  have hdescent : baseEnd_4167328 < baseStart_4167328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167330 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_4167330 : Nat := 118140960795 + 4167330 * 2 ^ 59
def prefixEnd_4167330 : Nat := 4983230072969 + 3 ^ 40 * 4167330 * 2
def baseEnd_4167330 : Nat := 1426562223934190357273203

theorem tailTrace_4167330 : CollatzResearch.WordTrace tailWord_4167330 prefixEnd_4167330 1426562223934190357273203 := by
  unfold tailWord_4167330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37998752998120652036480861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101330007994988405430615629 37998752998120652036480861)
  ·
    refine ⟨14249532374295244513680323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37998752998120652036480861 14249532374295244513680323)
    ·
      refine ⟨21374298561442866770520485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249532374295244513680323 21374298561442866770520485)
      ·
        refine ⟨4007680980270537519472591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21374298561442866770520485 4007680980270537519472591)
        ·
          refine ⟨6011521470405806279208887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007680980270537519472591 6011521470405806279208887)
          ·
            refine ⟨9017282205608709418813331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011521470405806279208887 9017282205608709418813331)
            ·
              refine ⟨13525923308413064128219997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017282205608709418813331 13525923308413064128219997)
              ·
                refine ⟨5072221240654899048082499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13525923308413064128219997 5072221240654899048082499)
                ·
                  refine ⟨7608331860982348572123749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072221240654899048082499 7608331860982348572123749)
                  ·
                    refine ⟨1426562223934190357273203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608331860982348572123749 1426562223934190357273203)
                    ·
                      rfl

theorem cell22_4167330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_4167330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167330 prefixEnd_4167330 := by exact prefixLift 4167330
  have htrace : WordTrace (prefixWord ++ tailWord_4167330) baseStart_4167330 baseEnd_4167330 := by
    simpa [prefixWord, tailWord_4167330, baseEnd_4167330] using wordTrace_append hprefix tailTrace_4167330
  have hstable : (prefixWord ++ tailWord_4167330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167330).length < 2 ^ (prefixWord ++ tailWord_4167330).sum := by decide
  have hdescent : baseEnd_4167330 < baseStart_4167330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167341 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4167341 : Nat := 118140960795 + 4167341 * 2 ^ 59
def prefixEnd_4167341 : Nat := 4983230072969 + 3 ^ 40 * 4167341 * 2
def baseEnd_4167341 : Nat := 1426565989458989995248169

theorem tailTrace_4167341 : CollatzResearch.WordTrace tailWord_4167341 prefixEnd_4167341 1426565989458989995248169 := by
  unfold tailWord_4167341
  simp only [CollatzResearch.WordTrace]
  refine ⟨151995413195442757024573877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101330275463628504683049251 151995413195442757024573877)
  ·
    refine ⟨14249569987072758471053801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151995413195442757024573877 14249569987072758471053801)
    ·
      refine ⟨10687177490304568853290351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14249569987072758471053801 10687177490304568853290351)
      ·
        refine ⟨16030766235456853279935527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10687177490304568853290351 16030766235456853279935527)
        ·
          refine ⟨24046149353185279919903291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16030766235456853279935527 24046149353185279919903291)
          ·
            refine ⟨36069224029777919879854937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24046149353185279919903291 36069224029777919879854937)
            ·
              refine ⟨27051918022333439909891203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36069224029777919879854937 27051918022333439909891203)
              ·
                refine ⟨40577877033500159864836805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27051918022333439909891203 40577877033500159864836805)
                ·
                  refine ⟨7608351943781279974656901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40577877033500159864836805 7608351943781279974656901)
                  ·
                    refine ⟨1426565989458989995248169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608351943781279974656901 1426565989458989995248169)
                    ·
                      rfl

theorem cell22_4167341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4167341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167341 prefixEnd_4167341 := by exact prefixLift 4167341
  have htrace : WordTrace (prefixWord ++ tailWord_4167341) baseStart_4167341 baseEnd_4167341 := by
    simpa [prefixWord, tailWord_4167341, baseEnd_4167341] using wordTrace_append hprefix tailTrace_4167341
  have hstable : (prefixWord ++ tailWord_4167341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167341).length < 2 ^ (prefixWord ++ tailWord_4167341).sum := by decide
  have hdescent : baseEnd_4167341 < baseStart_4167341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167373 : List Nat := [1, 6, 2, 1, 1, 2, 1, 8]
def baseStart_4167373 : Nat := 118140960795 + 4167373 * 2 ^ 59
def prefixEnd_4167373 : Nat := 4983230072969 + 3 ^ 40 * 4167373 * 2
def baseEnd_4167373 : Nat := 158508549301439175383119

theorem tailTrace_4167373 : CollatzResearch.WordTrace tailWord_4167373 prefixEnd_4167373 158508549301439175383119 := by
  unfold tailWord_4167373
  simp only [CollatzResearch.WordTrace]
  refine ⟨151996580331326826489738773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101331053554217884326492515 151996580331326826489738773)
  ·
    refine ⟨7124839703030944991706505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151996580331326826489738773 7124839703030944991706505)
    ·
      refine ⟨5343629777273208743779879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7124839703030944991706505 5343629777273208743779879)
      ·
        refine ⟨8015444665909813115669819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343629777273208743779879 8015444665909813115669819)
        ·
          refine ⟨12023166998864719673504729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8015444665909813115669819 12023166998864719673504729)
          ·
            refine ⟨9017375249148539755128547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12023166998864719673504729 9017375249148539755128547)
            ·
              refine ⟨13526062873722809632692821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017375249148539755128547 13526062873722809632692821)
              ·
                refine ⟨158508549301439175383119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13526062873722809632692821 158508549301439175383119)
                ·
                  rfl

theorem cell22_4167373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 8].length) (baseStart_4167373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167373 prefixEnd_4167373 := by exact prefixLift 4167373
  have htrace : WordTrace (prefixWord ++ tailWord_4167373) baseStart_4167373 baseEnd_4167373 := by
    simpa [prefixWord, tailWord_4167373, baseEnd_4167373] using wordTrace_append hprefix tailTrace_4167373
  have hstable : (prefixWord ++ tailWord_4167373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167373).length < 2 ^ (prefixWord ++ tailWord_4167373).sum := by decide
  have hdescent : baseEnd_4167373 < baseStart_4167373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167384 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_4167384 : Nat := 118140960795 + 4167384 * 2 ^ 59
def prefixEnd_4167384 : Nat := 4983230072969 + 3 ^ 40 * 4167384 * 2
def baseEnd_4167384 : Nat := 475526903079250738807679

theorem tailTrace_4167384 : CollatzResearch.WordTrace tailWord_4167384 prefixEnd_4167384 475526903079250738807679 := by
  unfold tailWord_4167384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75998490767143487684194603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101331321022857983578926137 75998490767143487684194603)
  ·
    refine ⟨113997736150715231526291905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75998490767143487684194603 113997736150715231526291905)
    ·
      refine ⟨85498302113036423644718929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113997736150715231526291905 85498302113036423644718929)
      ·
        refine ⟨64123726584777317733539197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85498302113036423644718929 64123726584777317733539197)
        ·
          refine ⟨24046397469291494150077199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64123726584777317733539197 24046397469291494150077199)
          ·
            refine ⟨36069596203937241225115799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24046397469291494150077199 36069596203937241225115799)
            ·
              refine ⟨54104394305905861837673699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36069596203937241225115799 54104394305905861837673699)
              ·
                refine ⟨81156591458858792756510549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54104394305905861837673699 81156591458858792756510549)
                ·
                  refine ⟨475526903079250738807679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81156591458858792756510549 475526903079250738807679)
                  ·
                    rfl

theorem cell22_4167384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_4167384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167384 prefixEnd_4167384 := by exact prefixLift 4167384
  have htrace : WordTrace (prefixWord ++ tailWord_4167384) baseStart_4167384 baseEnd_4167384 := by
    simpa [prefixWord, tailWord_4167384, baseEnd_4167384] using wordTrace_append hprefix tailTrace_4167384
  have hstable : (prefixWord ++ tailWord_4167384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167384).length < 2 ^ (prefixWord ++ tailWord_4167384).sum := by decide
  have hdescent : baseEnd_4167384 < baseStart_4167384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167405 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_4167405 : Nat := 118140960795 + 4167405 * 2 ^ 59
def prefixEnd_4167405 : Nat := 4983230072969 + 3 ^ 40 * 4167405 * 2
def baseEnd_4167405 : Nat := 1426587897966915161647973

theorem tailTrace_4167405 : CollatzResearch.WordTrace tailWord_4167405 prefixEnd_4167405 1426587897966915161647973 := by
  unfold tailWord_4167405
  simp only [CollatzResearch.WordTrace]
  refine ⟨151997747467210895954903669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101331831644807263969935779 151997747467210895954903669)
  ·
    refine ⟨14249788825051021495772219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151997747467210895954903669 14249788825051021495772219)
    ·
      refine ⟨21374683237576532243658329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249788825051021495772219 21374683237576532243658329)
      ·
        refine ⟨16031012428182399182743747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21374683237576532243658329 16031012428182399182743747)
        ·
          refine ⟨24046518642273598774115621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16031012428182399182743747 24046518642273598774115621)
          ·
            refine ⟨4508722245426299770146679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24046518642273598774115621 4508722245426299770146679)
            ·
              refine ⟨6763083368139449655220019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508722245426299770146679 6763083368139449655220019)
              ·
                refine ⟨10144625052209174482830029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763083368139449655220019 10144625052209174482830029)
                ·
                  refine ⟨3804234394578440431061261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10144625052209174482830029 3804234394578440431061261)
                  ·
                    refine ⟨1426587897966915161647973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804234394578440431061261 1426587897966915161647973)
                    ·
                      rfl

theorem cell22_4167405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_4167405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167405 prefixEnd_4167405 := by exact prefixLift 4167405
  have htrace : WordTrace (prefixWord ++ tailWord_4167405) baseStart_4167405 baseEnd_4167405 := by
    simpa [prefixWord, tailWord_4167405, baseEnd_4167405] using wordTrace_append hprefix tailTrace_4167405
  have hstable : (prefixWord ++ tailWord_4167405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167405).length < 2 ^ (prefixWord ++ tailWord_4167405).sum := by decide
  have hdescent : baseEnd_4167405 < baseStart_4167405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167542 : List Nat := [5, 1, 1, 3, 2, 2, 2, 6]
def baseStart_4167542 : Nat := 118140960795 + 4167542 * 2 ^ 59
def prefixEnd_4167542 : Nat := 4983230072969 + 3 ^ 40 * 4167542 * 2
def baseEnd_4167542 : Nat := 158514977318521385663617

theorem tailTrace_4167542 : CollatzResearch.WordTrace tailWord_4167542 prefixEnd_4167542 158514977318521385663617 := by
  unfold tailWord_4167542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9500171516732160522040055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101335162845143045568427253 9500171516732160522040055)
  ·
    refine ⟨14250257275098240783060083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9500171516732160522040055 14250257275098240783060083)
    ·
      refine ⟨21375385912647361174590125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14250257275098240783060083 21375385912647361174590125)
      ·
        refine ⟨8015769717242760440471297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21375385912647361174590125 8015769717242760440471297)
        ·
          refine ⟨6011827287932070330353473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8015769717242760440471297 6011827287932070330353473)
          ·
            refine ⟨4508870465949052747765105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011827287932070330353473 4508870465949052747765105)
            ·
              refine ⟨3381652849461789560823829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508870465949052747765105 3381652849461789560823829)
              ·
                refine ⟨158514977318521385663617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3381652849461789560823829 158514977318521385663617)
                ·
                  rfl

theorem cell22_4167542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_4167542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167542 prefixEnd_4167542 := by exact prefixLift 4167542
  have htrace : WordTrace (prefixWord ++ tailWord_4167542) baseStart_4167542 baseEnd_4167542 := by
    simpa [prefixWord, tailWord_4167542, baseEnd_4167542] using wordTrace_append hprefix tailTrace_4167542
  have hstable : (prefixWord ++ tailWord_4167542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167542).length < 2 ^ (prefixWord ++ tailWord_4167542).sum := by decide
  have hdescent : baseEnd_4167542 < baseStart_4167542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167613 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4167613 : Nat := 118140960795 + 4167613 * 2 ^ 59
def prefixEnd_4167613 : Nat := 4983230072969 + 3 ^ 40 * 4167613 * 2
def baseEnd_4167613 : Nat := 1426659100617671952447335

theorem tailTrace_4167613 : CollatzResearch.WordTrace tailWord_4167613 prefixEnd_4167613 1426659100617671952447335 := by
  unfold tailWord_4167613
  simp only [CollatzResearch.WordTrace]
  refine ⟨152005333850457347478475493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101336889233638231652316995 152005333850457347478475493)
  ·
    refine ⟨28501000096960752652214155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152005333850457347478475493 28501000096960752652214155)
    ·
      refine ⟨42751500145441128978321233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28501000096960752652214155 42751500145441128978321233)
      ·
        refine ⟨32063625109080846733740925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42751500145441128978321233 32063625109080846733740925)
        ·
          refine ⟨12023859415905317525152847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32063625109080846733740925 12023859415905317525152847)
          ·
            refine ⟨18035789123857976287729271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12023859415905317525152847 18035789123857976287729271)
            ·
              refine ⟨27053683685786964431593907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18035789123857976287729271 27053683685786964431593907)
              ·
                refine ⟨40580525528680446647390861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27053683685786964431593907 40580525528680446647390861)
                ·
                  refine ⟨15217697073255167492771573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40580525528680446647390861 15217697073255167492771573)
                  ·
                    refine ⟨1426659100617671952447335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15217697073255167492771573 1426659100617671952447335)
                    ·
                      rfl

theorem cell22_4167613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4167613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167613 prefixEnd_4167613 := by exact prefixLift 4167613
  have htrace : WordTrace (prefixWord ++ tailWord_4167613) baseStart_4167613 baseEnd_4167613 := by
    simpa [prefixWord, tailWord_4167613, baseEnd_4167613] using wordTrace_append hprefix tailTrace_4167613
  have hstable : (prefixWord ++ tailWord_4167613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167613).length < 2 ^ (prefixWord ++ tailWord_4167613).sum := by decide
  have hdescent : baseEnd_4167613 < baseStart_4167613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167662 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_4167662 : Nat := 118140960795 + 4167662 * 2 ^ 59
def prefixEnd_4167662 : Nat := 4983230072969 + 3 ^ 40 * 4167662 * 2
def baseEnd_4167662 : Nat := 1426675874319052157972185

theorem tailTrace_4167662 : CollatzResearch.WordTrace tailWord_4167662 prefixEnd_4167662 1426675874319052157972185 := by
  unfold tailWord_4167662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19000890128409978605876155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101338080684853219231339493 19000890128409978605876155)
  ·
    refine ⟨28501335192614967908814233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19000890128409978605876155 28501335192614967908814233)
    ·
      refine ⟨21376001394461225931610675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28501335192614967908814233 21376001394461225931610675)
      ·
        refine ⟨32064002091691838897416013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21376001394461225931610675 32064002091691838897416013)
        ·
          refine ⟨12024000784384439586531005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32064002091691838897416013 12024000784384439586531005)
          ·
            refine ⟨4509000294144164844949127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12024000784384439586531005 4509000294144164844949127)
            ·
              refine ⟨6763500441216247267423691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509000294144164844949127 6763500441216247267423691)
              ·
                refine ⟨10145250661824370901135537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763500441216247267423691 10145250661824370901135537)
                ·
                  refine ⟨7608937996368278175851653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10145250661824370901135537 7608937996368278175851653)
                  ·
                    refine ⟨1426675874319052157972185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608937996368278175851653 1426675874319052157972185)
                    ·
                      rfl

theorem cell22_4167662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_4167662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167662 prefixEnd_4167662 := by exact prefixLift 4167662
  have htrace : WordTrace (prefixWord ++ tailWord_4167662) baseStart_4167662 baseEnd_4167662 := by
    simpa [prefixWord, tailWord_4167662, baseEnd_4167662] using wordTrace_append hprefix tailTrace_4167662
  have hstable : (prefixWord ++ tailWord_4167662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167662).length < 2 ^ (prefixWord ++ tailWord_4167662).sum := by decide
  have hdescent : baseEnd_4167662 < baseStart_4167662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167688 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_4167688 : Nat := 118140960795 + 4167688 * 2 ^ 59
def prefixEnd_4167688 : Nat := 4983230072969 + 3 ^ 40 * 4167688 * 2
def baseEnd_4167688 : Nat := 475561591550132252274035

theorem tailTrace_4167688 : CollatzResearch.WordTrace tailWord_4167688 prefixEnd_4167688 475561591550132252274035 := by
  unfold tailWord_4167688
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004034662592817643727859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101338712883457090191637145 76004034662592817643727859)
  ·
    refine ⟨114006051993889226465591789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76004034662592817643727859 114006051993889226465591789)
    ·
      refine ⟨42752269497708459924596921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114006051993889226465591789 42752269497708459924596921)
      ·
        refine ⟨32064202123281344943447691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42752269497708459924596921 32064202123281344943447691)
        ·
          refine ⟨48096303184922017415171537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32064202123281344943447691 48096303184922017415171537)
          ·
            refine ⟨36072227388691513061378653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48096303184922017415171537 36072227388691513061378653)
            ·
              refine ⟨13527085270759317398016995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36072227388691513061378653 13527085270759317398016995)
              ·
                refine ⟨20290627906138976097025493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13527085270759317398016995 20290627906138976097025493)
                ·
                  refine ⟨475561591550132252274035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20290627906138976097025493 475561591550132252274035)
                  ·
                    rfl

theorem cell22_4167688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_4167688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167688 prefixEnd_4167688 := by exact prefixLift 4167688
  have htrace : WordTrace (prefixWord ++ tailWord_4167688) baseStart_4167688 baseEnd_4167688 := by
    simpa [prefixWord, tailWord_4167688, baseEnd_4167688] using wordTrace_append hprefix tailTrace_4167688
  have hstable : (prefixWord ++ tailWord_4167688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167688).length < 2 ^ (prefixWord ++ tailWord_4167688).sum := by decide
  have hdescent : baseEnd_4167688 < baseStart_4167688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167692 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_4167692 : Nat := 118140960795 + 4167692 * 2 ^ 59
def prefixEnd_4167692 : Nat := 4983230072969 + 3 ^ 40 * 4167692 * 2
def baseEnd_4167692 : Nat := 1426686143932142079722093

theorem tailTrace_4167692 : CollatzResearch.WordTrace tailWord_4167692 prefixEnd_4167692 1426686143932142079722093 := by
  unfold tailWord_4167692
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004107608585571985300665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101338810144780762647067553 76004107608585571985300665)
  ·
    refine ⟨57003080706439178988975499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76004107608585571985300665 57003080706439178988975499)
    ·
      refine ⟨85504621059658768483463249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57003080706439178988975499 85504621059658768483463249)
      ·
        refine ⟨64128465794744076362597437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85504621059658768483463249 64128465794744076362597437)
        ·
          refine ⟨24048174673029028635974039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64128465794744076362597437 24048174673029028635974039)
          ·
            refine ⟨36072262009543542953961059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24048174673029028635974039 36072262009543542953961059)
            ·
              refine ⟨54108393014315314430941589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36072262009543542953961059 54108393014315314430941589)
              ·
                refine ⟨2536330922546030363950387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54108393014315314430941589 2536330922546030363950387)
                ·
                  refine ⟨3804496383819045545925581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536330922546030363950387 3804496383819045545925581)
                  ·
                    refine ⟨1426686143932142079722093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804496383819045545925581 1426686143932142079722093)
                    ·
                      rfl

theorem cell22_4167692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_4167692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167692 prefixEnd_4167692 := by exact prefixLift 4167692
  have htrace : WordTrace (prefixWord ++ tailWord_4167692) baseStart_4167692 baseEnd_4167692 := by
    simpa [prefixWord, tailWord_4167692, baseEnd_4167692] using wordTrace_append hprefix tailTrace_4167692
  have hstable : (prefixWord ++ tailWord_4167692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167692).length < 2 ^ (prefixWord ++ tailWord_4167692).sum := by decide
  have hdescent : baseEnd_4167692 < baseStart_4167692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167726 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4167726 : Nat := 118140960795 + 4167726 * 2 ^ 59
def prefixEnd_4167726 : Nat := 4983230072969 + 3 ^ 40 * 4167726 * 2
def baseEnd_4167726 : Nat := 1426697782826977324371989

theorem tailTrace_4167726 : CollatzResearch.WordTrace tailWord_4167726 prefixEnd_4167726 1426697782826977324371989 := by
  unfold tailWord_4167726
  simp only [CollatzResearch.WordTrace]
  refine ⟨19001181912380995972167379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101339636866031978518226021 19001181912380995972167379)
  ·
    refine ⟨28501772868571493958251069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19001181912380995972167379 28501772868571493958251069)
    ·
      refine ⟨10688164825714310234344151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28501772868571493958251069 10688164825714310234344151)
      ·
        refine ⟨16032247238571465351516227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688164825714310234344151 16032247238571465351516227)
        ·
          refine ⟨24048370857857198027274341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032247238571465351516227 24048370857857198027274341)
          ·
            refine ⟨4509069535848224630113939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24048370857857198027274341 4509069535848224630113939)
            ·
              refine ⟨6763604303772336945170909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509069535848224630113939 6763604303772336945170909)
              ·
                refine ⟨2536351613914626354439091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6763604303772336945170909 2536351613914626354439091)
                ·
                  refine ⟨3804527420871939531658637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536351613914626354439091 3804527420871939531658637)
                  ·
                    refine ⟨1426697782826977324371989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804527420871939531658637 1426697782826977324371989)
                    ·
                      rfl

theorem cell22_4167726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4167726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167726 prefixEnd_4167726 := by exact prefixLift 4167726
  have htrace : WordTrace (prefixWord ++ tailWord_4167726) baseStart_4167726 baseEnd_4167726 := by
    simpa [prefixWord, tailWord_4167726, baseEnd_4167726] using wordTrace_append hprefix tailTrace_4167726
  have hstable : (prefixWord ++ tailWord_4167726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167726).length < 2 ^ (prefixWord ++ tailWord_4167726).sum := by decide
  have hdescent : baseEnd_4167726 < baseStart_4167726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167733 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 8]
def baseStart_4167733 : Nat := 118140960795 + 4167733 * 2 ^ 59
def prefixEnd_4167733 : Nat := 4983230072969 + 3 ^ 40 * 4167733 * 2
def baseEnd_4167733 : Nat := 475566726356677213148989

theorem tailTrace_4167733 : CollatzResearch.WordTrace tailWord_4167733 prefixEnd_4167733 475566726356677213148989 := by
  unfold tailWord_4167733
  simp only [CollatzResearch.WordTrace]
  refine ⟨152009710610022607972843853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101339807073348405315229235 152009710610022607972843853)
  ·
    refine ⟨57003641478758477989816445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152009710610022607972843853 57003641478758477989816445)
    ·
      refine ⟨21376365554534429246181167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57003641478758477989816445 21376365554534429246181167)
      ·
        refine ⟨32064548331801643869271751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21376365554534429246181167 32064548331801643869271751)
        ·
          refine ⟨48096822497702465803907627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32064548331801643869271751 48096822497702465803907627)
          ·
            refine ⟨72145233746553698705861441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48096822497702465803907627 72145233746553698705861441)
            ·
              refine ⟨54108925309915274029396081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72145233746553698705861441 54108925309915274029396081)
              ·
                refine ⟨40581693982436455522047061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54108925309915274029396081 40581693982436455522047061)
                ·
                  refine ⟨475566726356677213148989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40581693982436455522047061 475566726356677213148989)
                  ·
                    rfl

theorem cell22_4167733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_4167733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167733 prefixEnd_4167733 := by exact prefixLift 4167733
  have htrace : WordTrace (prefixWord ++ tailWord_4167733) baseStart_4167733 baseEnd_4167733 := by
    simpa [prefixWord, tailWord_4167733, baseEnd_4167733] using wordTrace_append hprefix tailTrace_4167733
  have hstable : (prefixWord ++ tailWord_4167733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167733).length < 2 ^ (prefixWord ++ tailWord_4167733).sum := by decide
  have hdescent : baseEnd_4167733 < baseStart_4167733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167735 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 1, 4]
def baseStart_4167735 : Nat := 118140960795 + 4167735 * 2 ^ 59
def prefixEnd_4167735 : Nat := 4983230072969 + 3 ^ 40 * 4167735 * 2
def baseEnd_4167735 : Nat := 1426700863710904300896961

theorem tailTrace_4167735 : CollatzResearch.WordTrace tailWord_4167735 prefixEnd_4167735 1426700863710904300896961 := by
  unfold tailWord_4167735
  simp only [CollatzResearch.WordTrace]
  refine ⟨152009783556015362314416659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101339855704010241542944439 152009783556015362314416659)
  ·
    refine ⟨228014675334023043471624989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152009783556015362314416659 228014675334023043471624989)
    ·
      refine ⟨85505503250258641301859371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228014675334023043471624989 85505503250258641301859371)
      ·
        refine ⟨128258254875387961952789057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85505503250258641301859371 128258254875387961952789057)
        ·
          refine ⟨96193691156540971464591793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128258254875387961952789057 96193691156540971464591793)
          ·
            refine ⟨72145268367405728598443845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96193691156540971464591793 72145268367405728598443845)
            ·
              refine ⟨13527237818888574112208221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72145268367405728598443845 13527237818888574112208221)
              ·
                refine ⟨5072714182083215292078083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13527237818888574112208221 5072714182083215292078083)
                ·
                  refine ⟨7609071273124822938117125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072714182083215292078083 7609071273124822938117125)
                  ·
                    refine ⟨1426700863710904300896961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609071273124822938117125 1426700863710904300896961)
                    ·
                      rfl

theorem cell22_4167735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_4167735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167735 prefixEnd_4167735 := by exact prefixLift 4167735
  have htrace : WordTrace (prefixWord ++ tailWord_4167735) baseStart_4167735 baseEnd_4167735 := by
    simpa [prefixWord, tailWord_4167735, baseEnd_4167735] using wordTrace_append hprefix tailTrace_4167735
  have hstable : (prefixWord ++ tailWord_4167735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167735).length < 2 ^ (prefixWord ++ tailWord_4167735).sum := by decide
  have hdescent : baseEnd_4167735 < baseStart_4167735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167780 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_4167780 : Nat := 118140960795 + 4167780 * 2 ^ 59
def prefixEnd_4167780 : Nat := 4983230072969 + 3 ^ 40 * 4167780 * 2
def baseEnd_4167780 : Nat := 1426716268130539183521823

theorem tailTrace_4167780 : CollatzResearch.WordTrace tailWord_4167780 prefixEnd_4167780 1426716268130539183521823 := by
  unfold tailWord_4167780
  simp only [CollatzResearch.WordTrace]
  refine ⟨76005712420426167499902397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101340949893901556666536529 76005712420426167499902397)
  ·
    refine ⟨28502142157659812812463399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76005712420426167499902397 28502142157659812812463399)
    ·
      refine ⟨42753213236489719218695099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28502142157659812812463399 42753213236489719218695099)
      ·
        refine ⟨64129819854734578828042649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42753213236489719218695099 64129819854734578828042649)
        ·
          refine ⟨48097364891050934121031987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64129819854734578828042649 48097364891050934121031987)
          ·
            refine ⟨72146047336576401181547981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48097364891050934121031987 72146047336576401181547981)
            ·
              refine ⟨27054767751216150443080493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72146047336576401181547981 27054767751216150443080493)
              ·
                refine ⟨10145537906706056416155185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27054767751216150443080493 10145537906706056416155185)
                ·
                  refine ⟨7609153430029542312116389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10145537906706056416155185 7609153430029542312116389)
                  ·
                    refine ⟨1426716268130539183521823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609153430029542312116389 1426716268130539183521823)
                    ·
                      rfl

theorem cell22_4167780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_4167780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167780 prefixEnd_4167780 := by exact prefixLift 4167780
  have htrace : WordTrace (prefixWord ++ tailWord_4167780) baseStart_4167780 baseEnd_4167780 := by
    simpa [prefixWord, tailWord_4167780, baseEnd_4167780] using wordTrace_append hprefix tailTrace_4167780
  have hstable : (prefixWord ++ tailWord_4167780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167780).length < 2 ^ (prefixWord ++ tailWord_4167780).sum := by decide
  have hdescent : baseEnd_4167780 < baseStart_4167780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167857 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 7]
def baseStart_4167857 : Nat := 118140960795 + 4167857 * 2 ^ 59
def prefixEnd_4167857 : Nat := 4983230072969 + 3 ^ 40 * 4167857 * 2
def baseEnd_4167857 : Nat := 475580875601378883115529

theorem tailTrace_4167857 : CollatzResearch.WordTrace tailWord_4167857 prefixEnd_4167857 475580875601378883115529 := by
  unfold tailWord_4167857
  simp only [CollatzResearch.WordTrace]
  refine ⟨152014233261573377150357825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101342822174382251433571883 152014233261573377150357825)
  ·
    refine ⟨114010674946180032862768369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152014233261573377150357825 114010674946180032862768369)
    ·
      refine ⟨85508006209635024647076277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114010674946180032862768369 85508006209635024647076277)
      ·
        refine ⟨8016375582153283560663401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85508006209635024647076277 8016375582153283560663401)
        ·
          refine ⟨6012281686614962670497551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8016375582153283560663401 6012281686614962670497551)
          ·
            refine ⟨9018422529922444005746327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012281686614962670497551 9018422529922444005746327)
            ·
              refine ⟨13527633794883666008619491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9018422529922444005746327 13527633794883666008619491)
              ·
                refine ⟨20291450692325499012929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13527633794883666008619491 20291450692325499012929237)
                ·
                  refine ⟨475580875601378883115529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20291450692325499012929237 475580875601378883115529)
                  ·
                    rfl

theorem cell22_4167857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_4167857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167857 prefixEnd_4167857 := by exact prefixLift 4167857
  have htrace : WordTrace (prefixWord ++ tailWord_4167857) baseStart_4167857 baseEnd_4167857 := by
    simpa [prefixWord, tailWord_4167857, baseEnd_4167857] using wordTrace_append hprefix tailTrace_4167857
  have hstable : (prefixWord ++ tailWord_4167857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167857).length < 2 ^ (prefixWord ++ tailWord_4167857).sum := by decide
  have hdescent : baseEnd_4167857 < baseStart_4167857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167861 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_4167861 : Nat := 118140960795 + 4167861 * 2 ^ 59
def prefixEnd_4167861 : Nat := 4983230072969 + 3 ^ 40 * 4167861 * 2
def baseEnd_4167861 : Nat := 1426743996085881972246575

theorem tailTrace_4167861 : CollatzResearch.WordTrace tailWord_4167861 prefixEnd_4167861 1426743996085881972246575 := by
  unfold tailWord_4167861
  simp only [CollatzResearch.WordTrace]
  refine ⟨152014379153558885833503437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101342919435705923889002291 152014379153558885833503437)
  ·
    refine ⟨57005392182584582187563789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152014379153558885833503437 57005392182584582187563789)
    ·
      refine ⟨21377022068469218320336421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57005392182584582187563789 21377022068469218320336421)
      ·
        refine ⟨4008191637837978435063079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21377022068469218320336421 4008191637837978435063079)
        ·
          refine ⟨6012287456756967652594619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008191637837978435063079 6012287456756967652594619)
          ·
            refine ⟨9018431185135451478891929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012287456756967652594619 9018431185135451478891929)
            ·
              refine ⟨6763823388851588609168947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018431185135451478891929 6763823388851588609168947)
              ·
                refine ⟨10145735083277382913753421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763823388851588609168947 10145735083277382913753421)
                ·
                  refine ⟨3804650656229018592657533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10145735083277382913753421 3804650656229018592657533)
                  ·
                    refine ⟨1426743996085881972246575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804650656229018592657533 1426743996085881972246575)
                    ·
                      rfl

theorem cell22_4167861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_4167861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167861 prefixEnd_4167861 := by exact prefixLift 4167861
  have htrace : WordTrace (prefixWord ++ tailWord_4167861) baseStart_4167861 baseEnd_4167861 := by
    simpa [prefixWord, tailWord_4167861, baseEnd_4167861] using wordTrace_append hprefix tailTrace_4167861
  have hstable : (prefixWord ++ tailWord_4167861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167861).length < 2 ^ (prefixWord ++ tailWord_4167861).sum := by decide
  have hdescent : baseEnd_4167861 < baseStart_4167861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167887 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 1, 4]
def baseStart_4167887 : Nat := 118140960795 + 4167887 * 2 ^ 59
def prefixEnd_4167887 : Nat := 4983230072969 + 3 ^ 40 * 4167887 * 2
def baseEnd_4167887 : Nat := 1426752896417226571096495

theorem tailTrace_4167887 : CollatzResearch.WordTrace tailWord_4167887 prefixEnd_4167887 1426752896417226571096495 := by
  unfold tailWord_4167887
  simp only [CollatzResearch.WordTrace]
  refine ⟨152015327451464692273949915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101343551634309794849299943 152015327451464692273949915)
  ·
    refine ⟨228022991177197038410924873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152015327451464692273949915 228022991177197038410924873)
    ·
      refine ⟨171017243382897778808193655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228022991177197038410924873 171017243382897778808193655)
      ·
        refine ⟨256525865074346668212290483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171017243382897778808193655 256525865074346668212290483)
        ·
          refine ⟨384788797611520002318435725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256525865074346668212290483 384788797611520002318435725)
          ·
            refine ⟨144295799104320000869413397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384788797611520002318435725 144295799104320000869413397)
            ·
              refine ⟨6763865583015000040753753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144295799104320000869413397 6763865583015000040753753)
              ·
                refine ⟨5072899187261250030565315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6763865583015000040753753 5072899187261250030565315)
                ·
                  refine ⟨7609348780891875045847973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072899187261250030565315 7609348780891875045847973)
                  ·
                    refine ⟨1426752896417226571096495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609348780891875045847973 1426752896417226571096495)
                    ·
                      rfl

theorem cell22_4167887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_4167887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167887 prefixEnd_4167887 := by exact prefixLift 4167887
  have htrace : WordTrace (prefixWord ++ tailWord_4167887) baseStart_4167887 baseEnd_4167887 := by
    simpa [prefixWord, tailWord_4167887, baseEnd_4167887] using wordTrace_append hprefix tailTrace_4167887
  have hstable : (prefixWord ++ tailWord_4167887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167887).length < 2 ^ (prefixWord ++ tailWord_4167887).sum := by decide
  have hdescent : baseEnd_4167887 < baseStart_4167887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167930 : List Nat := [3, 1, 1, 1, 1, 5, 1, 9]
def baseStart_4167930 : Nat := 118140960795 + 4167930 * 2 ^ 59
def prefixEnd_4167930 : Nat := 4983230072969 + 3 ^ 40 * 4167930 * 2
def baseEnd_4167930 : Nat := 158529735132887643585707

theorem tailTrace_4167930 : CollatzResearch.WordTrace tailWord_4167930 prefixEnd_4167930 158529735132887643585707 := by
  unfold tailWord_4167930
  simp only [CollatzResearch.WordTrace]
  refine ⟨38004223947577227654441311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101344597193539273745176829 38004223947577227654441311)
  ·
    refine ⟨57006335921365841481661967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38004223947577227654441311 57006335921365841481661967)
    ·
      refine ⟨85509503882048762222492951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57006335921365841481661967 85509503882048762222492951)
      ·
        refine ⟨128264255823073143333739427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85509503882048762222492951 128264255823073143333739427)
        ·
          refine ⟨192396383734609715000609141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128264255823073143333739427 192396383734609715000609141)
          ·
            refine ⟨18037160975119660781307107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192396383734609715000609141 18037160975119660781307107)
            ·
              refine ⟨27055741462679491171960661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18037160975119660781307107 27055741462679491171960661)
              ·
                refine ⟨158529735132887643585707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27055741462679491171960661 158529735132887643585707)
                ·
                  rfl

theorem cell22_4167930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_4167930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167930 prefixEnd_4167930 := by exact prefixLift 4167930
  have htrace : WordTrace (prefixWord ++ tailWord_4167930) baseStart_4167930 baseEnd_4167930 := by
    simpa [prefixWord, tailWord_4167930, baseEnd_4167930] using wordTrace_append hprefix tailTrace_4167930
  have hstable : (prefixWord ++ tailWord_4167930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167930).length < 2 ^ (prefixWord ++ tailWord_4167930).sum := by decide
  have hdescent : baseEnd_4167930 < baseStart_4167930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167966 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4167966 : Nat := 118140960795 + 4167966 * 2 ^ 59
def prefixEnd_4167966 : Nat := 4983230072969 + 3 ^ 40 * 4167966 * 2
def baseEnd_4167966 : Nat := 1426779939731696698371253

theorem tailTrace_4167966 : CollatzResearch.WordTrace tailWord_4167966 prefixEnd_4167966 1426779939731696698371253 := by
  unfold tailWord_4167966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002276102272311095759469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101345472545452325844050501 19002276102272311095759469)
  ·
    refine ⟨7125853538352116660909801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19002276102272311095759469 7125853538352116660909801)
    ·
      refine ⟨5344390153764087495682351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7125853538352116660909801 5344390153764087495682351)
      ·
        refine ⟨8016585230646131243523527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5344390153764087495682351 8016585230646131243523527)
        ·
          refine ⟨12024877845969196865285291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016585230646131243523527 12024877845969196865285291)
          ·
            refine ⟨18037316768953795297927937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024877845969196865285291 18037316768953795297927937)
            ·
              refine ⟨13527987576715346473445953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18037316768953795297927937 13527987576715346473445953)
              ·
                refine ⟨10145990682536509855084465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13527987576715346473445953 10145990682536509855084465)
                ·
                  refine ⟨7609493011902382391313349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10145990682536509855084465 7609493011902382391313349)
                  ·
                    refine ⟨1426779939731696698371253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609493011902382391313349 1426779939731696698371253)
                    ·
                      rfl

theorem cell22_4167966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4167966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167966 prefixEnd_4167966 := by exact prefixLift 4167966
  have htrace : WordTrace (prefixWord ++ tailWord_4167966) baseStart_4167966 baseEnd_4167966 := by
    simpa [prefixWord, tailWord_4167966, baseEnd_4167966] using wordTrace_append hprefix tailTrace_4167966
  have hstable : (prefixWord ++ tailWord_4167966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167966).length < 2 ^ (prefixWord ++ tailWord_4167966).sum := by decide
  have hdescent : baseEnd_4167966 < baseStart_4167966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167981 : List Nat := [1, 5, 3, 1, 2, 2, 1, 7]
def baseStart_4167981 : Nat := 118140960795 + 4167981 * 2 ^ 59
def prefixEnd_4167981 : Nat := 4983230072969 + 3 ^ 40 * 4167981 * 2
def baseEnd_4167981 : Nat := 158531674948693517694023

theorem tailTrace_4167981 : CollatzResearch.WordTrace tailWord_4167981 prefixEnd_4167981 158531674948693517694023 := by
  unfold tailWord_4167981
  simp only [CollatzResearch.WordTrace]
  refine ⟨152018755913124146327871797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101345837275416097551914531 152018755913124146327871797)
  ·
    refine ⟨14251758366855388718237981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152018755913124146327871797 14251758366855388718237981)
    ·
      refine ⟨5344409387570770769339243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14251758366855388718237981 5344409387570770769339243)
      ·
        refine ⟨8016614081356156154008865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5344409387570770769339243 8016614081356156154008865)
        ·
          refine ⟨6012460561017117115506649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8016614081356156154008865 6012460561017117115506649)
          ·
            refine ⟨4509345420762837836629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012460561017117115506649 4509345420762837836629987)
            ·
              refine ⟨6764018131144256754944981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509345420762837836629987 6764018131144256754944981)
              ·
                refine ⟨158531674948693517694023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6764018131144256754944981 158531674948693517694023)
                ·
                  rfl

theorem cell22_4167981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 7].length) (baseStart_4167981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167981 prefixEnd_4167981 := by exact prefixLift 4167981
  have htrace : WordTrace (prefixWord ++ tailWord_4167981) baseStart_4167981 baseEnd_4167981 := by
    simpa [prefixWord, tailWord_4167981, baseEnd_4167981] using wordTrace_append hprefix tailTrace_4167981
  have hstable : (prefixWord ++ tailWord_4167981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167981).length < 2 ^ (prefixWord ++ tailWord_4167981).sum := by decide
  have hdescent : baseEnd_4167981 < baseStart_4167981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167992 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_4167992 : Nat := 118140960795 + 4167992 * 2 ^ 59
def prefixEnd_4167992 : Nat := 4983230072969 + 3 ^ 40 * 4167992 * 2
def baseEnd_4167992 : Nat := 475596280021013765740391

theorem tailTrace_4167992 : CollatzResearch.WordTrace tailWord_4167992 prefixEnd_4167992 475596280021013765740391 := by
  unfold tailWord_4167992
  simp only [CollatzResearch.WordTrace]
  refine ⟨76009578558042147603261115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101346104744056196804348153 76009578558042147603261115)
  ·
    refine ⟨114014367837063221404891673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76009578558042147603261115 114014367837063221404891673)
    ·
      refine ⟨85510775877797416053668755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114014367837063221404891673 85510775877797416053668755)
      ·
        refine ⟨128266163816696124080503133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85510775877797416053668755 128266163816696124080503133)
        ·
          refine ⟨48099811431261046530188675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128266163816696124080503133 48099811431261046530188675)
          ·
            refine ⟨72149717146891569795283013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48099811431261046530188675 72149717146891569795283013)
            ·
              refine ⟨13528071965042169336615565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72149717146891569795283013 13528071965042169336615565)
              ·
                refine ⟨5073026986890813501230837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13528071965042169336615565 5073026986890813501230837)
                ·
                  refine ⟨475596280021013765740391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5073026986890813501230837 475596280021013765740391)
                  ·
                    rfl

theorem cell22_4167992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_4167992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4167992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4167992 prefixEnd_4167992 := by exact prefixLift 4167992
  have htrace : WordTrace (prefixWord ++ tailWord_4167992) baseStart_4167992 baseEnd_4167992 := by
    simpa [prefixWord, tailWord_4167992, baseEnd_4167992] using wordTrace_append hprefix tailTrace_4167992
  have hstable : (prefixWord ++ tailWord_4167992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167992).length < 2 ^ (prefixWord ++ tailWord_4167992).sum := by decide
  have hdescent : baseEnd_4167992 < baseStart_4167992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168037 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 6]
def baseStart_4168037 : Nat := 118140960795 + 4168037 * 2 ^ 59
def prefixEnd_4168037 : Nat := 4983230072969 + 3 ^ 40 * 4168037 * 2
def baseEnd_4168037 : Nat := 475601414827558726615345

theorem tailTrace_4168037 : CollatzResearch.WordTrace tailWord_4168037 prefixEnd_4168037 475601414827558726615345 := by
  unfold tailWord_4168037
  simp only [CollatzResearch.WordTrace]
  refine ⟨152020798400921267891910365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101347198933947511927940243 152020798400921267891910365)
  ·
    refine ⟨57007799400345475459466387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152020798400921267891910365 57007799400345475459466387)
    ·
      refine ⟨85511699100518213189199581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57007799400345475459466387 85511699100518213189199581)
      ·
        refine ⟨32066887162694329945949843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85511699100518213189199581 32066887162694329945949843)
        ·
          refine ⟨48100330744041494918924765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32066887162694329945949843 48100330744041494918924765)
          ·
            refine ⟨18037624029015560594596787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48100330744041494918924765 18037624029015560594596787)
            ·
              refine ⟨27056436043523340891895181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18037624029015560594596787 27056436043523340891895181)
              ·
                refine ⟨10146163516321252834460693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27056436043523340891895181 10146163516321252834460693)
                ·
                  refine ⟨475601414827558726615345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10146163516321252834460693 475601414827558726615345)
                  ·
                    rfl

theorem cell22_4168037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_4168037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168037 prefixEnd_4168037 := by exact prefixLift 4168037
  have htrace : WordTrace (prefixWord ++ tailWord_4168037) baseStart_4168037 baseEnd_4168037 := by
    simpa [prefixWord, tailWord_4168037, baseEnd_4168037] using wordTrace_append hprefix tailTrace_4168037
  have hstable : (prefixWord ++ tailWord_4168037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168037).length < 2 ^ (prefixWord ++ tailWord_4168037).sum := by decide
  have hdescent : baseEnd_4168037 < baseStart_4168037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168088 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 4]
def baseStart_4168088 : Nat := 118140960795 + 4168088 * 2 ^ 59
def prefixEnd_4168088 : Nat := 4983230072969 + 3 ^ 40 * 4168088 * 2
def baseEnd_4168088 : Nat := 475607234274976348940293

theorem tailTrace_4168088 : CollatzResearch.WordTrace tailWord_4168088 prefixEnd_4168088 475607234274976348940293 := by
  unfold tailWord_4168088
  simp only [CollatzResearch.WordTrace]
  refine ⟨76011329261868251801008459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101348439015824335734677945 76011329261868251801008459)
  ·
    refine ⟨114016993892802377701512689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76011329261868251801008459 114016993892802377701512689)
    ·
      refine ⟨85512745419601783276134517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114016993892802377701512689 85512745419601783276134517)
      ·
        refine ⟨8016819883087667182137611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85512745419601783276134517 8016819883087667182137611)
        ·
          refine ⟨12025229824631500773206417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016819883087667182137611 12025229824631500773206417)
          ·
            refine ⟨9018922368473625579904813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12025229824631500773206417 9018922368473625579904813)
            ·
              refine ⟨3382095888177609592464305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9018922368473625579904813 3382095888177609592464305)
              ·
                refine ⟨2536571916133207194348229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382095888177609592464305 2536571916133207194348229)
                ·
                  refine ⟨475607234274976348940293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536571916133207194348229 475607234274976348940293)
                  ·
                    rfl

theorem cell22_4168088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_4168088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168088 prefixEnd_4168088 := by exact prefixLift 4168088
  have htrace : WordTrace (prefixWord ++ tailWord_4168088) baseStart_4168088 baseEnd_4168088 := by
    simpa [prefixWord, tailWord_4168088, baseEnd_4168088] using wordTrace_append hprefix tailTrace_4168088
  have hstable : (prefixWord ++ tailWord_4168088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168088).length < 2 ^ (prefixWord ++ tailWord_4168088).sum := by decide
  have hdescent : baseEnd_4168088 < baseStart_4168088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168103 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 2, 3]
def baseStart_4168103 : Nat := 118140960795 + 4168103 * 2 ^ 59
def prefixEnd_4168103 : Nat := 4983230072969 + 3 ^ 40 * 4168103 * 2
def baseEnd_4168103 : Nat := 1426826837631474007695833

theorem tailTrace_4168103 : CollatzResearch.WordTrace tailWord_4168103 prefixEnd_4168103 1426826837631474007695833 := by
  unfold tailWord_4168103
  simp only [CollatzResearch.WordTrace]
  refine ⟨152023205618682161163812963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101348803745788107442541975 152023205618682161163812963)
  ·
    refine ⟨228034808428023241745719445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152023205618682161163812963 228034808428023241745719445)
    ·
      refine ⟨10689131645063589456830599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228034808428023241745719445 10689131645063589456830599)
      ·
        refine ⟨16033697467595384185245899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10689131645063589456830599 16033697467595384185245899)
        ·
          refine ⟨24050546201393076277868849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16033697467595384185245899 24050546201393076277868849)
          ·
            refine ⟨18037909651044807208401637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24050546201393076277868849 18037909651044807208401637)
            ·
              refine ⟨3382108059570901351575307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18037909651044807208401637 3382108059570901351575307)
              ·
                refine ⟨5073162089356352027362961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382108059570901351575307 5073162089356352027362961)
                ·
                  refine ⟨3804871567017264020522221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5073162089356352027362961 3804871567017264020522221)
                  ·
                    refine ⟨1426826837631474007695833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804871567017264020522221 1426826837631474007695833)
                    ·
                      rfl

theorem cell22_4168103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_4168103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168103 prefixEnd_4168103 := by exact prefixLift 4168103
  have htrace : WordTrace (prefixWord ++ tailWord_4168103) baseStart_4168103 baseEnd_4168103 := by
    simpa [prefixWord, tailWord_4168103, baseEnd_4168103] using wordTrace_append hprefix tailTrace_4168103
  have hstable : (prefixWord ++ tailWord_4168103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168103).length < 2 ^ (prefixWord ++ tailWord_4168103).sum := by decide
  have hdescent : baseEnd_4168103 < baseStart_4168103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168114 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_4168114 : Nat := 118140960795 + 4168114 * 2 ^ 59
def prefixEnd_4168114 : Nat := 4983230072969 + 3 ^ 40 * 4168114 * 2
def baseEnd_4168114 : Nat := 1426830603156273645670799

theorem tailTrace_4168114 : CollatzResearch.WordTrace tailWord_4168114 prefixEnd_4168114 1426830603156273645670799 := by
  unfold tailWord_4168114
  simp only [CollatzResearch.WordTrace]
  refine ⟨38005901705410577510615849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101349071214428206694975597 38005901705410577510615849)
  ·
    refine ⟨28504426279057933132961887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38005901705410577510615849 28504426279057933132961887)
    ·
      refine ⟨42756639418586899699442831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28504426279057933132961887 42756639418586899699442831)
      ·
        refine ⟨64134959127880349549164247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42756639418586899699442831 64134959127880349549164247)
        ·
          refine ⟨96202438691820524323746371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64134959127880349549164247 96202438691820524323746371)
          ·
            refine ⟨144303658037730786485619557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96202438691820524323746371 144303658037730786485619557)
            ·
              refine ⟨27056935882074522466053667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144303658037730786485619557 27056935882074522466053667)
              ·
                refine ⟨40585403823111783699080501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27056935882074522466053667 40585403823111783699080501)
                ·
                  refine ⟨3804881608416729721788797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40585403823111783699080501 3804881608416729721788797)
                  ·
                    refine ⟨1426830603156273645670799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804881608416729721788797 1426830603156273645670799)
                    ·
                      rfl

theorem cell22_4168114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_4168114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168114 prefixEnd_4168114 := by exact prefixLift 4168114
  have htrace : WordTrace (prefixWord ++ tailWord_4168114) baseStart_4168114 baseEnd_4168114 := by
    simpa [prefixWord, tailWord_4168114, baseEnd_4168114] using wordTrace_append hprefix tailTrace_4168114
  have hstable : (prefixWord ++ tailWord_4168114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168114).length < 2 ^ (prefixWord ++ tailWord_4168114).sum := by decide
  have hdescent : baseEnd_4168114 < baseStart_4168114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168131 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 1, 3]
def baseStart_4168131 : Nat := 118140960795 + 4168131 * 2 ^ 59
def prefixEnd_4168131 : Nat := 4983230072969 + 3 ^ 40 * 4168131 * 2
def baseEnd_4168131 : Nat := 1426836422603691267995747

theorem tailTrace_4168131 : CollatzResearch.WordTrace tailWord_4168131 prefixEnd_4168131 1426836422603691267995747 := by
  unfold tailWord_4168131
  simp only [CollatzResearch.WordTrace]
  refine ⟨152024226862580721945832247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101349484575053814630554831 152024226862580721945832247)
  ·
    refine ⟨228036340293871082918748371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152024226862580721945832247 228036340293871082918748371)
    ·
      refine ⟨342054510440806624378122557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228036340293871082918748371 342054510440806624378122557)
      ·
        refine ⟨128270441415302484141795959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342054510440806624378122557 128270441415302484141795959)
        ·
          refine ⟨192405662122953726212693939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128270441415302484141795959 192405662122953726212693939)
          ·
            refine ⟨288608493184430589319040909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192405662122953726212693939 288608493184430589319040909)
            ·
              refine ⟨108228184944161470994640341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288608493184430589319040909 108228184944161470994640341)
              ·
                refine ⟨2536598084628784476436883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108228184944161470994640341 2536598084628784476436883)
                ·
                  refine ⟨3804897126943176714655325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536598084628784476436883 3804897126943176714655325)
                  ·
                    refine ⟨1426836422603691267995747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3804897126943176714655325 1426836422603691267995747)
                    ·
                      rfl

theorem cell22_4168131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 3].length) (baseStart_4168131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168131 prefixEnd_4168131 := by exact prefixLift 4168131
  have htrace : WordTrace (prefixWord ++ tailWord_4168131) baseStart_4168131 baseEnd_4168131 := by
    simpa [prefixWord, tailWord_4168131, baseEnd_4168131] using wordTrace_append hprefix tailTrace_4168131
  have hstable : (prefixWord ++ tailWord_4168131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168131).length < 2 ^ (prefixWord ++ tailWord_4168131).sum := by decide
  have hdescent : baseEnd_4168131 < baseStart_4168131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168159 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 2, 5]
def baseStart_4168159 : Nat := 118140960795 + 4168159 * 2 ^ 59
def prefixEnd_4168159 : Nat := 4983230072969 + 3 ^ 40 * 4168159 * 2
def baseEnd_4168159 : Nat := 1426846007575908528295661

theorem tailTrace_4168159 : CollatzResearch.WordTrace tailWord_4168159 prefixEnd_4168159 1426846007575908528295661 := by
  unfold tailWord_4168159
  simp only [CollatzResearch.WordTrace]
  refine ⟨152025248106479282727851531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101350165404319521818567687 152025248106479282727851531)
  ·
    refine ⟨228037872159718924091777297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152025248106479282727851531 228037872159718924091777297)
    ·
      refine ⟨171028404119789193068832973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228037872159718924091777297 171028404119789193068832973)
      ·
        refine ⟨64135651544920947400812365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171028404119789193068832973 64135651544920947400812365)
        ·
          refine ⟨24050869329345355275304637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64135651544920947400812365 24050869329345355275304637)
          ·
            refine ⟨9019075998504508228239239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24050869329345355275304637 9019075998504508228239239)
            ·
              refine ⟨13528613997756762342358859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019075998504508228239239 13528613997756762342358859)
              ·
                refine ⟨20292920996635143513538289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13528613997756762342358859 20292920996635143513538289)
                ·
                  refine ⟨15219690747476357635153717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20292920996635143513538289 15219690747476357635153717)
                  ·
                    refine ⟨1426846007575908528295661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15219690747476357635153717 1426846007575908528295661)
                    ·
                      rfl

theorem cell22_4168159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_4168159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168159 prefixEnd_4168159 := by exact prefixLift 4168159
  have htrace : WordTrace (prefixWord ++ tailWord_4168159) baseStart_4168159 baseEnd_4168159 := by
    simpa [prefixWord, tailWord_4168159, baseEnd_4168159] using wordTrace_append hprefix tailTrace_4168159
  have hstable : (prefixWord ++ tailWord_4168159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168159).length < 2 ^ (prefixWord ++ tailWord_4168159).sum := by decide
  have hdescent : baseEnd_4168159 < baseStart_4168159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168206 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_4168206 : Nat := 118140960795 + 4168206 * 2 ^ 59
def prefixEnd_4168206 : Nat := 4983230072969 + 3 ^ 40 * 4168206 * 2
def baseEnd_4168206 : Nat := 475620698878805357456839

theorem tailTrace_4168206 : CollatzResearch.WordTrace tailWord_4168206 prefixEnd_4168206 475620698878805357456839 := by
  unfold tailWord_4168206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003370292163626219351559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101351308224872673169874981 19003370292163626219351559)
  ·
    refine ⟨28505055438245439329027339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19003370292163626219351559 28505055438245439329027339)
    ·
      refine ⟨42757583157368158993541009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28505055438245439329027339 42757583157368158993541009)
      ·
        refine ⟨32068187368026119245155757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42757583157368158993541009 32068187368026119245155757)
        ·
          refine ⟨12025570263009794716933409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32068187368026119245155757 12025570263009794716933409)
          ·
            refine ⟨9019177697257346037700057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12025570263009794716933409 9019177697257346037700057)
            ·
              refine ⟨6764383272943009528275043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9019177697257346037700057 6764383272943009528275043)
              ·
                refine ⟨10146574909414514292412565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764383272943009528275043 10146574909414514292412565)
                ·
                  refine ⟨475620698878805357456839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10146574909414514292412565 475620698878805357456839)
                  ·
                    rfl

theorem cell22_4168206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_4168206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168206 prefixEnd_4168206 := by exact prefixLift 4168206
  have htrace : WordTrace (prefixWord ++ tailWord_4168206) baseStart_4168206 baseEnd_4168206 := by
    simpa [prefixWord, tailWord_4168206, baseEnd_4168206] using wordTrace_append hprefix tailTrace_4168206
  have hstable : (prefixWord ++ tailWord_4168206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168206).length < 2 ^ (prefixWord ++ tailWord_4168206).sum := by decide
  have hdescent : baseEnd_4168206 < baseStart_4168206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168221 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4168221 : Nat := 118140960795 + 4168221 * 2 ^ 59
def prefixEnd_4168221 : Nat := 4983230072969 + 3 ^ 40 * 4168221 * 2
def baseEnd_4168221 : Nat := 1426867231442961033245471

theorem tailTrace_4168221 : CollatzResearch.WordTrace tailWord_4168221 prefixEnd_4168221 1426867231442961033245471 := by
  unfold tailWord_4168221
  simp only [CollatzResearch.WordTrace]
  refine ⟨152027509432254667316608517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101351672954836444877739011 152027509432254667316608517)
  ·
    refine ⟨28505158018547750121864097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152027509432254667316608517 28505158018547750121864097)
    ·
      refine ⟨21378868513910812591398073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28505158018547750121864097 21378868513910812591398073)
      ·
        refine ⟨16034151385433109443548555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21378868513910812591398073 16034151385433109443548555)
        ·
          refine ⟨24051227078149664165322833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16034151385433109443548555 24051227078149664165322833)
          ·
            refine ⟨18038420308612248123992125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24051227078149664165322833 18038420308612248123992125)
            ·
              refine ⟨6764407615729593046497047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18038420308612248123992125 6764407615729593046497047)
              ·
                refine ⟨10146611423594389569745571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764407615729593046497047 10146611423594389569745571)
                ·
                  refine ⟨15219917135391584354618357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146611423594389569745571 15219917135391584354618357)
                  ·
                    refine ⟨1426867231442961033245471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15219917135391584354618357 1426867231442961033245471)
                    ·
                      rfl

theorem cell22_4168221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4168221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168221 prefixEnd_4168221 := by exact prefixLift 4168221
  have htrace : WordTrace (prefixWord ++ tailWord_4168221) baseStart_4168221 baseEnd_4168221 := by
    simpa [prefixWord, tailWord_4168221, baseEnd_4168221] using wordTrace_append hprefix tailTrace_4168221
  have hstable : (prefixWord ++ tailWord_4168221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168221).length < 2 ^ (prefixWord ++ tailWord_4168221).sum := by decide
  have hdescent : baseEnd_4168221 < baseStart_4168221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168339 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_4168339 : Nat := 118140960795 + 4168339 * 2 ^ 59
def prefixEnd_4168339 : Nat := 4983230072969 + 3 ^ 40 * 4168339 * 2
def baseEnd_4168339 : Nat := 1426907625254448058795109

theorem tailTrace_4168339 : CollatzResearch.WordTrace tailWord_4168339 prefixEnd_4168339 1426907625254448058795109 := by
  unfold tailWord_4168339
  simp only [CollatzResearch.WordTrace]
  refine ⟨152031813245827173469404071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101354542163884782312936047 152031813245827173469404071)
  ·
    refine ⟨228047719868740760204106107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152031813245827173469404071 228047719868740760204106107)
    ·
      refine ⟨342071579803111140306159161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228047719868740760204106107 342071579803111140306159161)
      ·
        refine ⟨256553684852333355229619371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342071579803111140306159161 256553684852333355229619371)
        ·
          refine ⟨384830527278500032844429057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256553684852333355229619371 384830527278500032844429057)
          ·
            refine ⟨288622895458875024633321793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384830527278500032844429057 288622895458875024633321793)
            ·
              refine ⟨216467171594156268474991345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288622895458875024633321793 216467171594156268474991345)
              ·
                refine ⟨162350378695617201356243509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216467171594156268474991345 162350378695617201356243509)
                ·
                  refine ⟨15220348002714112627147829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162350378695617201356243509 15220348002714112627147829)
                  ·
                    refine ⟨1426907625254448058795109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15220348002714112627147829 1426907625254448058795109)
                    ·
                      rfl

theorem cell22_4168339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_4168339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168339 prefixEnd_4168339 := by exact prefixLift 4168339
  have htrace : WordTrace (prefixWord ++ tailWord_4168339) baseStart_4168339 baseEnd_4168339 := by
    simpa [prefixWord, tailWord_4168339, baseEnd_4168339] using wordTrace_append hprefix tailTrace_4168339
  have hstable : (prefixWord ++ tailWord_4168339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168339).length < 2 ^ (prefixWord ++ tailWord_4168339).sum := by decide
  have hdescent : baseEnd_4168339 < baseStart_4168339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168356 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_4168356 : Nat := 118140960795 + 4168356 * 2 ^ 59
def prefixEnd_4168356 : Nat := 4983230072969 + 3 ^ 40 * 4168356 * 2
def baseEnd_4168356 : Nat := 1426913444701865681120057

theorem tailTrace_4168356 : CollatzResearch.WordTrace tailWord_4168356 prefixEnd_4168356 1426913444701865681120057 := by
  unfold tailWord_4168356
  simp only [CollatzResearch.WordTrace]
  refine ⟨76016216643382792686386461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101354955524510390248515281 76016216643382792686386461)
  ·
    refine ⟨28506081241268547257394923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76016216643382792686386461 28506081241268547257394923)
    ·
      refine ⟨42759121861902820886092385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28506081241268547257394923 42759121861902820886092385)
      ·
        refine ⟨32069341396427115664569289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42759121861902820886092385 32069341396427115664569289)
        ·
          refine ⟨24052006047320336748426967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32069341396427115664569289 24052006047320336748426967)
          ·
            refine ⟨36078009070980505122640451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24052006047320336748426967 36078009070980505122640451)
            ·
              refine ⟨54117013606470757683960677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36078009070980505122640451 54117013606470757683960677)
              ·
                refine ⟨10146940051213267065742627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54117013606470757683960677 10146940051213267065742627)
                ·
                  refine ⟨15220410076819900598613941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146940051213267065742627 15220410076819900598613941)
                  ·
                    refine ⟨1426913444701865681120057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15220410076819900598613941 1426913444701865681120057)
                    ·
                      rfl

theorem cell22_4168356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_4168356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168356 prefixEnd_4168356 := by exact prefixLift 4168356
  have htrace : WordTrace (prefixWord ++ tailWord_4168356) baseStart_4168356 baseEnd_4168356 := by
    simpa [prefixWord, tailWord_4168356, baseEnd_4168356] using wordTrace_append hprefix tailTrace_4168356
  have hstable : (prefixWord ++ tailWord_4168356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168356).length < 2 ^ (prefixWord ++ tailWord_4168356).sum := by decide
  have hdescent : baseEnd_4168356 < baseStart_4168356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168431 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 7]
def baseStart_4168431 : Nat := 118140960795 + 4168431 * 2 ^ 59
def prefixEnd_4168431 : Nat := 4983230072969 + 3 ^ 40 * 4168431 * 2
def baseEnd_4168431 : Nat := 475646372911530161831609

theorem tailTrace_4168431 : CollatzResearch.WordTrace tailWord_4168431 prefixEnd_4168431 475646372911530161831609 := by
  unfold tailWord_4168431
  simp only [CollatzResearch.WordTrace]
  refine ⟨152035168761493873181753147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101356779174329248787835431 152035168761493873181753147)
  ·
    refine ⟨228052753142240809772629721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152035168761493873181753147 228052753142240809772629721)
    ·
      refine ⟨171039564856680607329472291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228052753142240809772629721 171039564856680607329472291)
      ·
        refine ⟨256559347285020910994208437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171039564856680607329472291 256559347285020910994208437)
        ·
          refine ⟨24052438807970710405707041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256559347285020910994208437 24052438807970710405707041)
          ·
            refine ⟨18039329105978032804280281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24052438807970710405707041 18039329105978032804280281)
            ·
              refine ⟨13529496829483524603210211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18039329105978032804280281 13529496829483524603210211)
              ·
                refine ⟨20294245244225286904815317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13529496829483524603210211 20294245244225286904815317)
                ·
                  refine ⟨475646372911530161831609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20294245244225286904815317 475646372911530161831609)
                  ·
                    rfl

theorem cell22_4168431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 7].length) (baseStart_4168431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168431 prefixEnd_4168431 := by exact prefixLift 4168431
  have htrace : WordTrace (prefixWord ++ tailWord_4168431) baseStart_4168431 baseEnd_4168431 := by
    simpa [prefixWord, tailWord_4168431, baseEnd_4168431] using wordTrace_append hprefix tailTrace_4168431
  have hstable : (prefixWord ++ tailWord_4168431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168431).length < 2 ^ (prefixWord ++ tailWord_4168431).sum := by decide
  have hdescent : baseEnd_4168431 < baseStart_4168431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168437 : List Nat := [1, 3, 6, 1, 1, 1, 2, 7]
def baseStart_4168437 : Nat := 118140960795 + 4168437 * 2 ^ 59
def prefixEnd_4168437 : Nat := 4983230072969 + 3 ^ 40 * 4168437 * 2
def baseEnd_4168437 : Nat := 158549019184134274427201

theorem tailTrace_4168437 : CollatzResearch.WordTrace tailWord_4168437 prefixEnd_4168437 158549019184134274427201 := by
  unfold tailWord_4168437
  simp only [CollatzResearch.WordTrace]
  refine ⟨152035387599472136206471565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101356925066314757470981043 152035387599472136206471565)
  ·
    refine ⟨57013270349802051077426837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152035387599472136206471565 57013270349802051077426837)
    ·
      refine ⟨2672497047646971144254383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57013270349802051077426837 2672497047646971144254383)
      ·
        refine ⟨4008745571470456716381575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672497047646971144254383 4008745571470456716381575)
        ·
          refine ⟨6013118357205685074572363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008745571470456716381575 6013118357205685074572363)
          ·
            refine ⟨9019677535808527611858545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013118357205685074572363 9019677535808527611858545)
            ·
              refine ⟨6764758151856395708893909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9019677535808527611858545 6764758151856395708893909)
              ·
                refine ⟨158549019184134274427201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6764758151856395708893909 158549019184134274427201)
                ·
                  rfl

theorem cell22_4168437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 7].length) (baseStart_4168437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168437 prefixEnd_4168437 := by exact prefixLift 4168437
  have htrace : WordTrace (prefixWord ++ tailWord_4168437) baseStart_4168437 baseEnd_4168437 := by
    simpa [prefixWord, tailWord_4168437, baseEnd_4168437] using wordTrace_append hprefix tailTrace_4168437
  have hstable : (prefixWord ++ tailWord_4168437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168437).length < 2 ^ (prefixWord ++ tailWord_4168437).sum := by decide
  have hdescent : baseEnd_4168437 < baseStart_4168437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168508 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_4168508 : Nat := 118140960795 + 4168508 * 2 ^ 59
def prefixEnd_4168508 : Nat := 4983230072969 + 3 ^ 40 * 4168508 * 2
def baseEnd_4168508 : Nat := 1426965477408187951319591

theorem tailTrace_4168508 : CollatzResearch.WordTrace tailWord_4168508 prefixEnd_4168508 1426965477408187951319591 := by
  unfold tailWord_4168508
  simp only [CollatzResearch.WordTrace]
  refine ⟨76018988591107457666153089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101358651454809943554870785 76018988591107457666153089)
  ·
    refine ⟨57014241443330593249614817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76018988591107457666153089 57014241443330593249614817)
    ·
      refine ⟨42760681082497944937211113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57014241443330593249614817 42760681082497944937211113)
      ·
        refine ⟨32070510811873458702908335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42760681082497944937211113 32070510811873458702908335)
        ·
          refine ⟨48105766217810188054362503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32070510811873458702908335 48105766217810188054362503)
          ·
            refine ⟨72158649326715282081543755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48105766217810188054362503 72158649326715282081543755)
            ·
              refine ⟨108237973990072923122315633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72158649326715282081543755 108237973990072923122315633)
              ·
                refine ⟨81178480492554692341736725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108237973990072923122315633 81178480492554692341736725)
                ·
                  refine ⟨3805241273088501203518909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81178480492554692341736725 3805241273088501203518909)
                  ·
                    refine ⟨1426965477408187951319591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805241273088501203518909 1426965477408187951319591)
                    ·
                      rfl

theorem cell22_4168508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_4168508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168508 prefixEnd_4168508 := by exact prefixLift 4168508
  have htrace : WordTrace (prefixWord ++ tailWord_4168508) baseStart_4168508 baseEnd_4168508 := by
    simpa [prefixWord, tailWord_4168508, baseEnd_4168508] using wordTrace_append hprefix tailTrace_4168508
  have hstable : (prefixWord ++ tailWord_4168508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168508).length < 2 ^ (prefixWord ++ tailWord_4168508).sum := by decide
  have hdescent : baseEnd_4168508 < baseStart_4168508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168510 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_4168510 : Nat := 118140960795 + 4168510 * 2 ^ 59
def prefixEnd_4168510 : Nat := 4983230072969 + 3 ^ 40 * 4168510 * 2
def baseEnd_4168510 : Nat := 475655387349686870923195

theorem tailTrace_4168510 : CollatzResearch.WordTrace tailWord_4168510 prefixEnd_4168510 475655387349686870923195 := by
  unfold tailWord_4168510
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004756266025958709234873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101358700085471779782585989 19004756266025958709234873)
  ·
    refine ⟨14253567199519469031926155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19004756266025958709234873 14253567199519469031926155)
    ·
      refine ⟨21380350799279203547889233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14253567199519469031926155 21380350799279203547889233)
      ·
        refine ⟨16035263099459402660916925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21380350799279203547889233 16035263099459402660916925)
        ·
          refine ⟨6013223662297275997843847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16035263099459402660916925 6013223662297275997843847)
          ·
            refine ⟨9019835493445913996765771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013223662297275997843847 9019835493445913996765771)
            ·
              refine ⟨13529753240168870995148657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019835493445913996765771 13529753240168870995148657)
              ·
                refine ⟨10147314930126653246361493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13529753240168870995148657 10147314930126653246361493)
                ·
                  refine ⟨475655387349686870923195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10147314930126653246361493 475655387349686870923195)
                  ·
                    rfl

theorem cell22_4168510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_4168510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168510 prefixEnd_4168510 := by exact prefixLift 4168510
  have htrace : WordTrace (prefixWord ++ tailWord_4168510) baseStart_4168510 baseEnd_4168510 := by
    simpa [prefixWord, tailWord_4168510, baseEnd_4168510] using wordTrace_append hprefix tailTrace_4168510
  have hstable : (prefixWord ++ tailWord_4168510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168510).length < 2 ^ (prefixWord ++ tailWord_4168510).sum := by decide
  have hdescent : baseEnd_4168510 < baseStart_4168510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168529 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 1, 4]
def baseStart_4168529 : Nat := 118140960795 + 4168529 * 2 ^ 59
def prefixEnd_4168529 : Nat := 4983230072969 + 3 ^ 40 * 4168529 * 2
def baseEnd_4168529 : Nat := 1426972666137350896544527

theorem tailTrace_4168529 : CollatzResearch.WordTrace tailWord_4168529 prefixEnd_4168529 1426972666137350896544527 := by
  unfold tailWord_4168529
  simp only [CollatzResearch.WordTrace]
  refine ⟨152038743115138835918820641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101359162076759223945880427 152038743115138835918820641)
  ·
    refine ⟨114029057336354126939115481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152038743115138835918820641 114029057336354126939115481)
    ·
      refine ⟨85521793002265595204336611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114029057336354126939115481 85521793002265595204336611)
      ·
        refine ⟨128282689503398392806504917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85521793002265595204336611 128282689503398392806504917)
        ·
          refine ⟨3006625535235899831402459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 128282689503398392806504917 3006625535235899831402459)
          ·
            refine ⟨4509938302853849747103689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006625535235899831402459 4509938302853849747103689)
            ·
              refine ⟨3382453727140387310327767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509938302853849747103689 3382453727140387310327767)
              ·
                refine ⟨5073680590710580965491651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382453727140387310327767 5073680590710580965491651)
                ·
                  refine ⟨7610520886065871448237477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073680590710580965491651 7610520886065871448237477)
                  ·
                    refine ⟨1426972666137350896544527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7610520886065871448237477 1426972666137350896544527)
                    ·
                      rfl

theorem cell22_4168529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_4168529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168529 prefixEnd_4168529 := by exact prefixLift 4168529
  have htrace : WordTrace (prefixWord ++ tailWord_4168529) baseStart_4168529 baseEnd_4168529 := by
    simpa [prefixWord, tailWord_4168529, baseEnd_4168529] using wordTrace_append hprefix tailTrace_4168529
  have hstable : (prefixWord ++ tailWord_4168529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168529).length < 2 ^ (prefixWord ++ tailWord_4168529).sum := by decide
  have hdescent : baseEnd_4168529 < baseStart_4168529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168536 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_4168536 : Nat := 118140960795 + 4168536 * 2 ^ 59
def prefixEnd_4168536 : Nat := 4983230072969 + 3 ^ 40 * 4168536 * 2
def baseEnd_4168536 : Nat := 1426975062380405211619505

theorem tailTrace_4168536 : CollatzResearch.WordTrace tailWord_4168536 prefixEnd_4168536 1426975062380405211619505 := by
  unfold tailWord_4168536
  simp only [CollatzResearch.WordTrace]
  refine ⟨76019499213056738057162731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101359332284075650742883641 76019499213056738057162731)
  ·
    refine ⟨114029248819585107085744097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76019499213056738057162731 114029248819585107085744097)
    ·
      refine ⟨85521936614688830314308073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114029248819585107085744097 85521936614688830314308073)
      ·
        refine ⟨64141452461016622735731055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85521936614688830314308073 64141452461016622735731055)
        ·
          refine ⟨96212178691524934103596583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64141452461016622735731055 96212178691524934103596583)
          ·
            refine ⟨144318268037287401155394875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96212178691524934103596583 144318268037287401155394875)
            ·
              refine ⟨216477402055931101733092313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144318268037287401155394875 216477402055931101733092313)
              ·
                refine ⟨162358051541948326299819235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216477402055931101733092313 162358051541948326299819235)
                ·
                  refine ⟨243537077312922489449728853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162358051541948326299819235 243537077312922489449728853)
                  ·
                    refine ⟨1426975062380405211619505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243537077312922489449728853 1426975062380405211619505)
                    ·
                      rfl

theorem cell22_4168536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_4168536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168536 prefixEnd_4168536 := by exact prefixLift 4168536
  have htrace : WordTrace (prefixWord ++ tailWord_4168536) baseStart_4168536 baseEnd_4168536 := by
    simpa [prefixWord, tailWord_4168536, baseEnd_4168536] using wordTrace_append hprefix tailTrace_4168536
  have hstable : (prefixWord ++ tailWord_4168536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168536).length < 2 ^ (prefixWord ++ tailWord_4168536).sum := by decide
  have hdescent : baseEnd_4168536 < baseStart_4168536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168578 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4168578 : Nat := 118140960795 + 4168578 * 2 ^ 59
def prefixEnd_4168578 : Nat := 4983230072969 + 3 ^ 40 * 4168578 * 2
def baseEnd_4168578 : Nat := 475663146612910367356459

theorem tailTrace_4168578 : CollatzResearch.WordTrace tailWord_4168578 prefixEnd_4168578 475663146612910367356459 := by
  unfold tailWord_4168578
  simp only [CollatzResearch.WordTrace]
  refine ⟨38010132572990329321838597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101360353527974211524902925 38010132572990329321838597)
  ·
    refine ⟨7126899857435686747844737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38010132572990329321838597 7126899857435686747844737)
    ·
      refine ⟨5345174893076765060883553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7126899857435686747844737 5345174893076765060883553)
      ·
        refine ⟨4008881169807573795662665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5345174893076765060883553 4008881169807573795662665)
        ·
          refine ⟨3006660877355680346746999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008881169807573795662665 3006660877355680346746999)
          ·
            refine ⟨4509991316033520520120499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006660877355680346746999 4509991316033520520120499)
            ·
              refine ⟨6764986974050280780180749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509991316033520520120499 6764986974050280780180749)
              ·
                refine ⟨2536870115268855292567781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6764986974050280780180749 2536870115268855292567781)
                ·
                  refine ⟨475663146612910367356459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536870115268855292567781 475663146612910367356459)
                  ·
                    rfl

theorem cell22_4168578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4168578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168578 prefixEnd_4168578 := by exact prefixLift 4168578
  have htrace : WordTrace (prefixWord ++ tailWord_4168578) baseStart_4168578 baseEnd_4168578 := by
    simpa [prefixWord, tailWord_4168578, baseEnd_4168578] using wordTrace_append hprefix tailTrace_4168578
  have hstable : (prefixWord ++ tailWord_4168578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168578).length < 2 ^ (prefixWord ++ tailWord_4168578).sum := by decide
  have hdescent : baseEnd_4168578 < baseStart_4168578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168583 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 7]
def baseStart_4168583 : Nat := 118140960795 + 4168583 * 2 ^ 59
def prefixEnd_4168583 : Nat := 4983230072969 + 3 ^ 40 * 4168583 * 2
def baseEnd_4168583 : Nat := 475663717146970918564787

theorem tailTrace_4168583 : CollatzResearch.WordTrace tailWord_4168583 prefixEnd_4168583 475663717146970918564787 := by
  unfold tailWord_4168583
  simp only [CollatzResearch.WordTrace]
  refine ⟨152040712656943203141286403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101360475104628802094190935 152040712656943203141286403)
  ·
    refine ⟨228061068985414804711929605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152040712656943203141286403 228061068985414804711929605)
    ·
      refine ⟨42761450434765275883486801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228061068985414804711929605 42761450434765275883486801)
      ·
        refine ⟨32071087826073956912615101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42761450434765275883486801 32071087826073956912615101)
        ·
          refine ⟨12026657934777733842230663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32071087826073956912615101 12026657934777733842230663)
          ·
            refine ⟨18039986902166600763345995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12026657934777733842230663 18039986902166600763345995)
            ·
              refine ⟨27059980353249901145018993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18039986902166600763345995 27059980353249901145018993)
              ·
                refine ⟨20294985264937425858764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27059980353249901145018993 20294985264937425858764245)
                ·
                  refine ⟨475663717146970918564787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20294985264937425858764245 475663717146970918564787)
                  ·
                    rfl

theorem cell22_4168583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 7].length) (baseStart_4168583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168583 prefixEnd_4168583 := by exact prefixLift 4168583
  have htrace : WordTrace (prefixWord ++ tailWord_4168583) baseStart_4168583 baseEnd_4168583 := by
    simpa [prefixWord, tailWord_4168583, baseEnd_4168583] using wordTrace_append hprefix tailTrace_4168583
  have hstable : (prefixWord ++ tailWord_4168583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168583).length < 2 ^ (prefixWord ++ tailWord_4168583).sum := by decide
  have hdescent : baseEnd_4168583 < baseStart_4168583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168587 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 1, 3]
def baseStart_4168587 : Nat := 118140960795 + 4168587 * 2 ^ 59
def prefixEnd_4168587 : Nat := 4983230072969 + 3 ^ 40 * 4168587 * 2
def baseEnd_4168587 : Nat := 1426992520722658078594349

theorem tailTrace_4168587 : CollatzResearch.WordTrace tailWord_4168587 prefixEnd_4168587 1426992520722658078594349 := by
  unfold tailWord_4168587
  simp only [CollatzResearch.WordTrace]
  refine ⟨152040858548928711824432015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101360572365952474549621343 152040858548928711824432015)
  ·
    refine ⟨228061287823393067736648023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152040858548928711824432015 228061287823393067736648023)
    ·
      refine ⟨342091931735089601604972035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228061287823393067736648023 342091931735089601604972035)
      ·
        refine ⟨513137897602634402407458053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342091931735089601604972035 513137897602634402407458053)
        ·
          refine ⟨96213355800493950451398385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513137897602634402407458053 96213355800493950451398385)
          ·
            refine ⟨72160016850370462838548789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96213355800493950451398385 72160016850370462838548789)
            ·
              refine ⟨6765001579722230891113949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72160016850370462838548789 6765001579722230891113949)
              ·
                refine ⟨2536875592395836584167731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6765001579722230891113949 2536875592395836584167731)
                ·
                  refine ⟨3805313388593754876251597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536875592395836584167731 3805313388593754876251597)
                  ·
                    refine ⟨1426992520722658078594349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805313388593754876251597 1426992520722658078594349)
                    ·
                      rfl

theorem cell22_4168587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 3].length) (baseStart_4168587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168587 prefixEnd_4168587 := by exact prefixLift 4168587
  have htrace : WordTrace (prefixWord ++ tailWord_4168587) baseStart_4168587 baseEnd_4168587 := by
    simpa [prefixWord, tailWord_4168587, baseEnd_4168587] using wordTrace_append hprefix tailTrace_4168587
  have hstable : (prefixWord ++ tailWord_4168587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168587).length < 2 ^ (prefixWord ++ tailWord_4168587).sum := by decide
  have hdescent : baseEnd_4168587 < baseStart_4168587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168604 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_4168604 : Nat := 118140960795 + 4168604 * 2 ^ 59
def prefixEnd_4168604 : Nat := 4983230072969 + 3 ^ 40 * 4168604 * 2
def baseEnd_4168604 : Nat := 1426998340170075700919297

theorem tailTrace_4168604 : CollatzResearch.WordTrace tailWord_4168604 prefixEnd_4168604 1426998340170075700919297 := by
  unfold tailWord_4168604
  simp only [CollatzResearch.WordTrace]
  refine ⟨76020739294933561863900433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101360985726578082485200577 76020739294933561863900433)
  ·
    refine ⟨57015554471200171397925325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76020739294933561863900433 57015554471200171397925325)
    ·
      refine ⟨21380832926700064274221997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57015554471200171397925325 21380832926700064274221997)
      ·
        refine ⟨8017812347512524102833249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21380832926700064274221997 8017812347512524102833249)
        ·
          refine ⟨6013359260634393077124937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8017812347512524102833249 6013359260634393077124937)
          ·
            refine ⟨4510019445475794807843703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6013359260634393077124937 4510019445475794807843703)
            ·
              refine ⟨6765029168213692211765555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510019445475794807843703 6765029168213692211765555)
              ·
                refine ⟨10147543752320538317648333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765029168213692211765555 10147543752320538317648333)
                ·
                  refine ⟨3805328907120201869118125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10147543752320538317648333 3805328907120201869118125)
                  ·
                    refine ⟨1426998340170075700919297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805328907120201869118125 1426998340170075700919297)
                    ·
                      rfl

theorem cell22_4168604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_4168604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168604 prefixEnd_4168604 := by exact prefixLift 4168604
  have htrace : WordTrace (prefixWord ++ tailWord_4168604) baseStart_4168604 baseEnd_4168604 := by
    simpa [prefixWord, tailWord_4168604, baseEnd_4168604] using wordTrace_append hprefix tailTrace_4168604
  have hstable : (prefixWord ++ tailWord_4168604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168604).length < 2 ^ (prefixWord ++ tailWord_4168604).sum := by decide
  have hdescent : baseEnd_4168604 < baseStart_4168604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168643 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 1, 5]
def baseStart_4168643 : Nat := 118140960795 + 4168643 * 2 ^ 59
def prefixEnd_4168643 : Nat := 4983230072969 + 3 ^ 40 * 4168643 * 2
def baseEnd_4168643 : Nat := 1427011690667092599194177

theorem tailTrace_4168643 : CollatzResearch.WordTrace tailWord_4168643 prefixEnd_4168643 1427011690667092599194177 := by
  unfold tailWord_4168643
  simp only [CollatzResearch.WordTrace]
  refine ⟨152042901036725833388470583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101361934024483888925647055 152042901036725833388470583)
  ·
    refine ⟨228064351555088750082705875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152042901036725833388470583 228064351555088750082705875)
    ·
      refine ⟨342096527332633125124058813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228064351555088750082705875 342096527332633125124058813)
      ·
        refine ⟨128286197749737421921522055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342096527332633125124058813 128286197749737421921522055)
        ·
          refine ⟨192429296624606132882283083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128286197749737421921522055 192429296624606132882283083)
          ·
            refine ⟨288643944936909199323424625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192429296624606132882283083 288643944936909199323424625)
            ·
              refine ⟨216482958702681899492568469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288643944936909199323424625 216482958702681899492568469)
              ·
                refine ⟨10147638689188214038714147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 216482958702681899492568469 10147638689188214038714147)
                ·
                  refine ⟨15221458033782321058071221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10147638689188214038714147 15221458033782321058071221)
                  ·
                    refine ⟨1427011690667092599194177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15221458033782321058071221 1427011690667092599194177)
                    ·
                      rfl

theorem cell22_4168643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_4168643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168643 prefixEnd_4168643 := by exact prefixLift 4168643
  have htrace : WordTrace (prefixWord ++ tailWord_4168643) baseStart_4168643 baseEnd_4168643 := by
    simpa [prefixWord, tailWord_4168643, baseEnd_4168643] using wordTrace_append hprefix tailTrace_4168643
  have hstable : (prefixWord ++ tailWord_4168643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168643).length < 2 ^ (prefixWord ++ tailWord_4168643).sum := by decide
  have hdescent : baseEnd_4168643 < baseStart_4168643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168825 : List Nat := [1, 2, 1, 3, 5, 10]
def baseStart_4168825 : Nat := 118140960795 + 4168825 * 2 ^ 59
def prefixEnd_4168825 : Nat := 4983230072969 + 3 ^ 40 * 4168825 * 2
def baseEnd_4168825 : Nat := 17618197444277836927699

theorem tailTrace_4168825 : CollatzResearch.WordTrace tailWord_4168825 prefixEnd_4168825 17618197444277836927699 := by
  unfold tailWord_4168825
  simp only [CollatzResearch.WordTrace]
  refine ⟨152049539122066478471595929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101366359414710985647730619 152049539122066478471595929)
  ·
    refine ⟨114037154341549858853696947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152049539122066478471595929 114037154341549858853696947)
    ·
      refine ⟨171055731512324788280545421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114037154341549858853696947 171055731512324788280545421)
      ·
        refine ⟨64145899317121795605204533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171055731512324788280545421 64145899317121795605204533)
        ·
          refine ⟨6013678060980168337987925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64145899317121795605204533 6013678060980168337987925)
          ·
            refine ⟨17618197444277836927699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6013678060980168337987925 17618197444277836927699)
            ·
              rfl

theorem cell22_4168825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 10].length) (baseStart_4168825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168825 prefixEnd_4168825 := by exact prefixLift 4168825
  have htrace : WordTrace (prefixWord ++ tailWord_4168825) baseStart_4168825 baseEnd_4168825 := by
    simpa [prefixWord, tailWord_4168825, baseEnd_4168825] using wordTrace_append hprefix tailTrace_4168825
  have hstable : (prefixWord ++ tailWord_4168825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168825).length < 2 ^ (prefixWord ++ tailWord_4168825).sum := by decide
  have hdescent : baseEnd_4168825 < baseStart_4168825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168829 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_4168829 : Nat := 118140960795 + 4168829 * 2 ^ 59
def prefixEnd_4168829 : Nat := 4983230072969 + 3 ^ 40 * 4168829 * 2
def baseEnd_4168829 : Nat := 1427075362268250114043607

theorem tailTrace_4168829 : CollatzResearch.WordTrace tailWord_4168829 prefixEnd_4168829 1427075362268250114043607 := by
  unfold tailWord_4168829
  simp only [CollatzResearch.WordTrace]
  refine ⟨152049685014051987154741541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101366456676034658103161027 152049685014051987154741541)
  ·
    refine ⟨28509315940134747591514039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152049685014051987154741541 28509315940134747591514039)
    ·
      refine ⟨42763973910202121387271059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28509315940134747591514039 42763973910202121387271059)
      ·
        refine ⟨64145960865303182080906589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42763973910202121387271059 64145960865303182080906589)
        ·
          refine ⟨24054735324488693280339971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64145960865303182080906589 24054735324488693280339971)
          ·
            refine ⟨36082102986733039920509957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24054735324488693280339971 36082102986733039920509957)
            ·
              refine ⟨6765394310012444985095617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36082102986733039920509957 6765394310012444985095617)
              ·
                refine ⟨5074045732509333738821713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765394310012444985095617 5074045732509333738821713)
                ·
                  refine ⟨3805534299382000304116285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074045732509333738821713 3805534299382000304116285)
                  ·
                    refine ⟨1427075362268250114043607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805534299382000304116285 1427075362268250114043607)
                    ·
                      rfl

theorem cell22_4168829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_4168829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168829 prefixEnd_4168829 := by exact prefixLift 4168829
  have htrace : WordTrace (prefixWord ++ tailWord_4168829) baseStart_4168829 baseEnd_4168829 := by
    simpa [prefixWord, tailWord_4168829, baseEnd_4168829] using wordTrace_append hprefix tailTrace_4168829
  have hstable : (prefixWord ++ tailWord_4168829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168829).length < 2 ^ (prefixWord ++ tailWord_4168829).sum := by decide
  have hdescent : baseEnd_4168829 < baseStart_4168829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168925 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_4168925 : Nat := 118140960795 + 4168925 * 2 ^ 59
def prefixEnd_4168925 : Nat := 4983230072969 + 3 ^ 40 * 4168925 * 2
def baseEnd_4168925 : Nat := 1427108225030137863643313

theorem tailTrace_4168925 : CollatzResearch.WordTrace tailWord_4168925 prefixEnd_4168925 1427108225030137863643313 := by
  unfold tailWord_4168925
  simp only [CollatzResearch.WordTrace]
  refine ⟨152053186421704195550236229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101368790947802797033490819 152053186421704195550236229)
  ·
    refine ⟨28509972454069536665669293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152053186421704195550236229 28509972454069536665669293)
    ·
      refine ⟨10691239670276076249625985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28509972454069536665669293 10691239670276076249625985)
      ·
        refine ⟨8018429752707057187219489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10691239670276076249625985 8018429752707057187219489)
        ·
          refine ⟨6013822314530292890414617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8018429752707057187219489 6013822314530292890414617)
          ·
            refine ⟨4510366735897719667810963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6013822314530292890414617 4510366735897719667810963)
            ·
              refine ⟨6765550103846579501716445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510366735897719667810963 6765550103846579501716445)
              ·
                refine ⟨2537081288942467313143667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6765550103846579501716445 2537081288942467313143667)
                ·
                  refine ⟨3805621933413700969715501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537081288942467313143667 3805621933413700969715501)
                  ·
                    refine ⟨1427108225030137863643313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805621933413700969715501 1427108225030137863643313)
                    ·
                      rfl

theorem cell22_4168925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_4168925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168925 prefixEnd_4168925 := by exact prefixLift 4168925
  have htrace : WordTrace (prefixWord ++ tailWord_4168925) baseStart_4168925 baseEnd_4168925 := by
    simpa [prefixWord, tailWord_4168925, baseEnd_4168925] using wordTrace_append hprefix tailTrace_4168925
  have hstable : (prefixWord ++ tailWord_4168925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168925).length < 2 ^ (prefixWord ++ tailWord_4168925).sum := by decide
  have hdescent : baseEnd_4168925 < baseStart_4168925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168968 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 1, 4]
def baseStart_4168968 : Nat := 118140960795 + 4168968 * 2 ^ 59
def prefixEnd_4168968 : Nat := 4983230072969 + 3 ^ 40 * 4168968 * 2
def baseEnd_4168968 : Nat := 1427122944808900084818181

theorem tailTrace_4168968 : CollatzResearch.WordTrace tailWord_4168968 prefixEnd_4168968 1427122944808900084818181 := by
  unfold tailWord_4168968
  simp only [CollatzResearch.WordTrace]
  refine ⟨76027377380274206947025779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101369836507032275929367705 76027377380274206947025779)
  ·
    refine ⟨114041066070411310420538669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76027377380274206947025779 114041066070411310420538669)
    ·
      refine ⟨42765399776404241407702001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114041066070411310420538669 42765399776404241407702001)
      ·
        refine ⟨32074049832303181055776501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42765399776404241407702001 32074049832303181055776501)
        ·
          refine ⟨3006942171778423223979047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32074049832303181055776501 3006942171778423223979047)
          ·
            refine ⟨4510413257667634835968571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006942171778423223979047 4510413257667634835968571)
            ·
              refine ⟨6765619886501452253952857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510413257667634835968571 6765619886501452253952857)
              ·
                refine ⟨5074214914876089190464643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765619886501452253952857 5074214914876089190464643)
                ·
                  refine ⟨7611322372314133785696965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074214914876089190464643 7611322372314133785696965)
                  ·
                    refine ⟨1427122944808900084818181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7611322372314133785696965 1427122944808900084818181)
                    ·
                      rfl

theorem cell22_4168968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_4168968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168968 prefixEnd_4168968 := by exact prefixLift 4168968
  have htrace : WordTrace (prefixWord ++ tailWord_4168968) baseStart_4168968 baseEnd_4168968 := by
    simpa [prefixWord, tailWord_4168968, baseEnd_4168968] using wordTrace_append hprefix tailTrace_4168968
  have hstable : (prefixWord ++ tailWord_4168968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168968).length < 2 ^ (prefixWord ++ tailWord_4168968).sum := by decide
  have hdescent : baseEnd_4168968 < baseStart_4168968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168994 : List Nat := [3, 3, 1, 1, 5, 9]
def baseStart_4168994 : Nat := 118140960795 + 4168994 * 2 ^ 59
def prefixEnd_4168994 : Nat := 4983230072969 + 3 ^ 40 * 4168994 * 2
def baseEnd_4168994 : Nat := 17618911668398082514421

theorem tailTrace_4168994 : CollatzResearch.WordTrace tailWord_4168994 prefixEnd_4168994 17618911668398082514421 := by
  unfold tailWord_4168994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38013925764613555083624509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101370468705636146889665357 38013925764613555083624509)
  ·
    refine ⟨14255222161730083156359191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38013925764613555083624509 14255222161730083156359191)
    ·
      refine ⟨21382833242595124734538787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255222161730083156359191 21382833242595124734538787)
      ·
        refine ⟨32074249863892687101808181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382833242595124734538787 32074249863892687101808181)
        ·
          refine ⟨3006960924739939415794517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32074249863892687101808181 3006960924739939415794517)
          ·
            refine ⟨17618911668398082514421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3006960924739939415794517 17618911668398082514421)
            ·
              rfl

theorem cell22_4168994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 9].length) (baseStart_4168994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4168994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4168994 prefixEnd_4168994 := by exact prefixLift 4168994
  have htrace : WordTrace (prefixWord ++ tailWord_4168994) baseStart_4168994 baseEnd_4168994 := by
    simpa [prefixWord, tailWord_4168994, baseEnd_4168994] using wordTrace_append hprefix tailTrace_4168994
  have hstable : (prefixWord ++ tailWord_4168994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168994).length < 2 ^ (prefixWord ++ tailWord_4168994).sum := by decide
  have hdescent : baseEnd_4168994 < baseStart_4168994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169056 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 5]
def baseStart_4169056 : Nat := 118140960795 + 4169056 * 2 ^ 59
def prefixEnd_4169056 : Nat := 4983230072969 + 3 ^ 40 * 4169056 * 2
def baseEnd_4169056 : Nat := 475717689669099062872637

theorem tailTrace_4169056 : CollatzResearch.WordTrace tailWord_4169056 prefixEnd_4169056 475717689669099062872637 := by
  unfold tailWord_4169056
  simp only [CollatzResearch.WordTrace]
  refine ⟨76028982192114802461627511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101371976256153069948836681 76028982192114802461627511)
  ·
    refine ⟨114043473288172203692441267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76028982192114802461627511 114043473288172203692441267)
    ·
      refine ⟨171065209932258305538661901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114043473288172203692441267 171065209932258305538661901)
      ·
        refine ⟨64149453724596864576998213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171065209932258305538661901 64149453724596864576998213)
        ·
          refine ⟨12028022573361912108187165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64149453724596864576998213 12028022573361912108187165)
          ·
            refine ⟨4510508465010717040570187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12028022573361912108187165 4510508465010717040570187)
            ·
              refine ⟨6765762697516075560855281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510508465010717040570187 6765762697516075560855281)
              ·
                refine ⟨5074322023137056670641461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765762697516075560855281 5074322023137056670641461)
                ·
                  refine ⟨475717689669099062872637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5074322023137056670641461 475717689669099062872637)
                  ·
                    rfl

theorem cell22_4169056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_4169056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169056 prefixEnd_4169056 := by exact prefixLift 4169056
  have htrace : WordTrace (prefixWord ++ tailWord_4169056) baseStart_4169056 baseEnd_4169056 := by
    simpa [prefixWord, tailWord_4169056, baseEnd_4169056] using wordTrace_append hprefix tailTrace_4169056
  have hstable : (prefixWord ++ tailWord_4169056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169056).length < 2 ^ (prefixWord ++ tailWord_4169056).sum := by decide
  have hdescent : baseEnd_4169056 < baseStart_4169056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169099 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 6, 3]
def baseStart_4169099 : Nat := 118140960795 + 4169099 * 2 ^ 59
def prefixEnd_4169099 : Nat := 4983230072969 + 3 ^ 40 * 4169099 * 2
def baseEnd_4169099 : Nat := 1427167788786059409792779

theorem tailTrace_4169099 : CollatzResearch.WordTrace tailWord_4169099 prefixEnd_4169099 1427167788786059409792779 := by
  unfold tailWord_4169099
  simp only [CollatzResearch.WordTrace]
  refine ⟨152059532723073823267070351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101373021815382548844713567 152059532723073823267070351)
  ·
    refine ⟨228089299084610734900605527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152059532723073823267070351 228089299084610734900605527)
    ·
      refine ⟨342133948626916102350908291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228089299084610734900605527 342133948626916102350908291)
      ·
        refine ⟨513200922940374153526362437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342133948626916102350908291 513200922940374153526362437)
        ·
          refine ⟨96225173051320153786192957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513200922940374153526362437 96225173051320153786192957)
          ·
            refine ⟨36084439894245057669822359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96225173051320153786192957 36084439894245057669822359)
            ·
              refine ⟨54126659841367586504733539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36084439894245057669822359 54126659841367586504733539)
              ·
                refine ⟨81189989762051379757100309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54126659841367586504733539 81189989762051379757100309)
                ·
                  refine ⟨3805780770096158426114077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81189989762051379757100309 3805780770096158426114077)
                  ·
                    refine ⟨1427167788786059409792779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805780770096158426114077 1427167788786059409792779)
                    ·
                      rfl

theorem cell22_4169099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 3].length) (baseStart_4169099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169099 prefixEnd_4169099 := by exact prefixLift 4169099
  have htrace : WordTrace (prefixWord ++ tailWord_4169099) baseStart_4169099 baseEnd_4169099 := by
    simpa [prefixWord, tailWord_4169099, baseEnd_4169099] using wordTrace_append hprefix tailTrace_4169099
  have hstable : (prefixWord ++ tailWord_4169099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169099).length < 2 ^ (prefixWord ++ tailWord_4169099).sum := by decide
  have hdescent : baseEnd_4169099 < baseStart_4169099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169148 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_4169148 : Nat := 118140960795 + 4169148 * 2 ^ 59
def prefixEnd_4169148 : Nat := 4983230072969 + 3 ^ 40 * 4169148 * 2
def baseEnd_4169148 : Nat := 1427184562487439615317629

theorem tailTrace_4169148 : CollatzResearch.WordTrace tailWord_4169148 prefixEnd_4169148 1427184562487439615317629 := by
  unfold tailWord_4169148
  simp only [CollatzResearch.WordTrace]
  refine ⟨76030659949948152317802049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101374213266597536423736065 76030659949948152317802049)
  ·
    refine ⟨57022994962461114238351537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76030659949948152317802049 57022994962461114238351537)
    ·
      refine ⟨42767246221845835678763653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57022994962461114238351537 42767246221845835678763653)
      ·
        refine ⟨8018858666596094189768185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42767246221845835678763653 8018858666596094189768185)
        ·
          refine ⟨6014143999947070642326139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8018858666596094189768185 6014143999947070642326139)
          ·
            refine ⟨9021215999920605963489209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014143999947070642326139 9021215999920605963489209)
            ·
              refine ⟨6765911999940454472616907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9021215999920605963489209 6765911999940454472616907)
              ·
                refine ⟨10148867999910681708925361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765911999940454472616907 10148867999910681708925361)
                ·
                  refine ⟨7611650999933011281694021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10148867999910681708925361 7611650999933011281694021)
                  ·
                    refine ⟨1427184562487439615317629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7611650999933011281694021 1427184562487439615317629)
                    ·
                      rfl

theorem cell22_4169148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_4169148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169148 prefixEnd_4169148 := by exact prefixLift 4169148
  have htrace : WordTrace (prefixWord ++ tailWord_4169148) baseStart_4169148 baseEnd_4169148 := by
    simpa [prefixWord, tailWord_4169148, baseEnd_4169148] using wordTrace_append hprefix tailTrace_4169148
  have hstable : (prefixWord ++ tailWord_4169148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169148).length < 2 ^ (prefixWord ++ tailWord_4169148).sum := by decide
  have hdescent : baseEnd_4169148 < baseStart_4169148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169191 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 5]
def baseStart_4169191 : Nat := 118140960795 + 4169191 * 2 ^ 59
def prefixEnd_4169191 : Nat := 4983230072969 + 3 ^ 40 * 4169191 * 2
def baseEnd_4169191 : Nat := 475733094088733945497499

theorem tailTrace_4169191 : CollatzResearch.WordTrace tailWord_4169191 prefixEnd_4169191 475733094088733945497499 := by
  unfold tailWord_4169191
  simp only [CollatzResearch.WordTrace]
  refine ⟨152062888238740522979419427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101375258825827015319612951 152062888238740522979419427)
  ·
    refine ⟨228094332358110784469129141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152062888238740522979419427 228094332358110784469129141)
    ·
      refine ⟨21383843658572886043980857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228094332358110784469129141 21383843658572886043980857)
      ·
        refine ⟨16037882743929664532985643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21383843658572886043980857 16037882743929664532985643)
        ·
          refine ⟨24056824115894496799478465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037882743929664532985643 24056824115894496799478465)
          ·
            refine ⟨18042618086920872599608849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24056824115894496799478465 18042618086920872599608849)
            ·
              refine ⟨13531963565190654449706637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18042618086920872599608849 13531963565190654449706637)
              ·
                refine ⟨5074486336946495418639989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13531963565190654449706637 5074486336946495418639989)
                ·
                  refine ⟨475733094088733945497499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5074486336946495418639989 475733094088733945497499)
                  ·
                    rfl

theorem cell22_4169191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 5].length) (baseStart_4169191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169191 prefixEnd_4169191 := by exact prefixLift 4169191
  have htrace : WordTrace (prefixWord ++ tailWord_4169191) baseStart_4169191 baseEnd_4169191 := by
    simpa [prefixWord, tailWord_4169191, baseEnd_4169191] using wordTrace_append hprefix tailTrace_4169191
  have hstable : (prefixWord ++ tailWord_4169191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169191).length < 2 ^ (prefixWord ++ tailWord_4169191).sum := by decide
  have hdescent : baseEnd_4169191 < baseStart_4169191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169266 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_4169266 : Nat := 118140960795 + 4169266 * 2 ^ 59
def prefixEnd_4169266 : Nat := 4983230072969 + 3 ^ 40 * 4169266 * 2
def baseEnd_4169266 : Nat := 1427224956298926640867267

theorem tailTrace_4169266 : CollatzResearch.WordTrace tailWord_4169266 prefixEnd_4169266 1427224956298926640867267 := by
  unfold tailWord_4169266
  simp only [CollatzResearch.WordTrace]
  refine ⟨38016405928367202697099913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101377082475645873858933101 38016405928367202697099913)
  ·
    refine ⟨28512304446275402022824935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38016405928367202697099913 28512304446275402022824935)
    ·
      refine ⟨42768456669413103034237403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28512304446275402022824935 42768456669413103034237403)
      ·
        refine ⟨64152685004119654551356105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42768456669413103034237403 64152685004119654551356105)
        ·
          refine ⟨48114513753089740913517079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64152685004119654551356105 48114513753089740913517079)
          ·
            refine ⟨72171770629634611370275619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48114513753089740913517079 72171770629634611370275619)
            ·
              refine ⟨108257655944451917055413429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72171770629634611370275619 108257655944451917055413429)
              ·
                refine ⟨10149155244792367223945009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108257655944451917055413429 10149155244792367223945009)
                ·
                  refine ⟨7611866433594275417958757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10149155244792367223945009 7611866433594275417958757)
                  ·
                    refine ⟨1427224956298926640867267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7611866433594275417958757 1427224956298926640867267)
                    ·
                      rfl

theorem cell22_4169266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_4169266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169266 prefixEnd_4169266 := by exact prefixLift 4169266
  have htrace : WordTrace (prefixWord ++ tailWord_4169266) baseStart_4169266 baseEnd_4169266 := by
    simpa [prefixWord, tailWord_4169266, baseEnd_4169266] using wordTrace_append hprefix tailTrace_4169266
  have hstable : (prefixWord ++ tailWord_4169266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169266).length < 2 ^ (prefixWord ++ tailWord_4169266).sum := by decide
  have hdescent : baseEnd_4169266 < baseStart_4169266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169356 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_4169356 : Nat := 118140960795 + 4169356 * 2 ^ 59
def prefixEnd_4169356 : Nat := 4983230072969 + 3 ^ 40 * 4169356 * 2
def baseEnd_4169356 : Nat := 1427255765138196406116991

theorem tailTrace_4169356 : CollatzResearch.WordTrace tailWord_4169356 prefixEnd_4169356 1427255765138196406116991 := by
  unfold tailWord_4169356
  simp only [CollatzResearch.WordTrace]
  refine ⟨76034453141571378079587961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101379270855428504106117281 76034453141571378079587961)
  ·
    refine ⟨57025839856178533559690971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76034453141571378079587961 57025839856178533559690971)
    ·
      refine ⟨85538759784267800339536457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57025839856178533559690971 85538759784267800339536457)
      ·
        refine ⟨64154069838200850254652343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85538759784267800339536457 64154069838200850254652343)
        ·
          refine ⟨96231104757301275381978515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64154069838200850254652343 96231104757301275381978515)
          ·
            refine ⟨144346657135951913072967773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96231104757301275381978515 144346657135951913072967773)
            ·
              refine ⟨54129996425981967402362915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144346657135951913072967773 54129996425981967402362915)
              ·
                refine ⟨81194994638972951103544373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54129996425981967402362915 81194994638972951103544373)
                ·
                  refine ⟨7612030747403714165957285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81194994638972951103544373 7612030747403714165957285)
                  ·
                    refine ⟨1427255765138196406116991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7612030747403714165957285 1427255765138196406116991)
                    ·
                      rfl

theorem cell22_4169356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_4169356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169356 prefixEnd_4169356 := by exact prefixLift 4169356
  have htrace : WordTrace (prefixWord ++ tailWord_4169356) baseStart_4169356 baseEnd_4169356 := by
    simpa [prefixWord, tailWord_4169356, baseEnd_4169356] using wordTrace_append hprefix tailTrace_4169356
  have hstable : (prefixWord ++ tailWord_4169356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169356).length < 2 ^ (prefixWord ++ tailWord_4169356).sum := by decide
  have hdescent : baseEnd_4169356 < baseStart_4169356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169358 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_4169358 : Nat := 118140960795 + 4169358 * 2 ^ 59
def prefixEnd_4169358 : Nat := 4983230072969 + 3 ^ 40 * 4169358 * 2
def baseEnd_4169358 : Nat := 1427256449779069067566985

theorem tailTrace_4169358 : CollatzResearch.WordTrace tailWord_4169358 prefixEnd_4169358 1427256449779069067566985 := by
  unfold tailWord_4169358
  simp only [CollatzResearch.WordTrace]
  refine ⟨19008622403641938812593591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101379319486090340333832485 19008622403641938812593591)
  ·
    refine ⟨28512933605462908218890387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19008622403641938812593591 28512933605462908218890387)
    ·
      refine ⟨42769400408194362328335581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28512933605462908218890387 42769400408194362328335581)
      ·
        refine ⟨16038525153072885873125843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42769400408194362328335581 16038525153072885873125843)
        ·
          refine ⟨24057787729609328809688765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16038525153072885873125843 24057787729609328809688765)
          ·
            refine ⟨9021670398603498303633287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24057787729609328809688765 9021670398603498303633287)
            ·
              refine ⟨13532505597905247455449931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021670398603498303633287 13532505597905247455449931)
              ·
                refine ⟨20298758396857871183174897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13532505597905247455449931 20298758396857871183174897)
                ·
                  refine ⟨15224068797643403387381173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20298758396857871183174897 15224068797643403387381173)
                  ·
                    refine ⟨1427256449779069067566985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15224068797643403387381173 1427256449779069067566985)
                    ·
                      rfl

theorem cell22_4169358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_4169358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169358 prefixEnd_4169358 := by exact prefixLift 4169358
  have htrace : WordTrace (prefixWord ++ tailWord_4169358) baseStart_4169358 baseEnd_4169358 := by
    simpa [prefixWord, tailWord_4169358, baseEnd_4169358] using wordTrace_append hprefix tailTrace_4169358
  have hstable : (prefixWord ++ tailWord_4169358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169358).length < 2 ^ (prefixWord ++ tailWord_4169358).sum := by decide
  have hdescent : baseEnd_4169358 < baseStart_4169358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169373 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4169373 : Nat := 118140960795 + 4169373 * 2 ^ 59
def prefixEnd_4169373 : Nat := 4983230072969 + 3 ^ 40 * 4169373 * 2
def baseEnd_4169373 : Nat := 1427261584585614028441939

theorem tailTrace_4169373 : CollatzResearch.WordTrace tailWord_4169373 prefixEnd_4169373 1427261584585614028441939 := by
  unfold tailWord_4169373
  simp only [CollatzResearch.WordTrace]
  refine ⟨152069526324081168062544773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101379684216054112041696515 152069526324081168062544773)
  ·
    refine ⟨28513036185765219011727145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152069526324081168062544773 28513036185765219011727145)
    ·
      refine ⟨21384777139323914258795359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28513036185765219011727145 21384777139323914258795359)
      ·
        refine ⟨32077165708985871388193039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21384777139323914258795359 32077165708985871388193039)
        ·
          refine ⟨48115748563478807082289559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32077165708985871388193039 48115748563478807082289559)
          ·
            refine ⟨72173622845218210623434339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48115748563478807082289559 72173622845218210623434339)
            ·
              refine ⟨108260434267827315935151509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72173622845218210623434339 108260434267827315935151509)
              ·
                refine ⟨5074707856304405434460227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108260434267827315935151509 5074707856304405434460227)
                ·
                  refine ⟨7612061784456608151690341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074707856304405434460227 7612061784456608151690341)
                  ·
                    refine ⟨1427261584585614028441939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7612061784456608151690341 1427261584585614028441939)
                    ·
                      rfl

theorem cell22_4169373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4169373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169373 prefixEnd_4169373 := by exact prefixLift 4169373
  have htrace : WordTrace (prefixWord ++ tailWord_4169373) baseStart_4169373 baseEnd_4169373 := by
    simpa [prefixWord, tailWord_4169373, baseEnd_4169373] using wordTrace_append hprefix tailTrace_4169373
  have hstable : (prefixWord ++ tailWord_4169373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169373).length < 2 ^ (prefixWord ++ tailWord_4169373).sum := by decide
  have hdescent : baseEnd_4169373 < baseStart_4169373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169416 : List Nat := [2, 1, 3, 1, 2, 2, 2, 9]
def baseStart_4169416 : Nat := 118140960795 + 4169416 * 2 ^ 59
def prefixEnd_4169416 : Nat := 4983230072969 + 3 ^ 40 * 4169416 * 2
def baseEnd_4169416 : Nat := 158586256040486249957423

theorem tailTrace_4169416 : CollatzResearch.WordTrace tailWord_4169416 prefixEnd_4169416 158586256040486249957423 := by
  unfold tailWord_4169416
  simp only [CollatzResearch.WordTrace]
  refine ⟨76035547331462693203180051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101380729775283590937573401 76035547331462693203180051)
  ·
    refine ⟨114053320997194039804770077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76035547331462693203180051 114053320997194039804770077)
    ·
      refine ⟨42769995373947764926788779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114053320997194039804770077 42769995373947764926788779)
      ·
        refine ⟨64154993060921647390183169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42769995373947764926788779 64154993060921647390183169)
        ·
          refine ⟨48116244795691235542637377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64154993060921647390183169 48116244795691235542637377)
          ·
            refine ⟨36087183596768426656978033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48116244795691235542637377 36087183596768426656978033)
            ·
              refine ⟨27065387697576319992733525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36087183596768426656978033 27065387697576319992733525)
              ·
                refine ⟨158586256040486249957423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27065387697576319992733525 158586256040486249957423)
                ·
                  rfl

theorem cell22_4169416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_4169416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169416 prefixEnd_4169416 := by exact prefixLift 4169416
  have htrace : WordTrace (prefixWord ++ tailWord_4169416) baseStart_4169416 baseEnd_4169416 := by
    simpa [prefixWord, tailWord_4169416, baseEnd_4169416] using wordTrace_append hprefix tailTrace_4169416
  have hstable : (prefixWord ++ tailWord_4169416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169416).length < 2 ^ (prefixWord ++ tailWord_4169416).sum := by decide
  have hdescent : baseEnd_4169416 < baseStart_4169416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169431 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_4169431 : Nat := 118140960795 + 4169431 * 2 ^ 59
def prefixEnd_4169431 : Nat := 4983230072969 + 3 ^ 40 * 4169431 * 2
def baseEnd_4169431 : Nat := 1427281439170921210491761

theorem tailTrace_4169431 : CollatzResearch.WordTrace tailWord_4169431 prefixEnd_4169431 1427281439170921210491761 := by
  unfold tailWord_4169431
  simp only [CollatzResearch.WordTrace]
  refine ⟨152071641757871043968156147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101381094505247362645437431 152071641757871043968156147)
  ·
    refine ⟨228107462636806565952234221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152071641757871043968156147 228107462636806565952234221)
    ·
      refine ⟨85540298488802462232087833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228107462636806565952234221 85540298488802462232087833)
      ·
        refine ⟨64155223866601846674065875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85540298488802462232087833 64155223866601846674065875)
        ·
          refine ⟨96232835799902770011098813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64155223866601846674065875 96232835799902770011098813)
          ·
            refine ⟨36087313424963538754162055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96232835799902770011098813 36087313424963538754162055)
            ·
              refine ⟨54130970137445308131243083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36087313424963538754162055 54130970137445308131243083)
              ·
                refine ⟨81196455206167962196864625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54130970137445308131243083 81196455206167962196864625)
                ·
                  refine ⟨60897341404625971647648469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81196455206167962196864625 60897341404625971647648469)
                  ·
                    refine ⟨1427281439170921210491761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60897341404625971647648469 1427281439170921210491761)
                    ·
                      rfl

theorem cell22_4169431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_4169431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169431 prefixEnd_4169431 := by exact prefixLift 4169431
  have htrace : WordTrace (prefixWord ++ tailWord_4169431) baseStart_4169431 baseEnd_4169431 := by
    simpa [prefixWord, tailWord_4169431, baseEnd_4169431] using wordTrace_append hprefix tailTrace_4169431
  have hstable : (prefixWord ++ tailWord_4169431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169431).length < 2 ^ (prefixWord ++ tailWord_4169431).sum := by decide
  have hdescent : baseEnd_4169431 < baseStart_4169431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169433 : List Nat := [1, 2, 1, 2, 3, 3, 4, 6]
def baseStart_4169433 : Nat := 118140960795 + 4169433 * 2 ^ 59
def prefixEnd_4169433 : Nat := 4983230072969 + 3 ^ 40 * 4169433 * 2
def baseEnd_4169433 : Nat := 158586902645754874660195

theorem tailTrace_4169433 : CollatzResearch.WordTrace tailWord_4169433 prefixEnd_4169433 158586902645754874660195 := by
  unfold tailWord_4169433
  simp only [CollatzResearch.WordTrace]
  refine ⟨152071714703863798309728953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101381143135909198873152635 152071714703863798309728953)
  ·
    refine ⟨114053786027897848732296715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152071714703863798309728953 114053786027897848732296715)
    ·
      refine ⟨171080679041846773098445073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114053786027897848732296715 171080679041846773098445073)
      ·
        refine ⟨128310509281385079823833805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171080679041846773098445073 128310509281385079823833805)
        ·
          refine ⟨48116440980519404933937677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128310509281385079823833805 48116440980519404933937677)
          ·
            refine ⟨18043665367694776850226629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48116440980519404933937677 18043665367694776850226629)
            ·
              refine ⟨3383187256442770659417493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18043665367694776850226629 3383187256442770659417493)
              ·
                refine ⟨158586902645754874660195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3383187256442770659417493 158586902645754874660195)
                ·
                  rfl

theorem cell22_4169433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 6].length) (baseStart_4169433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169433 prefixEnd_4169433 := by exact prefixLift 4169433
  have htrace : WordTrace (prefixWord ++ tailWord_4169433) baseStart_4169433 baseEnd_4169433 := by
    simpa [prefixWord, tailWord_4169433, baseEnd_4169433] using wordTrace_append hprefix tailTrace_4169433
  have hstable : (prefixWord ++ tailWord_4169433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169433).length < 2 ^ (prefixWord ++ tailWord_4169433).sum := by decide
  have hdescent : baseEnd_4169433 < baseStart_4169433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169557 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 4]
def baseStart_4169557 : Nat := 118140960795 + 4169557 * 2 ^ 59
def prefixEnd_4169557 : Nat := 4983230072969 + 3 ^ 40 * 4169557 * 2
def baseEnd_4169557 : Nat := 475774857181966293947125

theorem tailTrace_4169557 : CollatzResearch.WordTrace tailWord_4169557 prefixEnd_4169557 475774857181966293947125 := by
  unfold tailWord_4169557
  simp only [CollatzResearch.WordTrace]
  refine ⟨152076237355414567487242925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101384158236943044991495283 152076237355414567487242925)
  ·
    refine ⟨57028589008280462807716097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152076237355414567487242925 57028589008280462807716097)
    ·
      refine ⟨42771441756210347105787073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57028589008280462807716097 42771441756210347105787073)
      ·
        refine ⟨32078581317157760329340305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42771441756210347105787073 32078581317157760329340305)
        ·
          refine ⟨24058935987868320247005229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32078581317157760329340305 24058935987868320247005229)
          ·
            refine ⟨9022100995450620092626961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24058935987868320247005229 9022100995450620092626961)
            ·
              refine ⟨6766575746587965069470221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9022100995450620092626961 6766575746587965069470221)
              ·
                refine ⟨2537465904970486901051333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6766575746587965069470221 2537465904970486901051333)
                ·
                  refine ⟨475774857181966293947125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537465904970486901051333 475774857181966293947125)
                  ·
                    rfl

theorem cell22_4169557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_4169557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169557 prefixEnd_4169557 := by exact prefixLift 4169557
  have htrace : WordTrace (prefixWord ++ tailWord_4169557) baseStart_4169557 baseEnd_4169557 := by
    simpa [prefixWord, tailWord_4169557, baseEnd_4169557] using wordTrace_append hprefix tailTrace_4169557
  have hstable : (prefixWord ++ tailWord_4169557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169557).length < 2 ^ (prefixWord ++ tailWord_4169557).sum := by decide
  have hdescent : baseEnd_4169557 < baseStart_4169557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169559 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 1, 4]
def baseStart_4169559 : Nat := 118140960795 + 4169559 * 2 ^ 59
def prefixEnd_4169559 : Nat := 4983230072969 + 3 ^ 40 * 4169559 * 2
def baseEnd_4169559 : Nat := 1427325256186771543291369

theorem tailTrace_4169559 : CollatzResearch.WordTrace tailWord_4169559 prefixEnd_4169559 1427325256186771543291369 := by
  unfold tailWord_4169559
  simp only [CollatzResearch.WordTrace]
  refine ⟨152076310301407321828815731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101384206867604881219210487 152076310301407321828815731)
  ·
    refine ⟨228114465452110982743223597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152076310301407321828815731 228114465452110982743223597)
    ·
      refine ⟨85542924544541618528708849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228114465452110982743223597 85542924544541618528708849)
      ·
        refine ⟨64157193408406213896531637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85542924544541618528708849 64157193408406213896531637)
        ·
          refine ⟨6014736882038082552799841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64157193408406213896531637 6014736882038082552799841)
          ·
            refine ⟨4511052661528561914599881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6014736882038082552799841 4511052661528561914599881)
            ·
              refine ⟨3383289496146421435949911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511052661528561914599881 3383289496146421435949911)
              ·
                refine ⟨5074934244219632153924867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383289496146421435949911 5074934244219632153924867)
                ·
                  refine ⟨7612401366329448230887301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074934244219632153924867 7612401366329448230887301)
                  ·
                    refine ⟨1427325256186771543291369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7612401366329448230887301 1427325256186771543291369)
                    ·
                      rfl

theorem cell22_4169559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_4169559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169559 prefixEnd_4169559 := by exact prefixLift 4169559
  have htrace : WordTrace (prefixWord ++ tailWord_4169559) baseStart_4169559 baseEnd_4169559 := by
    simpa [prefixWord, tailWord_4169559, baseEnd_4169559] using wordTrace_append hprefix tailTrace_4169559
  have hstable : (prefixWord ++ tailWord_4169559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169559).length < 2 ^ (prefixWord ++ tailWord_4169559).sum := by decide
  have hdescent : baseEnd_4169559 < baseStart_4169559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169568 : List Nat := [2, 1, 1, 3, 3, 3, 9]
def baseStart_4169568 : Nat := 118140960795 + 4169568 * 2 ^ 59
def prefixEnd_4169568 : Nat := 4983230072969 + 3 ^ 40 * 4169568 * 2
def baseEnd_4169568 : Nat := 52864012484099945178383

theorem tailTrace_4169568 : CollatzResearch.WordTrace tailWord_4169568 prefixEnd_4169568 52864012484099945178383 := by
  unfold tailWord_4169568
  simp only [CollatzResearch.WordTrace]
  refine ⟨76038319279187358182946679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101384425705583144243928905 76038319279187358182946679)
  ·
    refine ⟨114057478918781037274420019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76038319279187358182946679 114057478918781037274420019)
    ·
      refine ⟨171086218378171555911630029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114057478918781037274420019 171086218378171555911630029)
      ·
        refine ⟨64157331891814333466861261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171086218378171555911630029 64157331891814333466861261)
        ·
          refine ⟨24058999459430375050072973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64157331891814333466861261 24058999459430375050072973)
          ·
            refine ⟨9022124797286390643777365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24058999459430375050072973 9022124797286390643777365)
            ·
              refine ⟨52864012484099945178383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9022124797286390643777365 52864012484099945178383)
              ·
                rfl

theorem cell22_4169568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 9].length) (baseStart_4169568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169568 prefixEnd_4169568 := by exact prefixLift 4169568
  have htrace : WordTrace (prefixWord ++ tailWord_4169568) baseStart_4169568 baseEnd_4169568 := by
    simpa [prefixWord, tailWord_4169568, baseEnd_4169568] using wordTrace_append hprefix tailTrace_4169568
  have hstable : (prefixWord ++ tailWord_4169568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169568).length < 2 ^ (prefixWord ++ tailWord_4169568).sum := by decide
  have hdescent : baseEnd_4169568 < baseStart_4169568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169572 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_4169572 : Nat := 118140960795 + 4169572 * 2 ^ 59
def prefixEnd_4169572 : Nat := 4983230072969 + 3 ^ 40 * 4169572 * 2
def baseEnd_4169572 : Nat := 1427329706352443842716329

theorem tailTrace_4169572 : CollatzResearch.WordTrace tailWord_4169572 prefixEnd_4169572 1427329706352443842716329 := by
  unfold tailWord_4169572
  simp only [CollatzResearch.WordTrace]
  refine ⟨76038392225180112524519485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101384522966906816699359313 76038392225180112524519485)
  ·
    refine ⟨28514397084442542196694807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76038392225180112524519485 28514397084442542196694807)
    ·
      refine ⟨42771595626663813295042211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28514397084442542196694807 42771595626663813295042211)
      ·
        refine ⟨64157393439995719942563317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42771595626663813295042211 64157393439995719942563317)
        ·
          refine ⟨6014755634999598744615311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64157393439995719942563317 6014755634999598744615311)
          ·
            refine ⟨9022133452499398116922967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014755634999598744615311 9022133452499398116922967)
            ·
              refine ⟨13533200178749097175384451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9022133452499398116922967 13533200178749097175384451)
              ·
                refine ⟨20299800268123645763076677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13533200178749097175384451 20299800268123645763076677)
                ·
                  refine ⟨3806212550273183580576877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20299800268123645763076677 3806212550273183580576877)
                  ·
                    refine ⟨1427329706352443842716329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806212550273183580576877 1427329706352443842716329)
                    ·
                      rfl

theorem cell22_4169572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_4169572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169572 prefixEnd_4169572 := by exact prefixLift 4169572
  have htrace : WordTrace (prefixWord ++ tailWord_4169572) baseStart_4169572 baseEnd_4169572 := by
    simpa [prefixWord, tailWord_4169572, baseEnd_4169572] using wordTrace_append hprefix tailTrace_4169572
  have hstable : (prefixWord ++ tailWord_4169572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169572).length < 2 ^ (prefixWord ++ tailWord_4169572).sum := by decide
  have hdescent : baseEnd_4169572 < baseStart_4169572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169589 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4169589 : Nat := 118140960795 + 4169589 * 2 ^ 59
def prefixEnd_4169589 : Nat := 4983230072969 + 3 ^ 40 * 4169589 * 2
def baseEnd_4169589 : Nat := 1427335525799861465041277

theorem tailTrace_4169589 : CollatzResearch.WordTrace tailWord_4169589 prefixEnd_4169589 1427335525799861465041277 := by
  unfold tailWord_4169589
  simp only [CollatzResearch.WordTrace]
  refine ⟨152077404491298636952407821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101384936327532424634938547 152077404491298636952407821)
  ·
    refine ⟨57029026684236988857152933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152077404491298636952407821 57029026684236988857152933)
    ·
      refine ⟨10692942503294435410716175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57029026684236988857152933 10692942503294435410716175)
      ·
        refine ⟨16039413754941653116074263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692942503294435410716175 16039413754941653116074263)
        ·
          refine ⟨24059120632412479674111395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16039413754941653116074263 24059120632412479674111395)
          ·
            refine ⟨36088680948618719511167093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24059120632412479674111395 36088680948618719511167093)
            ·
              refine ⟨3383313838933004954171915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36088680948618719511167093 3383313838933004954171915)
              ·
                refine ⟨5074970758399507431257873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383313838933004954171915 5074970758399507431257873)
                ·
                  refine ⟨3806228068799630573443405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074970758399507431257873 3806228068799630573443405)
                  ·
                    refine ⟨1427335525799861465041277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806228068799630573443405 1427335525799861465041277)
                    ·
                      rfl

theorem cell22_4169589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4169589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169589 prefixEnd_4169589 := by exact prefixLift 4169589
  have htrace : WordTrace (prefixWord ++ tailWord_4169589) baseStart_4169589 baseEnd_4169589 := by
    simpa [prefixWord, tailWord_4169589, baseEnd_4169589] using wordTrace_append hprefix tailTrace_4169589
  have hstable : (prefixWord ++ tailWord_4169589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169589).length < 2 ^ (prefixWord ++ tailWord_4169589).sum := by decide
  have hdescent : baseEnd_4169589 < baseStart_4169589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169600 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_4169600 : Nat := 118140960795 + 4169600 * 2 ^ 59
def prefixEnd_4169600 : Nat := 4983230072969 + 3 ^ 40 * 4169600 * 2
def baseEnd_4169600 : Nat := 1427339291324661103016243

theorem tailTrace_4169600 : CollatzResearch.WordTrace tailWord_4169600 prefixEnd_4169600 1427339291324661103016243 := by
  unfold tailWord_4169600
  simp only [CollatzResearch.WordTrace]
  refine ⟨76038902847129392915529127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101385203796172523887372169 76038902847129392915529127)
  ·
    refine ⟨114058354270694089373293691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76038902847129392915529127 114058354270694089373293691)
    ·
      refine ⟨171087531406041134059940537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114058354270694089373293691 171087531406041134059940537)
      ·
        refine ⟨128315648554530850544955403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171087531406041134059940537 128315648554530850544955403)
        ·
          refine ⟨192473472831796275817433105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128315648554530850544955403 192473472831796275817433105)
          ·
            refine ⟨144355104623847206863074829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192473472831796275817433105 144355104623847206863074829)
            ·
              refine ⟨54133164233942702573653061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144355104623847206863074829 54133164233942702573653061)
              ·
                refine ⟨10149968293864256732559949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54133164233942702573653061 10149968293864256732559949)
                ·
                  refine ⟨3806238110199096274709981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10149968293864256732559949 3806238110199096274709981)
                  ·
                    refine ⟨1427339291324661103016243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806238110199096274709981 1427339291324661103016243)
                    ·
                      rfl

theorem cell22_4169600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_4169600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169600 prefixEnd_4169600 := by exact prefixLift 4169600
  have htrace : WordTrace (prefixWord ++ tailWord_4169600) baseStart_4169600 baseEnd_4169600 := by
    simpa [prefixWord, tailWord_4169600, baseEnd_4169600] using wordTrace_append hprefix tailTrace_4169600
  have hstable : (prefixWord ++ tailWord_4169600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169600).length < 2 ^ (prefixWord ++ tailWord_4169600).sum := by decide
  have hdescent : baseEnd_4169600 < baseStart_4169600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169640 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4169640 : Nat := 118140960795 + 4169640 * 2 ^ 59
def prefixEnd_4169640 : Nat := 4983230072969 + 3 ^ 40 * 4169640 * 2
def baseEnd_4169640 : Nat := 1427352984142114332016121

theorem tailTrace_4169640 : CollatzResearch.WordTrace tailWord_4169640 prefixEnd_4169640 1427352984142114332016121 := by
  unfold tailWord_4169640
  simp only [CollatzResearch.WordTrace]
  refine ⟨76039632307056936331257187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101386176409409248441676249 76039632307056936331257187)
  ·
    refine ⟨114059448460585404496885781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76039632307056936331257187 114059448460585404496885781)
    ·
      refine ⟨5346536646589940835791521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114059448460585404496885781 5346536646589940835791521)
      ·
        refine ⟨4009902484942455626843641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5346536646589940835791521 4009902484942455626843641)
        ·
          refine ⟨3007426863706841720132731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4009902484942455626843641 3007426863706841720132731)
          ·
            refine ⟨4511140295560262580199097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007426863706841720132731 4511140295560262580199097)
            ·
              refine ⟨3383355221670196935149323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511140295560262580199097 3383355221670196935149323)
              ·
                refine ⟨5075032832505295402723985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383355221670196935149323 5075032832505295402723985)
                ·
                  refine ⟨3806274624378971552042989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5075032832505295402723985 3806274624378971552042989)
                  ·
                    refine ⟨1427352984142114332016121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806274624378971552042989 1427352984142114332016121)
                    ·
                      rfl

theorem cell22_4169640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4169640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169640 prefixEnd_4169640 := by exact prefixLift 4169640
  have htrace : WordTrace (prefixWord ++ tailWord_4169640) baseStart_4169640 baseEnd_4169640 := by
    simpa [prefixWord, tailWord_4169640, baseEnd_4169640] using wordTrace_append hprefix tailTrace_4169640
  have hstable : (prefixWord ++ tailWord_4169640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169640).length < 2 ^ (prefixWord ++ tailWord_4169640).sum := by decide
  have hdescent : baseEnd_4169640 < baseStart_4169640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169709 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4169709 : Nat := 118140960795 + 4169709 * 2 ^ 59
def prefixEnd_4169709 : Nat := 4983230072969 + 3 ^ 40 * 4169709 * 2
def baseEnd_4169709 : Nat := 475792201417407050680303

theorem tailTrace_4169709 : CollatzResearch.WordTrace tailWord_4169709 prefixEnd_4169709 475792201417407050680303 := by
  unfold tailWord_4169709
  simp only [CollatzResearch.WordTrace]
  refine ⟨152081781250863897446776181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101387854167242598297850787 152081781250863897446776181)
  ·
    refine ⟨14257666992268490385635267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152081781250863897446776181 14257666992268490385635267)
    ·
      refine ⟨21386500488402735578452901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14257666992268490385635267 21386500488402735578452901)
      ·
        refine ⟨4009968841575512920959919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21386500488402735578452901 4009968841575512920959919)
        ·
          refine ⟨6014953262363269381439879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009968841575512920959919 6014953262363269381439879)
          ·
            refine ⟨9022429893544904072159819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014953262363269381439879 9022429893544904072159819)
            ·
              refine ⟨13533644840317356108239729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9022429893544904072159819 13533644840317356108239729)
              ·
                refine ⟨10150233630238017081179797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13533644840317356108239729 10150233630238017081179797)
                ·
                  refine ⟨475792201417407050680303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10150233630238017081179797 475792201417407050680303)
                  ·
                    rfl

theorem cell22_4169709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4169709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169709 prefixEnd_4169709 := by exact prefixLift 4169709
  have htrace : WordTrace (prefixWord ++ tailWord_4169709) baseStart_4169709 baseEnd_4169709 := by
    simpa [prefixWord, tailWord_4169709, baseEnd_4169709] using wordTrace_append hprefix tailTrace_4169709
  have hstable : (prefixWord ++ tailWord_4169709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169709).length < 2 ^ (prefixWord ++ tailWord_4169709).sum := by decide
  have hdescent : baseEnd_4169709 < baseStart_4169709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169726 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_4169726 : Nat := 118140960795 + 4169726 * 2 ^ 59
def prefixEnd_4169726 : Nat := 4983230072969 + 3 ^ 40 * 4169726 * 2
def baseEnd_4169726 : Nat := 475794141233212924788619

theorem tailTrace_4169726 : CollatzResearch.WordTrace tailWord_4169726 prefixEnd_4169726 475794141233212924788619 := by
  unfold tailWord_4169726
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010300161475288668768129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101388267527868206233430021 19010300161475288668768129)
  ·
    refine ⟨14257725121106466501576097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19010300161475288668768129 14257725121106466501576097)
    ·
      refine ⟨10693293840829849876182073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14257725121106466501576097 10693293840829849876182073)
      ·
        refine ⟨8019970380622387407136555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10693293840829849876182073 8019970380622387407136555)
        ·
          refine ⟨12029955570933581110704833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8019970380622387407136555 12029955570933581110704833)
          ·
            refine ⟨9022466678200185833028625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12029955570933581110704833 9022466678200185833028625)
            ·
              refine ⟨6766850008650139374771469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9022466678200185833028625 6766850008650139374771469)
              ·
                refine ⟨2537568753243802265539301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6766850008650139374771469 2537568753243802265539301)
                ·
                  refine ⟨475794141233212924788619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537568753243802265539301 475794141233212924788619)
                  ·
                    rfl

theorem cell22_4169726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_4169726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169726 prefixEnd_4169726 := by exact prefixLift 4169726
  have htrace : WordTrace (prefixWord ++ tailWord_4169726) baseStart_4169726 baseEnd_4169726 := by
    simpa [prefixWord, tailWord_4169726, baseEnd_4169726] using wordTrace_append hprefix tailTrace_4169726
  have hstable : (prefixWord ++ tailWord_4169726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169726).length < 2 ^ (prefixWord ++ tailWord_4169726).sum := by decide
  have hdescent : baseEnd_4169726 < baseStart_4169726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169782 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_4169782 : Nat := 118140960795 + 4169782 * 2 ^ 59
def prefixEnd_4169782 : Nat := 4983230072969 + 3 ^ 40 * 4169782 * 2
def baseEnd_4169782 : Nat := 475800531214691098321895

theorem tailTrace_4169782 : CollatzResearch.WordTrace tailWord_4169782 prefixEnd_4169782 475800531214691098321895 := by
  unfold tailWord_4169782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505277736224964432136475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101389629186399620609455733 9505277736224964432136475)
  ·
    refine ⟨14257916604337446648204713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9505277736224964432136475 14257916604337446648204713)
    ·
      refine ⟨10693437453253084986153535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14257916604337446648204713 10693437453253084986153535)
      ·
        refine ⟨16040156179879627479230303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10693437453253084986153535 16040156179879627479230303)
        ·
          refine ⟨24060234269819441218845455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16040156179879627479230303 24060234269819441218845455)
          ·
            refine ⟨36090351404729161828268183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24060234269819441218845455 36090351404729161828268183)
            ·
              refine ⟨54135527107093742742402275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36090351404729161828268183 54135527107093742742402275)
              ·
                refine ⟨81203290660640614113603413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54135527107093742742402275 81203290660640614113603413)
                ·
                  refine ⟨475800531214691098321895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81203290660640614113603413 475800531214691098321895)
                  ·
                    rfl

theorem cell22_4169782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_4169782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169782 prefixEnd_4169782 := by exact prefixLift 4169782
  have htrace : WordTrace (prefixWord ++ tailWord_4169782) baseStart_4169782 baseEnd_4169782 := by
    simpa [prefixWord, tailWord_4169782, baseEnd_4169782] using wordTrace_append hprefix tailTrace_4169782
  have hstable : (prefixWord ++ tailWord_4169782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169782).length < 2 ^ (prefixWord ++ tailWord_4169782).sum := by decide
  have hdescent : baseEnd_4169782 < baseStart_4169782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169812 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_4169812 : Nat := 118140960795 + 4169812 * 2 ^ 59
def prefixEnd_4169812 : Nat := 4983230072969 + 3 ^ 40 * 4169812 * 2
def baseEnd_4169812 : Nat := 1427411863257163216715593

theorem tailTrace_4169812 : CollatzResearch.WordTrace tailWord_4169812 prefixEnd_4169812 1427411863257163216715593 := by
  unfold tailWord_4169812
  simp only [CollatzResearch.WordTrace]
  refine ⟨76042768984745373018887845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101390358646327164025183793 76042768984745373018887845)
  ·
    refine ⟨14258019184639757441041471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76042768984745373018887845 14258019184639757441041471)
    ·
      refine ⟨21387028776959636161562207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14258019184639757441041471 21387028776959636161562207)
      ·
        refine ⟨32080543165439454242343311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21387028776959636161562207 32080543165439454242343311)
        ·
          refine ⟨48120814748159181363514967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32080543165439454242343311 48120814748159181363514967)
          ·
            refine ⟨72181222122238772045272451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48120814748159181363514967 72181222122238772045272451)
            ·
              refine ⟨108271833183358158067908677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72181222122238772045272451 108271833183358158067908677)
              ·
                refine ⟨20300968721879654637732877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108271833183358158067908677 20300968721879654637732877)
                ·
                  refine ⟨7612863270704870489149829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20300968721879654637732877 7612863270704870489149829)
                  ·
                    refine ⟨1427411863257163216715593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7612863270704870489149829 1427411863257163216715593)
                    ·
                      rfl

theorem cell22_4169812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_4169812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169812 prefixEnd_4169812 := by exact prefixLift 4169812
  have htrace : WordTrace (prefixWord ++ tailWord_4169812) baseStart_4169812 baseEnd_4169812 := by
    simpa [prefixWord, tailWord_4169812, baseEnd_4169812] using wordTrace_append hprefix tailTrace_4169812
  have hstable : (prefixWord ++ tailWord_4169812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169812).length < 2 ^ (prefixWord ++ tailWord_4169812).sum := by decide
  have hdescent : baseEnd_4169812 < baseStart_4169812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169829 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_4169829 : Nat := 118140960795 + 4169829 * 2 ^ 59
def prefixEnd_4169829 : Nat := 4983230072969 + 3 ^ 40 * 4169829 * 2
def baseEnd_4169829 : Nat := 1427417682704580839040541

theorem tailTrace_4169829 : CollatzResearch.WordTrace tailWord_4169829 prefixEnd_4169829 1427417682704580839040541 := by
  unfold tailWord_4169829
  simp only [CollatzResearch.WordTrace]
  refine ⟨152086158010429157941144541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101390772006952771960763027 152086158010429157941144541)
  ·
    refine ⟨57032309253910934227929203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152086158010429157941144541 57032309253910934227929203)
    ·
      refine ⟨85548463880866401341893805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57032309253910934227929203 85548463880866401341893805)
      ·
        refine ⟨32080673955324900503210177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85548463880866401341893805 32080673955324900503210177)
        ·
          refine ⟨24060505466493675377407633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32080673955324900503210177 24060505466493675377407633)
          ·
            refine ⟨18045379099870256533055725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24060505466493675377407633 18045379099870256533055725)
            ·
              refine ⟨6767017162451346199895897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18045379099870256533055725 6767017162451346199895897)
              ·
                refine ⟨5075262871838509649921923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6767017162451346199895897 5075262871838509649921923)
                ·
                  refine ⟨7612894307757764474882885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075262871838509649921923 7612894307757764474882885)
                  ·
                    refine ⟨1427417682704580839040541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7612894307757764474882885 1427417682704580839040541)
                    ·
                      rfl

theorem cell22_4169829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_4169829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169829 prefixEnd_4169829 := by exact prefixLift 4169829
  have htrace : WordTrace (prefixWord ++ tailWord_4169829) baseStart_4169829 baseEnd_4169829 := by
    simpa [prefixWord, tailWord_4169829, baseEnd_4169829] using wordTrace_append hprefix tailTrace_4169829
  have hstable : (prefixWord ++ tailWord_4169829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169829).length < 2 ^ (prefixWord ++ tailWord_4169829).sum := by decide
  have hdescent : baseEnd_4169829 < baseStart_4169829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169842 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_4169842 : Nat := 118140960795 + 4169842 * 2 ^ 59
def prefixEnd_4169842 : Nat := 4983230072969 + 3 ^ 40 * 4169842 * 2
def baseEnd_4169842 : Nat := 1427422132870253138465501

theorem tailTrace_4169842 : CollatzResearch.WordTrace tailWord_4169842 prefixEnd_4169842 1427422132870253138465501 := by
  unfold tailWord_4169842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38021658039845515290341945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101391088106254707440911853 38021658039845515290341945)
  ·
    refine ⟨28516243529884136467756459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38021658039845515290341945 28516243529884136467756459)
    ·
      refine ⟨42774365294826204701634689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28516243529884136467756459 42774365294826204701634689)
      ·
        refine ⟨32080773971119653526226017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42774365294826204701634689 32080773971119653526226017)
        ·
          refine ⟨24060580478339740144669513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32080773971119653526226017 24060580478339740144669513)
          ·
            refine ⟨18045435358754805108502135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24060580478339740144669513 18045435358754805108502135)
            ·
              refine ⟨27068153038132207662753203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045435358754805108502135 27068153038132207662753203)
              ·
                refine ⟨40602229557198311494129805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27068153038132207662753203 40602229557198311494129805)
                ·
                  refine ⟨15225836083949366810298677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40602229557198311494129805 15225836083949366810298677)
                  ·
                    refine ⟨1427422132870253138465501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15225836083949366810298677 1427422132870253138465501)
                    ·
                      rfl

theorem cell22_4169842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_4169842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169842 prefixEnd_4169842 := by exact prefixLift 4169842
  have htrace : WordTrace (prefixWord ++ tailWord_4169842) baseStart_4169842 baseEnd_4169842 := by
    simpa [prefixWord, tailWord_4169842, baseEnd_4169842] using wordTrace_append hprefix tailTrace_4169842
  have hstable : (prefixWord ++ tailWord_4169842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169842).length < 2 ^ (prefixWord ++ tailWord_4169842).sum := by decide
  have hdescent : baseEnd_4169842 < baseStart_4169842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169859 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 2, 3]
def baseStart_4169859 : Nat := 118140960795 + 4169859 * 2 ^ 59
def prefixEnd_4169859 : Nat := 4983230072969 + 3 ^ 40 * 4169859 * 2
def baseEnd_4169859 : Nat := 1427427952317670760790449

theorem tailTrace_4169859 : CollatzResearch.WordTrace tailWord_4169859 prefixEnd_4169859 1427427952317670760790449 := by
  unfold tailWord_4169859
  simp only [CollatzResearch.WordTrace]
  refine ⟨152087252200320473064736631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101391501466880315376491087 152087252200320473064736631)
  ·
    refine ⟨228130878300480709597104947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152087252200320473064736631 228130878300480709597104947)
    ·
      refine ⟨342196317450721064395657421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228130878300480709597104947 342196317450721064395657421)
      ·
        refine ⟨128323619044020399148371533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342196317450721064395657421 128323619044020399148371533)
        ·
          refine ⟨48121357141507649680639325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128323619044020399148371533 48121357141507649680639325)
          ·
            refine ⟨18045508928065368630239747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48121357141507649680639325 18045508928065368630239747)
            ·
              refine ⟨27068263392098052945359621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045508928065368630239747 27068263392098052945359621)
              ·
                refine ⟨5075299386018384927254929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27068263392098052945359621 5075299386018384927254929)
                ·
                  refine ⟨3806474539513788695441197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5075299386018384927254929 3806474539513788695441197)
                  ·
                    refine ⟨1427427952317670760790449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806474539513788695441197 1427427952317670760790449)
                    ·
                      rfl

theorem cell22_4169859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 3].length) (baseStart_4169859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169859 prefixEnd_4169859 := by exact prefixLift 4169859
  have htrace : WordTrace (prefixWord ++ tailWord_4169859) baseStart_4169859 baseEnd_4169859 := by
    simpa [prefixWord, tailWord_4169859, baseEnd_4169859] using wordTrace_append hprefix tailTrace_4169859
  have hstable : (prefixWord ++ tailWord_4169859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169859).length < 2 ^ (prefixWord ++ tailWord_4169859).sum := by decide
  have hdescent : baseEnd_4169859 < baseStart_4169859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169861 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 4]
def baseStart_4169861 : Nat := 118140960795 + 4169861 * 2 ^ 59
def prefixEnd_4169861 : Nat := 4983230072969 + 3 ^ 40 * 4169861 * 2
def baseEnd_4169861 : Nat := 475809545652847807413481

theorem tailTrace_4169861 : CollatzResearch.WordTrace tailWord_4169861 prefixEnd_4169861 475809545652847807413481 := by
  unfold tailWord_4169861
  simp only [CollatzResearch.WordTrace]
  refine ⟨152087325146313227406309437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101391550097542151604206291 152087325146313227406309437)
  ·
    refine ⟨57032746929867460277366039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152087325146313227406309437 57032746929867460277366039)
    ·
      refine ⟨85549120394801190416049059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57032746929867460277366039 85549120394801190416049059)
      ·
        refine ⟨128323680592201785624073589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85549120394801190416049059 128323680592201785624073589)
        ·
          refine ⟨12030345055518917402256899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128323680592201785624073589 12030345055518917402256899)
          ·
            refine ⟨18045517583278376103385349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030345055518917402256899 18045517583278376103385349)
            ·
              refine ⟨3383534546864695519384753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18045517583278376103385349 3383534546864695519384753)
              ·
                refine ⟨2537650910148521639538565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3383534546864695519384753 2537650910148521639538565)
                ·
                  refine ⟨475809545652847807413481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537650910148521639538565 475809545652847807413481)
                  ·
                    rfl

theorem cell22_4169861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_4169861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169861 prefixEnd_4169861 := by exact prefixLift 4169861
  have htrace : WordTrace (prefixWord ++ tailWord_4169861) baseStart_4169861 baseEnd_4169861 := by
    simpa [prefixWord, tailWord_4169861, baseEnd_4169861] using wordTrace_append hprefix tailTrace_4169861
  have hstable : (prefixWord ++ tailWord_4169861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169861).length < 2 ^ (prefixWord ++ tailWord_4169861).sum := by decide
  have hdescent : baseEnd_4169861 < baseStart_4169861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169889 : List Nat := [1, 2, 3, 3, 1, 3, 3, 6]
def baseStart_4169889 : Nat := 118140960795 + 4169889 * 2 ^ 59
def prefixEnd_4169889 : Nat := 4983230072969 + 3 ^ 40 * 4169889 * 2
def baseEnd_4169889 : Nat := 158604246881195631393373

theorem tailTrace_4169889 : CollatzResearch.WordTrace tailWord_4169889 prefixEnd_4169889 158604246881195631393373 := by
  unfold tailWord_4169889
  simp only [CollatzResearch.WordTrace]
  refine ⟨152088346390211788188328721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101392230926807858792219147 152088346390211788188328721)
  ·
    refine ⟨114066259792658841141246541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152088346390211788188328721 114066259792658841141246541)
    ·
      refine ⟨42774847422247065427967453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114066259792658841141246541 42774847422247065427967453)
      ·
        refine ⟨16040567783342649535487795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42774847422247065427967453 16040567783342649535487795)
        ·
          refine ⟨24060851675013974303231693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16040567783342649535487795 24060851675013974303231693)
          ·
            refine ⟨9022819378130240363711885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24060851675013974303231693 9022819378130240363711885)
            ·
              refine ⟨3383557266798840136391957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9022819378130240363711885 3383557266798840136391957)
              ·
                refine ⟨158604246881195631393373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3383557266798840136391957 158604246881195631393373)
                ·
                  rfl

theorem cell22_4169889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 6].length) (baseStart_4169889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169889 prefixEnd_4169889 := by exact prefixLift 4169889
  have htrace : WordTrace (prefixWord ++ tailWord_4169889) baseStart_4169889 baseEnd_4169889 := by
    simpa [prefixWord, tailWord_4169889, baseEnd_4169889] using wordTrace_append hprefix tailTrace_4169889
  have hstable : (prefixWord ++ tailWord_4169889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169889).length < 2 ^ (prefixWord ++ tailWord_4169889).sum := by decide
  have hdescent : baseEnd_4169889 < baseStart_4169889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169964 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_4169964 : Nat := 118140960795 + 4169964 * 2 ^ 59
def prefixEnd_4169964 : Nat := 4983230072969 + 3 ^ 40 * 4169964 * 2
def baseEnd_4169964 : Nat := 1427463895963485486915127

theorem tailTrace_4169964 : CollatzResearch.WordTrace tailWord_4169964 prefixEnd_4169964 1427463895963485486915127 := by
  unfold tailWord_4169964
  simp only [CollatzResearch.WordTrace]
  refine ⟨76045540932470037998654473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101394054576626717331539297 76045540932470037998654473)
  ·
    refine ⟨57034155699352528498990855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76045540932470037998654473 57034155699352528498990855)
    ·
      refine ⟨85551233549028792748486283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57034155699352528498990855 85551233549028792748486283)
      ·
        refine ⟨128326850323543189122729425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85551233549028792748486283 128326850323543189122729425)
        ·
          refine ⟨96245137742657391842047069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128326850323543189122729425 96245137742657391842047069)
          ·
            refine ⟨36091926653496521940767651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96245137742657391842047069 36091926653496521940767651)
            ·
              refine ⟨54137889980244782911151477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36091926653496521940767651 54137889980244782911151477)
              ·
                refine ⟨5075427185647948397920451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54137889980244782911151477 5075427185647948397920451)
                ·
                  refine ⟨7613140778471922596880677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075427185647948397920451 7613140778471922596880677)
                  ·
                    refine ⟨1427463895963485486915127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7613140778471922596880677 1427463895963485486915127)
                    ·
                      rfl

theorem cell22_4169964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_4169964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169964 prefixEnd_4169964 := by exact prefixLift 4169964
  have htrace : WordTrace (prefixWord ++ tailWord_4169964) baseStart_4169964 baseEnd_4169964 := by
    simpa [prefixWord, tailWord_4169964, baseEnd_4169964] using wordTrace_append hprefix tailTrace_4169964
  have hstable : (prefixWord ++ tailWord_4169964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169964).length < 2 ^ (prefixWord ++ tailWord_4169964).sum := by decide
  have hdescent : baseEnd_4169964 < baseStart_4169964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169977 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_4169977 : Nat := 118140960795 + 4169977 * 2 ^ 59
def prefixEnd_4169977 : Nat := 4983230072969 + 3 ^ 40 * 4169977 * 2
def baseEnd_4169977 : Nat := 1427468346129157786340087

theorem tailTrace_4169977 : CollatzResearch.WordTrace tailWord_4169977 prefixEnd_4169977 1427468346129157786340087 := by
  unfold tailWord_4169977
  simp only [CollatzResearch.WordTrace]
  refine ⟨152091556013892979217532185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101394370675928652811688123 152091556013892979217532185)
  ·
    refine ⟨114068667010419734413149139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152091556013892979217532185 114068667010419734413149139)
    ·
      refine ⟨171103000515629601619723709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114068667010419734413149139 171103000515629601619723709)
      ·
        refine ⟨64163625193361100607396391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171103000515629601619723709 64163625193361100607396391)
        ·
          refine ⟨96245437790041650911094587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64163625193361100607396391 96245437790041650911094587)
          ·
            refine ⟨144368156685062476366641881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96245437790041650911094587 144368156685062476366641881)
            ·
              refine ⟨108276117513796857274981411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144368156685062476366641881 108276117513796857274981411)
              ·
                refine ⟨162414176270695285912472117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108276117513796857274981411 162414176270695285912472117)
                ·
                  refine ⟨15226329025377683054294261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162414176270695285912472117 15226329025377683054294261)
                  ·
                    refine ⟨1427468346129157786340087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15226329025377683054294261 1427468346129157786340087)
                    ·
                      rfl

theorem cell22_4169977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_4169977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4169977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4169977 prefixEnd_4169977 := by exact prefixLift 4169977
  have htrace : WordTrace (prefixWord ++ tailWord_4169977) baseStart_4169977 baseEnd_4169977 := by
    simpa [prefixWord, tailWord_4169977, baseEnd_4169977] using wordTrace_append hprefix tailTrace_4169977
  have hstable : (prefixWord ++ tailWord_4169977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169977).length < 2 ^ (prefixWord ++ tailWord_4169977).sum := by decide
  have hdescent : baseEnd_4169977 < baseStart_4169977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170024 : List Nat := [2, 1, 5, 1, 3, 10]
def baseStart_4170024 : Nat := 118140960795 + 4170024 * 2 ^ 59
def prefixEnd_4170024 : Nat := 4983230072969 + 3 ^ 40 * 4170024 * 2
def baseEnd_4170024 : Nat := 17623264631971176918703

theorem tailTrace_4170024 : CollatzResearch.WordTrace tailWord_4170024 prefixEnd_4170024 17623264631971176918703 := by
  unfold tailWord_4170024
  simp only [CollatzResearch.WordTrace]
  refine ⟨76046635122361353122246563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101395513496481804162995417 76046635122361353122246563)
  ·
    refine ⟨114069952683542029683369845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76046635122361353122246563 114069952683542029683369845)
    ·
      refine ⟨10694058064082065282815923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114069952683542029683369845 10694058064082065282815923)
      ·
        refine ⟨16041087096123097924223885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694058064082065282815923 16041087096123097924223885)
        ·
          refine ⟨6015407661046161721583957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16041087096123097924223885 6015407661046161721583957)
          ·
            refine ⟨17623264631971176918703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6015407661046161721583957 17623264631971176918703)
            ·
              rfl

theorem cell22_4170024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 10].length) (baseStart_4170024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170024 prefixEnd_4170024 := by exact prefixLift 4170024
  have htrace : WordTrace (prefixWord ++ tailWord_4170024) baseStart_4170024 baseEnd_4170024 := by
    simpa [prefixWord, tailWord_4170024, baseEnd_4170024] using wordTrace_append hprefix tailTrace_4170024
  have hstable : (prefixWord ++ tailWord_4170024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170024).length < 2 ^ (prefixWord ++ tailWord_4170024).sum := by decide
  have hdescent : baseEnd_4170024 < baseStart_4170024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170030 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_4170030 : Nat := 118140960795 + 4170030 * 2 ^ 59
def prefixEnd_4170030 : Nat := 4983230072969 + 3 ^ 40 * 4170030 * 2
def baseEnd_4170030 : Nat := 475828829704094438254975

theorem tailTrace_4170030 : CollatzResearch.WordTrace tailWord_4170030 prefixEnd_4170030 475828829704094438254975 := by
  unfold tailWord_4170030
  simp only [CollatzResearch.WordTrace]
  refine ⟨19011686135337621158651443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101395659388467312846141029 19011686135337621158651443)
  ·
    refine ⟨28517529203006431737977165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19011686135337621158651443 28517529203006431737977165)
    ·
      refine ⟨10694073451127411901741437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28517529203006431737977165 10694073451127411901741437)
      ·
        refine ⟨4010277544172779463153039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10694073451127411901741437 4010277544172779463153039)
        ·
          refine ⟨6015416316259169194729559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010277544172779463153039 6015416316259169194729559)
          ·
            refine ⟨9023124474388753792094339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015416316259169194729559 9023124474388753792094339)
            ·
              refine ⟨13534686711583130688141509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023124474388753792094339 13534686711583130688141509)
              ·
                refine ⟨2537753758421837004026533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13534686711583130688141509 2537753758421837004026533)
                ·
                  refine ⟨475828829704094438254975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537753758421837004026533 475828829704094438254975)
                  ·
                    rfl

theorem cell22_4170030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_4170030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170030 prefixEnd_4170030 := by exact prefixLift 4170030
  have htrace : WordTrace (prefixWord ++ tailWord_4170030) baseStart_4170030 baseEnd_4170030 := by
    simpa [prefixWord, tailWord_4170030, baseEnd_4170030] using wordTrace_append hprefix tailTrace_4170030
  have hstable : (prefixWord ++ tailWord_4170030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170030).length < 2 ^ (prefixWord ++ tailWord_4170030).sum := by decide
  have hdescent : baseEnd_4170030 < baseStart_4170030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170039 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 7, 3]
def baseStart_4170039 : Nat := 118140960795 + 4170039 * 2 ^ 59
def prefixEnd_4170039 : Nat := 4983230072969 + 3 ^ 40 * 4170039 * 2
def baseEnd_4170039 : Nat := 1427489569996210291289897

theorem tailTrace_4170039 : CollatzResearch.WordTrace tailWord_4170039 prefixEnd_4170039 1427489569996210291289897 := by
  unfold tailWord_4170039
  simp only [CollatzResearch.WordTrace]
  refine ⟨152093817339668363806289171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101395878226445575870859447 152093817339668363806289171)
  ·
    refine ⟨228140726009502545709433757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152093817339668363806289171 228140726009502545709433757)
    ·
      refine ⟨85552772253563454641037659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228140726009502545709433757 85552772253563454641037659)
      ·
        refine ⟨128329158380345181961556489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85552772253563454641037659 128329158380345181961556489)
        ·
          refine ⟨96246868785258886471167367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128329158380345181961556489 96246868785258886471167367)
          ·
            refine ⟨144370303177888329706751051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96246868785258886471167367 144370303177888329706751051)
            ·
              refine ⟨216555454766832494560126577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144370303177888329706751051 216555454766832494560126577)
              ·
                refine ⟨162416591075124370920094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216555454766832494560126577 162416591075124370920094933)
                ·
                  refine ⟨3806638853323227443439725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162416591075124370920094933 3806638853323227443439725)
                  ·
                    refine ⟨1427489569996210291289897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806638853323227443439725 1427489569996210291289897)
                    ·
                      rfl

theorem cell22_4170039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_4170039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170039 prefixEnd_4170039 := by exact prefixLift 4170039
  have htrace : WordTrace (prefixWord ++ tailWord_4170039) baseStart_4170039 baseEnd_4170039 := by
    simpa [prefixWord, tailWord_4170039, baseEnd_4170039] using wordTrace_append hprefix tailTrace_4170039
  have hstable : (prefixWord ++ tailWord_4170039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170039).length < 2 ^ (prefixWord ++ tailWord_4170039).sum := by decide
  have hdescent : baseEnd_4170039 < baseStart_4170039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170041 : List Nat := [1, 2, 1, 6, 1, 3, 1, 7]
def baseStart_4170041 : Nat := 118140960795 + 4170041 * 2 ^ 59
def prefixEnd_4170041 : Nat := 4983230072969 + 3 ^ 40 * 4170041 * 2
def baseEnd_4170041 : Nat := 158610028293009216971099

theorem tailTrace_4170041 : CollatzResearch.WordTrace tailWord_4170041 prefixEnd_4170041 158610028293009216971099 := by
  unfold tailWord_4170041
  simp only [CollatzResearch.WordTrace]
  refine ⟨152093890285661118147861977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101395926857107412098574651 152093890285661118147861977)
  ·
    refine ⟨114070417714245838610896483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152093890285661118147861977 114070417714245838610896483)
    ·
      refine ⟨171105626571368757916344725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114070417714245838610896483 171105626571368757916344725)
      ·
        refine ⟨8020576245532910527328659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171105626571368757916344725 8020576245532910527328659)
        ·
          refine ⟨12030864368299365790992989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020576245532910527328659 12030864368299365790992989)
          ·
            refine ⟨4511574138112262171622371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12030864368299365790992989 4511574138112262171622371)
            ·
              refine ⟨6767361207168393257433557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511574138112262171622371 6767361207168393257433557)
              ·
                refine ⟨158610028293009216971099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6767361207168393257433557 158610028293009216971099)
                ·
                  rfl

theorem cell22_4170041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 7].length) (baseStart_4170041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170041 prefixEnd_4170041 := by exact prefixLift 4170041
  have htrace : WordTrace (prefixWord ++ tailWord_4170041) baseStart_4170041 baseEnd_4170041 := by
    simpa [prefixWord, tailWord_4170041, baseEnd_4170041] using wordTrace_append hprefix tailTrace_4170041
  have hstable : (prefixWord ++ tailWord_4170041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170041).length < 2 ^ (prefixWord ++ tailWord_4170041).sum := by decide
  have hdescent : baseEnd_4170041 < baseStart_4170041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170084 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_4170084 : Nat := 118140960795 + 4170084 * 2 ^ 59
def prefixEnd_4170084 : Nat := 4983230072969 + 3 ^ 40 * 4170084 * 2
def baseEnd_4170084 : Nat := 1427504974415845173914759

theorem tailTrace_4170084 : CollatzResearch.WordTrace tailWord_4170084 prefixEnd_4170084 1427504974415845173914759 := by
  unfold tailWord_4170084
  simp only [CollatzResearch.WordTrace]
  refine ⟨76047729312252668245838653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101396972416336890994451537 76047729312252668245838653)
  ·
    refine ⟨28517898492094750592189495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76047729312252668245838653 28517898492094750592189495)
    ·
      refine ⟨42776847738142125888284243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28517898492094750592189495 42776847738142125888284243)
      ·
        refine ⟨64165271607213188832426365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42776847738142125888284243 64165271607213188832426365)
        ·
          refine ⟨24061976852704945812159887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64165271607213188832426365 24061976852704945812159887)
          ·
            refine ⟨36092965279057418718239831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24061976852704945812159887 36092965279057418718239831)
            ·
              refine ⟨54139447918586128077359747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36092965279057418718239831 54139447918586128077359747)
              ·
                refine ⟨81209171877879192116039621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54139447918586128077359747 81209171877879192116039621)
                ·
                  refine ⟨15226719727102348521757429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81209171877879192116039621 15226719727102348521757429)
                  ·
                    refine ⟨1427504974415845173914759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15226719727102348521757429 1427504974415845173914759)
                    ·
                      rfl

theorem cell22_4170084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_4170084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170084 prefixEnd_4170084 := by exact prefixLift 4170084
  have htrace : WordTrace (prefixWord ++ tailWord_4170084) baseStart_4170084 baseEnd_4170084 := by
    simpa [prefixWord, tailWord_4170084, baseEnd_4170084] using wordTrace_append hprefix tailTrace_4170084
  have hstable : (prefixWord ++ tailWord_4170084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170084).length < 2 ^ (prefixWord ++ tailWord_4170084).sum := by decide
  have hdescent : baseEnd_4170084 < baseStart_4170084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170090 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_4170090 : Nat := 118140960795 + 4170090 * 2 ^ 59
def prefixEnd_4170090 : Nat := 4983230072969 + 3 ^ 40 * 4170090 * 2
def baseEnd_4170090 : Nat := 1427507028338463158264741

theorem tailTrace_4170090 : CollatzResearch.WordTrace tailWord_4170090 prefixEnd_4170090 1427507028338463158264741 := by
  unfold tailWord_4170090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38023919365620899879098931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101397118308322399677597149 38023919365620899879098931)
  ·
    refine ⟨57035879048431349818648397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38023919365620899879098931 57035879048431349818648397)
    ·
      refine ⟨21388454643161756181993149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57035879048431349818648397 21388454643161756181993149)
      ·
        refine ⟨8020670491185658568247431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21388454643161756181993149 8020670491185658568247431)
        ·
          refine ⟨12031005736778487852371147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020670491185658568247431 12031005736778487852371147)
          ·
            refine ⟨18046508605167731778556721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031005736778487852371147 18046508605167731778556721)
            ·
              refine ⟨13534881453875798833917541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18046508605167731778556721 13534881453875798833917541)
              ·
                refine ⟨2537790272601712281359539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13534881453875798833917541 2537790272601712281359539)
                ·
                  refine ⟨3806685408902568422039309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537790272601712281359539 3806685408902568422039309)
                  ·
                    refine ⟨1427507028338463158264741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806685408902568422039309 1427507028338463158264741)
                    ·
                      rfl

theorem cell22_4170090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_4170090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170090 prefixEnd_4170090 := by exact prefixLift 4170090
  have htrace : WordTrace (prefixWord ++ tailWord_4170090) baseStart_4170090 baseEnd_4170090 := by
    simpa [prefixWord, tailWord_4170090, baseEnd_4170090] using wordTrace_append hprefix tailTrace_4170090
  have hstable : (prefixWord ++ tailWord_4170090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170090).length < 2 ^ (prefixWord ++ tailWord_4170090).sum := by decide
  have hdescent : baseEnd_4170090 < baseStart_4170090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170101 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4170101 : Nat := 118140960795 + 4170101 * 2 ^ 59
def prefixEnd_4170101 : Nat := 4983230072969 + 3 ^ 40 * 4170101 * 2
def baseEnd_4170101 : Nat := 1427510793863262796239707

theorem tailTrace_4170101 : CollatzResearch.WordTrace tailWord_4170101 prefixEnd_4170101 1427510793863262796239707 := by
  unfold tailWord_4170101
  simp only [CollatzResearch.WordTrace]
  refine ⟨152096078665443748395046157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101397385776962498930030771 152096078665443748395046157)
  ·
    refine ⟨57036029499541405648142309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152096078665443748395046157 57036029499541405648142309)
    ·
      refine ⟨10694255531164013559026683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57036029499541405648142309 10694255531164013559026683)
      ·
        refine ⟨16041383296746020338540025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694255531164013559026683 16041383296746020338540025)
        ·
          refine ⟨12031037472559515253905019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16041383296746020338540025 12031037472559515253905019)
          ·
            refine ⟨18046556208839272880857529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031037472559515253905019 18046556208839272880857529)
            ·
              refine ⟨13534917156629454660643147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18046556208839272880857529 13534917156629454660643147)
              ·
                refine ⟨20302375734944181990964721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13534917156629454660643147 20302375734944181990964721)
                ·
                  refine ⟨15226781801208136493223541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20302375734944181990964721 15226781801208136493223541)
                  ·
                    refine ⟨1427510793863262796239707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15226781801208136493223541 1427510793863262796239707)
                    ·
                      rfl

theorem cell22_4170101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4170101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170101 prefixEnd_4170101 := by exact prefixLift 4170101
  have htrace : WordTrace (prefixWord ++ tailWord_4170101) baseStart_4170101 baseEnd_4170101 := by
    simpa [prefixWord, tailWord_4170101, baseEnd_4170101] using wordTrace_append hprefix tailTrace_4170101
  have hstable : (prefixWord ++ tailWord_4170101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170101).length < 2 ^ (prefixWord ++ tailWord_4170101).sum := by decide
  have hdescent : baseEnd_4170101 < baseStart_4170101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170154 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_4170154 : Nat := 118140960795 + 4170154 * 2 ^ 59
def prefixEnd_4170154 : Nat := 4983230072969 + 3 ^ 40 * 4170154 * 2
def baseEnd_4170154 : Nat := 475842978948796108221515

theorem tailTrace_4170154 : CollatzResearch.WordTrace tailWord_4170154 prefixEnd_4170154 475842978948796108221515 := by
  unfold tailWord_4170154
  simp only [CollatzResearch.WordTrace]
  refine ⟨38024502933562934611681379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101398674489501158964483677 38024502933562934611681379)
  ·
    refine ⟨57036754400344401917522069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38024502933562934611681379 57036754400344401917522069)
    ·
      refine ⟨2673597862516143839883847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57036754400344401917522069 2673597862516143839883847)
      ·
        refine ⟨4010396793774215759825771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673597862516143839883847 4010396793774215759825771)
        ·
          refine ⟨6015595190661323639738657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010396793774215759825771 6015595190661323639738657)
          ·
            refine ⟨4511696392995992729803993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6015595190661323639738657 4511696392995992729803993)
            ·
              refine ⟨3383772294746994547352995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511696392995992729803993 3383772294746994547352995)
              ·
                refine ⟨5075658442120491821029493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383772294746994547352995 5075658442120491821029493)
                ·
                  refine ⟨475842978948796108221515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075658442120491821029493 475842978948796108221515)
                  ·
                    rfl

theorem cell22_4170154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_4170154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170154 prefixEnd_4170154 := by exact prefixLift 4170154
  have htrace : WordTrace (prefixWord ++ tailWord_4170154) baseStart_4170154 baseEnd_4170154 := by
    simpa [prefixWord, tailWord_4170154, baseEnd_4170154] using wordTrace_append hprefix tailTrace_4170154
  have hstable : (prefixWord ++ tailWord_4170154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170154).length < 2 ^ (prefixWord ++ tailWord_4170154).sum := by decide
  have hdescent : baseEnd_4170154 < baseStart_4170154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170266 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_4170266 : Nat := 118140960795 + 4170266 * 2 ^ 59
def prefixEnd_4170266 : Nat := 4983230072969 + 3 ^ 40 * 4170266 * 2
def baseEnd_4170266 : Nat := 475855758911752455288067

theorem tailTrace_4170266 : CollatzResearch.WordTrace tailWord_4170266 prefixEnd_4170266 475855758911752455288067 := by
  unfold tailWord_4170266
  simp only [CollatzResearch.WordTrace]
  refine ⟨38025524177461495393700663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101401397806563987716535101 38025524177461495393700663)
  ·
    refine ⟨57038286266192243090550995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38025524177461495393700663 57038286266192243090550995)
    ·
      refine ⟨85557429399288364635826493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57038286266192243090550995 85557429399288364635826493)
      ·
        refine ⟨32084036024733136738434935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85557429399288364635826493 32084036024733136738434935)
        ·
          refine ⟨48126054037099705107652403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32084036024733136738434935 48126054037099705107652403)
          ·
            refine ⟨72189081055649557661478605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48126054037099705107652403 72189081055649557661478605)
            ·
              refine ⟨27070905395868584123054477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72189081055649557661478605 27070905395868584123054477)
              ·
                refine ⟨10151589523450719046145429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27070905395868584123054477 10151589523450719046145429)
                ·
                  refine ⟨475855758911752455288067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10151589523450719046145429 475855758911752455288067)
                  ·
                    rfl

theorem cell22_4170266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_4170266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170266 prefixEnd_4170266 := by exact prefixLift 4170266
  have htrace : WordTrace (prefixWord ++ tailWord_4170266) baseStart_4170266 baseEnd_4170266 := by
    simpa [prefixWord, tailWord_4170266, baseEnd_4170266] using wordTrace_append hprefix tailTrace_4170266
  have hstable : (prefixWord ++ tailWord_4170266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170266).length < 2 ^ (prefixWord ++ tailWord_4170266).sum := by decide
  have hdescent : baseEnd_4170266 < baseStart_4170266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170296 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_4170296 : Nat := 118140960795 + 4170296 * 2 ^ 59
def prefixEnd_4170296 : Nat := 4983230072969 + 3 ^ 40 * 4170296 * 2
def baseEnd_4170296 : Nat := 1427577546348347287614109

theorem tailTrace_4170296 : CollatzResearch.WordTrace tailWord_4170296 prefixEnd_4170296 1427577546348347287614109 := by
  unfold tailWord_4170296
  simp only [CollatzResearch.WordTrace]
  refine ⟨76051595449868648349197371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101402127266491531132263161 76051595449868648349197371)
  ·
    refine ⟨114077393174802972523796057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76051595449868648349197371 114077393174802972523796057)
    ·
      refine ⟨85558044881102229392847043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114077393174802972523796057 85558044881102229392847043)
      ·
        refine ⟨128337067321653344089270565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85558044881102229392847043 128337067321653344089270565)
        ·
          refine ⟨24063200122810002016738231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128337067321653344089270565 24063200122810002016738231)
          ·
            refine ⟨36094800184215003025107347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24063200122810002016738231 36094800184215003025107347)
            ·
              refine ⟨54142200276322504537661021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36094800184215003025107347 54142200276322504537661021)
              ·
                refine ⟨20303325103620939201622883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54142200276322504537661021 20303325103620939201622883)
                ·
                  refine ⟨30454987655431408802434325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20303325103620939201622883 30454987655431408802434325)
                  ·
                    refine ⟨1427577546348347287614109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30454987655431408802434325 1427577546348347287614109)
                    ·
                      rfl

theorem cell22_4170296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_4170296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170296 prefixEnd_4170296 := by exact prefixLift 4170296
  have htrace : WordTrace (prefixWord ++ tailWord_4170296) baseStart_4170296 baseEnd_4170296 := by
    simpa [prefixWord, tailWord_4170296, baseEnd_4170296] using wordTrace_append hprefix tailTrace_4170296
  have hstable : (prefixWord ++ tailWord_4170296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170296).length < 2 ^ (prefixWord ++ tailWord_4170296).sum := by decide
  have hdescent : baseEnd_4170296 < baseStart_4170296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170298 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_4170298 : Nat := 118140960795 + 4170298 * 2 ^ 59
def prefixEnd_4170298 : Nat := 4983230072969 + 3 ^ 40 * 4170298 * 2
def baseEnd_4170298 : Nat := 1427578230989219949064103

theorem tailTrace_4170298 : CollatzResearch.WordTrace tailWord_4170298 prefixEnd_4170298 1427578230989219949064103 := by
  unfold tailWord_4170298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38025815961432512759991887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101402175897153367359978365 38025815961432512759991887)
  ·
    refine ⟨57038723942148769139987831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38025815961432512759991887 57038723942148769139987831)
    ·
      refine ⟨85558085913223153709981747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57038723942148769139987831 85558085913223153709981747)
      ·
        refine ⟨128337128869834730564972621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85558085913223153709981747 128337128869834730564972621)
        ·
          refine ⟨48126423326188023961864733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128337128869834730564972621 48126423326188023961864733)
          ·
            refine ⟨18047408747320508985699275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48126423326188023961864733 18047408747320508985699275)
            ·
              refine ⟨27071113120980763478548913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18047408747320508985699275 27071113120980763478548913)
              ·
                refine ⟨20303334840735572608911685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27071113120980763478548913 20303334840735572608911685)
                ·
                  refine ⟨3806875282637919864170941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20303334840735572608911685 3806875282637919864170941)
                  ·
                    refine ⟨1427578230989219949064103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806875282637919864170941 1427578230989219949064103)
                    ·
                      rfl

theorem cell22_4170298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_4170298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170298 prefixEnd_4170298 := by exact prefixLift 4170298
  have htrace : WordTrace (prefixWord ++ tailWord_4170298) baseStart_4170298 baseEnd_4170298 := by
    simpa [prefixWord, tailWord_4170298, baseEnd_4170298] using wordTrace_append hprefix tailTrace_4170298
  have hstable : (prefixWord ++ tailWord_4170298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170298).length < 2 ^ (prefixWord ++ tailWord_4170298).sum := by decide
  have hdescent : baseEnd_4170298 < baseStart_4170298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170300 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 4]
def baseStart_4170300 : Nat := 118140960795 + 4170300 * 2 ^ 59
def prefixEnd_4170300 : Nat := 4983230072969 + 3 ^ 40 * 4170300 * 2
def baseEnd_4170300 : Nat := 475859638543364203504699

theorem tailTrace_4170300 : CollatzResearch.WordTrace tailWord_4170300 prefixEnd_4170300 475859638543364203504699 := by
  unfold tailWord_4170300
  simp only [CollatzResearch.WordTrace]
  refine ⟨76051668395861402690770177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101402224527815203587693569 76051668395861402690770177)
  ·
    refine ⟨57038751296896052018077633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76051668395861402690770177 57038751296896052018077633)
    ·
      refine ⟨42779063472672039013558225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57038751296896052018077633 42779063472672039013558225)
      ·
        refine ⟨32084297604504029260168669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42779063472672039013558225 32084297604504029260168669)
        ·
          refine ⟨12031611601689010972563251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32084297604504029260168669 12031611601689010972563251)
          ·
            refine ⟨18047417402533516458844877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031611601689010972563251 18047417402533516458844877)
            ·
              refine ⟨6767781525950068672066829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18047417402533516458844877 6767781525950068672066829)
              ·
                refine ⟨2537918072231275752025061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6767781525950068672066829 2537918072231275752025061)
                ·
                  refine ⟨475859638543364203504699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537918072231275752025061 475859638543364203504699)
                  ·
                    rfl

theorem cell22_4170300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_4170300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170300 prefixEnd_4170300 := by exact prefixLift 4170300
  have htrace : WordTrace (prefixWord ++ tailWord_4170300) baseStart_4170300 baseEnd_4170300 := by
    simpa [prefixWord, tailWord_4170300, baseEnd_4170300] using wordTrace_append hprefix tailTrace_4170300
  have hstable : (prefixWord ++ tailWord_4170300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170300).length < 2 ^ (prefixWord ++ tailWord_4170300).sum := by decide
  have hdescent : baseEnd_4170300 < baseStart_4170300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170311 : List Nat := [1, 1, 4, 1, 4, 1, 10]
def baseStart_4170311 : Nat := 118140960795 + 4170311 * 2 ^ 59
def prefixEnd_4170311 : Nat := 4983230072969 + 3 ^ 40 * 4170311 * 2
def baseEnd_4170311 : Nat := 52873432635366379573669

theorem tailTrace_4170311 : CollatzResearch.WordTrace tailWord_4170311 prefixEnd_4170311 52873432635366379573669 := by
  unfold tailWord_4170311
  simp only [CollatzResearch.WordTrace]
  refine ⟨152103737994682954260190787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101402491996455302840127191 152103737994682954260190787)
  ·
    refine ⟨228155606992024431390286181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152103737994682954260190787 228155606992024431390286181)
    ·
      refine ⟨42779176311004580885678659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228155606992024431390286181 42779176311004580885678659)
      ·
        refine ⟨64168764466506871328517989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42779176311004580885678659 64168764466506871328517989)
        ·
          refine ⟨12031643337470038374097123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64168764466506871328517989 12031643337470038374097123)
          ·
            refine ⟨18047465006205057561145685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031643337470038374097123 18047465006205057561145685)
            ·
              refine ⟨52873432635366379573669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18047465006205057561145685 52873432635366379573669)
              ·
                rfl

theorem cell22_4170311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 10].length) (baseStart_4170311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170311 prefixEnd_4170311 := by exact prefixLift 4170311
  have htrace : WordTrace (prefixWord ++ tailWord_4170311) baseStart_4170311 baseEnd_4170311 := by
    simpa [prefixWord, tailWord_4170311, baseEnd_4170311] using wordTrace_append hprefix tailTrace_4170311
  have hstable : (prefixWord ++ tailWord_4170311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170311).length < 2 ^ (prefixWord ++ tailWord_4170311).sum := by decide
  have hdescent : baseEnd_4170311 < baseStart_4170311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170332 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_4170332 : Nat := 118140960795 + 4170332 * 2 ^ 59
def prefixEnd_4170332 : Nat := 4983230072969 + 3 ^ 40 * 4170332 * 2
def baseEnd_4170332 : Nat := 1427589869884055193713999

theorem tailTrace_4170332 : CollatzResearch.WordTrace tailWord_4170332 prefixEnd_4170332 1427589869884055193713999 := by
  unfold tailWord_4170332
  simp only [CollatzResearch.WordTrace]
  refine ⟨76052251963803437423352625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101403002618404583231136833 76052251963803437423352625)
  ·
    refine ⟨57039188972852578067514469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76052251963803437423352625 57039188972852578067514469)
    ·
      refine ⟨10694847932409858387658963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57039188972852578067514469 10694847932409858387658963)
      ·
        refine ⟨16042271898614787581488445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694847932409858387658963 16042271898614787581488445)
        ·
          refine ⟨6015851961980545343058167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16042271898614787581488445 6015851961980545343058167)
          ·
            refine ⟨9023777942970818014587251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015851961980545343058167 9023777942970818014587251)
            ·
              refine ⟨13535666914456227021880877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023777942970818014587251 13535666914456227021880877)
              ·
                refine ⟨5075875092921085133205329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13535666914456227021880877 5075875092921085133205329)
                ·
                  refine ⟨3806906319690813849903997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5075875092921085133205329 3806906319690813849903997)
                  ·
                    refine ⟨1427589869884055193713999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806906319690813849903997 1427589869884055193713999)
                    ·
                      rfl

theorem cell22_4170332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_4170332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170332 prefixEnd_4170332 := by exact prefixLift 4170332
  have htrace : WordTrace (prefixWord ++ tailWord_4170332) baseStart_4170332 baseEnd_4170332 := by
    simpa [prefixWord, tailWord_4170332, baseEnd_4170332] using wordTrace_append hprefix tailTrace_4170332
  have hstable : (prefixWord ++ tailWord_4170332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170332).length < 2 ^ (prefixWord ++ tailWord_4170332).sum := by decide
  have hdescent : baseEnd_4170332 < baseStart_4170332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170343 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4170343 : Nat := 118140960795 + 4170343 * 2 ^ 59
def prefixEnd_4170343 : Nat := 4983230072969 + 3 ^ 40 * 4170343 * 2
def baseEnd_4170343 : Nat := 1427593635408854831688965

theorem tailTrace_4170343 : CollatzResearch.WordTrace tailWord_4170343 prefixEnd_4170343 1427593635408854831688965 := by
  unfold tailWord_4170343
  simp only [CollatzResearch.WordTrace]
  refine ⟨152104905130567023725355683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101403270087044682483570455 152104905130567023725355683)
  ·
    refine ⟨228157357695850535588033525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152104905130567023725355683 228157357695850535588033525)
    ·
      refine ⟨21389752283985987711378143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228157357695850535588033525 21389752283985987711378143)
      ·
        refine ⟨32084628425978981567067215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21389752283985987711378143 32084628425978981567067215)
        ·
          refine ⟨48126942638968472350600823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32084628425978981567067215 48126942638968472350600823)
          ·
            refine ⟨72190413958452708525901235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48126942638968472350600823 72190413958452708525901235)
            ·
              refine ⟨108285620937679062788851853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72190413958452708525901235 108285620937679062788851853)
              ·
                refine ⟨40607107851629648545819445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108285620937679062788851853 40607107851629648545819445)
                ·
                  refine ⟨3806916361090279551170573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40607107851629648545819445 3806916361090279551170573)
                  ·
                    refine ⟨1427593635408854831688965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3806916361090279551170573 1427593635408854831688965)
                    ·
                      rfl

theorem cell22_4170343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4170343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170343 prefixEnd_4170343 := by exact prefixLift 4170343
  have htrace : WordTrace (prefixWord ++ tailWord_4170343) baseStart_4170343 baseEnd_4170343 := by
    simpa [prefixWord, tailWord_4170343, baseEnd_4170343] using wordTrace_append hprefix tailTrace_4170343
  have hstable : (prefixWord ++ tailWord_4170343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170343).length < 2 ^ (prefixWord ++ tailWord_4170343).sum := by decide
  have hdescent : baseEnd_4170343 < baseStart_4170343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170373 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 5]
def baseStart_4170373 : Nat := 118140960795 + 4170373 * 2 ^ 59
def prefixEnd_4170373 : Nat := 4983230072969 + 3 ^ 40 * 4170373 * 2
def baseEnd_4170373 : Nat := 475867968340648251146291

theorem tailTrace_4170373 : CollatzResearch.WordTrace tailWord_4170373 prefixEnd_4170373 475867968340648251146291 := by
  unfold tailWord_4170373
  simp only [CollatzResearch.WordTrace]
  refine ⟨152105999320458338848947773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101403999546972225899298515 152105999320458338848947773)
  ·
    refine ⟨57039749745171877068355415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152105999320458338848947773 57039749745171877068355415)
    ·
      refine ⟨85559624617757815602533123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57039749745171877068355415 85559624617757815602533123)
      ·
        refine ⟨128339436926636723403799685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85559624617757815602533123 128339436926636723403799685)
        ·
          refine ⟨24063644423744385638212441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128339436926636723403799685 24063644423744385638212441)
          ·
            refine ⟨18047733317808289228659331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24063644423744385638212441 18047733317808289228659331)
            ·
              refine ⟨27071599976712433842988997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18047733317808289228659331 27071599976712433842988997)
              ·
                refine ⟨5075924995633581345560437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27071599976712433842988997 5075924995633581345560437)
                ·
                  refine ⟨475867968340648251146291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075924995633581345560437 475867968340648251146291)
                  ·
                    rfl

theorem cell22_4170373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_4170373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170373 prefixEnd_4170373 := by exact prefixLift 4170373
  have htrace : WordTrace (prefixWord ++ tailWord_4170373) baseStart_4170373 baseEnd_4170373 := by
    simpa [prefixWord, tailWord_4170373, baseEnd_4170373] using wordTrace_append hprefix tailTrace_4170373
  have hstable : (prefixWord ++ tailWord_4170373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170373).length < 2 ^ (prefixWord ++ tailWord_4170373).sum := by decide
  have hdescent : baseEnd_4170373 < baseStart_4170373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170463 : List Nat := [1, 1, 2, 3, 2, 4, 1, 8]
def baseStart_4170463 : Nat := 118140960795 + 4170463 * 2 ^ 59
def prefixEnd_4170463 : Nat := 4983230072969 + 3 ^ 40 * 4170463 * 2
def baseEnd_4170463 : Nat := 158626079317912724298733

theorem tailTrace_4170463 : CollatzResearch.WordTrace tailWord_4170463 prefixEnd_4170463 158626079317912724298733 := by
  unfold tailWord_4170463
  simp only [CollatzResearch.WordTrace]
  refine ⟨152109281890132284219724043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101406187926754856146482695 152109281890132284219724043)
  ·
    refine ⟨228163922835198426329586065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152109281890132284219724043 228163922835198426329586065)
    ·
      refine ⟨171122942126398819747189549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228163922835198426329586065 171122942126398819747189549)
      ·
        refine ⟨64171103297399557405196081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171122942126398819747189549 64171103297399557405196081)
        ·
          refine ⟨48128327473049668053897061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64171103297399557405196081 48128327473049668053897061)
          ·
            refine ⟨9024061401196812760105699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48128327473049668053897061 9024061401196812760105699)
            ·
              refine ⟨13536092101795219140158549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024061401196812760105699 13536092101795219140158549)
              ·
                refine ⟨158626079317912724298733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13536092101795219140158549 158626079317912724298733)
                ·
                  rfl

theorem cell22_4170463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 8].length) (baseStart_4170463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170463 prefixEnd_4170463 := by exact prefixLift 4170463
  have htrace : WordTrace (prefixWord ++ tailWord_4170463) baseStart_4170463 baseEnd_4170463 := by
    simpa [prefixWord, tailWord_4170463, baseEnd_4170463] using wordTrace_append hprefix tailTrace_4170463
  have hstable : (prefixWord ++ tailWord_4170463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170463).length < 2 ^ (prefixWord ++ tailWord_4170463).sum := by decide
  have hdescent : baseEnd_4170463 < baseStart_4170463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170493 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4170493 : Nat := 118140960795 + 4170493 * 2 ^ 59
def prefixEnd_4170493 : Nat := 4983230072969 + 3 ^ 40 * 4170493 * 2
def baseEnd_4170493 : Nat := 1427644983474304440438505

theorem tailTrace_4170493 : CollatzResearch.WordTrace tailWord_4170493 prefixEnd_4170493 1427644983474304440438505 := by
  unfold tailWord_4170493
  simp only [CollatzResearch.WordTrace]
  refine ⟨152110376080023599343316133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101406917386682399562210755 152110376080023599343316133)
  ·
    refine ⟨28520695515004424876871775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152110376080023599343316133 28520695515004424876871775)
    ·
      refine ⟨42781043272506637315307663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28520695515004424876871775 42781043272506637315307663)
      ·
        refine ⟨64171564908759955972961495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42781043272506637315307663 64171564908759955972961495)
        ·
          refine ⟨96257347363139933959442243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64171564908759955972961495 96257347363139933959442243)
          ·
            refine ⟨144386021044709900939163365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96257347363139933959442243 144386021044709900939163365)
            ·
              refine ⟨27072378945883106426093131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144386021044709900939163365 27072378945883106426093131)
              ·
                refine ⟨40608568418824659639139697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27072378945883106426093131 40608568418824659639139697)
                ·
                  refine ⟨30456426314118494729354773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40608568418824659639139697 30456426314118494729354773)
                  ·
                    refine ⟨1427644983474304440438505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30456426314118494729354773 1427644983474304440438505)
                    ·
                      rfl

theorem cell22_4170493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4170493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170493 prefixEnd_4170493 := by exact prefixLift 4170493
  have htrace : WordTrace (prefixWord ++ tailWord_4170493) baseStart_4170493 baseEnd_4170493 := by
    simpa [prefixWord, tailWord_4170493, baseEnd_4170493] using wordTrace_append hprefix tailTrace_4170493
  have hstable : (prefixWord ++ tailWord_4170493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170493).length < 2 ^ (prefixWord ++ tailWord_4170493).sum := by decide
  have hdescent : baseEnd_4170493 < baseStart_4170493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170542 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_4170542 : Nat := 118140960795 + 4170542 * 2 ^ 59
def prefixEnd_4170542 : Nat := 4983230072969 + 3 ^ 40 * 4170542 * 2
def baseEnd_4170542 : Nat := 475887252391894881987785

theorem tailTrace_4170542 : CollatzResearch.WordTrace tailWord_4170542 prefixEnd_4170542 475887252391894881987785 := by
  unfold tailWord_4170542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014020407105760088981235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101408108837897387141233253 19014020407105760088981235)
  ·
    refine ⟨28521030610658640133471853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014020407105760088981235 28521030610658640133471853)
    ·
      refine ⟨10695386478996990050051945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28521030610658640133471853 10695386478996990050051945)
      ·
        refine ⟨8021539859247742537538959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10695386478996990050051945 8021539859247742537538959)
        ·
          refine ⟨12032309788871613806308439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8021539859247742537538959 12032309788871613806308439)
          ·
            refine ⟨18048464683307420709462659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12032309788871613806308439 18048464683307420709462659)
            ·
              refine ⟨27072697024961131064193989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18048464683307420709462659 27072697024961131064193989)
              ·
                refine ⟨5076130692180212074536373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27072697024961131064193989 5076130692180212074536373)
                ·
                  refine ⟨475887252391894881987785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5076130692180212074536373 475887252391894881987785)
                  ·
                    rfl

theorem cell22_4170542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_4170542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170542 prefixEnd_4170542 := by exact prefixLift 4170542
  have htrace : WordTrace (prefixWord ++ tailWord_4170542) baseStart_4170542 baseEnd_4170542 := by
    simpa [prefixWord, tailWord_4170542, baseEnd_4170542] using wordTrace_append hprefix tailTrace_4170542
  have hstable : (prefixWord ++ tailWord_4170542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170542).length < 2 ^ (prefixWord ++ tailWord_4170542).sum := by decide
  have hdescent : baseEnd_4170542 < baseStart_4170542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170557 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_4170557 : Nat := 118140960795 + 4170557 * 2 ^ 59
def prefixEnd_4170557 : Nat := 4983230072969 + 3 ^ 40 * 4170557 * 2
def baseEnd_4170557 : Nat := 1427666891982229606838309

theorem tailTrace_4170557 : CollatzResearch.WordTrace tailWord_4170557 prefixEnd_4170557 1427666891982229606838309 := by
  unfold tailWord_4170557
  simp only [CollatzResearch.WordTrace]
  refine ⟨152112710351791738273645925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101408473567861158849097283 152112710351791738273645925)
  ·
    refine ⟨28521133190960950926308611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152112710351791738273645925 28521133190960950926308611)
    ·
      refine ⟨42781699786441426389462917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28521133190960950926308611 42781699786441426389462917)
      ·
        refine ⟨8021568709957767448024297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42781699786441426389462917 8021568709957767448024297)
        ·
          refine ⟨6016176532468325586018223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8021568709957767448024297 6016176532468325586018223)
          ·
            refine ⟨9024264798702488379027335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6016176532468325586018223 9024264798702488379027335)
            ·
              refine ⟨13536397198053732568541003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024264798702488379027335 13536397198053732568541003)
              ·
                refine ⟨20304595797080598852811505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13536397198053732568541003 20304595797080598852811505)
                ·
                  refine ⟨15228446847810449139608629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20304595797080598852811505 15228446847810449139608629)
                  ·
                    refine ⟨1427666891982229606838309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15228446847810449139608629 1427666891982229606838309)
                    ·
                      rfl

theorem cell22_4170557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_4170557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170557 prefixEnd_4170557 := by exact prefixLift 4170557
  have htrace : WordTrace (prefixWord ++ tailWord_4170557) baseStart_4170557 baseEnd_4170557 := by
    simpa [prefixWord, tailWord_4170557, baseEnd_4170557] using wordTrace_append hprefix tailTrace_4170557
  have hstable : (prefixWord ++ tailWord_4170557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170557).length < 2 ^ (prefixWord ++ tailWord_4170557).sum := by decide
  have hdescent : baseEnd_4170557 < baseStart_4170557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170585 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_4170585 : Nat := 118140960795 + 4170585 * 2 ^ 59
def prefixEnd_4170585 : Nat := 4983230072969 + 3 ^ 40 * 4170585 * 2
def baseEnd_4170585 : Nat := 1427676476954446867138223

theorem tailTrace_4170585 : CollatzResearch.WordTrace tailWord_4170585 prefixEnd_4170585 1427676476954446867138223 := by
  unfold tailWord_4170585
  simp only [CollatzResearch.WordTrace]
  refine ⟨152113731595690299055665209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101409154397126866037110139 152113731595690299055665209)
  ·
    refine ⟨114085298696767724291748907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152113731595690299055665209 114085298696767724291748907)
    ·
      refine ⟨171127948045151586437623361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114085298696767724291748907 171127948045151586437623361)
      ·
        refine ⟨128345961033863689828217521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171127948045151586437623361 128345961033863689828217521)
        ·
          refine ⟨96259470775397767371163141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128345961033863689828217521 96259470775397767371163141)
          ·
            refine ⟨18048650770387081382093089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96259470775397767371163141 18048650770387081382093089)
            ·
              refine ⟨13536488077790311036569817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18048650770387081382093089 13536488077790311036569817)
              ·
                refine ⟨10152366058342733277427363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13536488077790311036569817 10152366058342733277427363)
                ·
                  refine ⟨15228549087514099916141045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10152366058342733277427363 15228549087514099916141045)
                  ·
                    refine ⟨1427676476954446867138223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15228549087514099916141045 1427676476954446867138223)
                    ·
                      rfl

theorem cell22_4170585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_4170585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170585 prefixEnd_4170585 := by exact prefixLift 4170585
  have htrace : WordTrace (prefixWord ++ tailWord_4170585) baseStart_4170585 baseEnd_4170585 := by
    simpa [prefixWord, tailWord_4170585, baseEnd_4170585] using wordTrace_append hprefix tailTrace_4170585
  have hstable : (prefixWord ++ tailWord_4170585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170585).length < 2 ^ (prefixWord ++ tailWord_4170585).sum := by decide
  have hdescent : baseEnd_4170585 < baseStart_4170585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170632 : List Nat := [2, 1, 3, 3, 2, 1, 4, 6]
def baseStart_4170632 : Nat := 118140960795 + 4170632 * 2 ^ 59
def prefixEnd_4170632 : Nat := 4983230072969 + 3 ^ 40 * 4170632 * 2
def baseEnd_4170632 : Nat := 158632507334994934579231

theorem tailTrace_4170632 : CollatzResearch.WordTrace tailWord_4170632 prefixEnd_4170632 158632507334994934579231 := by
  unfold tailWord_4170632
  simp only [CollatzResearch.WordTrace]
  refine ⟨76057722913260013041313075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101410297217680017388417433 76057722913260013041313075)
  ·
    refine ⟨114086584369890019561969613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76057722913260013041313075 114086584369890019561969613)
    ·
      refine ⟨42782469138708757335738605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114086584369890019561969613 42782469138708757335738605)
      ·
        refine ⟨16043425927015784000901977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42782469138708757335738605 16043425927015784000901977)
        ·
          refine ⟨12032569445261838000676483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16043425927015784000901977 12032569445261838000676483)
          ·
            refine ⟨18048854167892757001014725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12032569445261838000676483 18048854167892757001014725)
            ·
              refine ⟨3384160156479891937690261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18048854167892757001014725 3384160156479891937690261)
              ·
                refine ⟨158632507334994934579231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3384160156479891937690261 158632507334994934579231)
                ·
                  rfl

theorem cell22_4170632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_4170632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170632 prefixEnd_4170632 := by exact prefixLift 4170632
  have htrace : WordTrace (prefixWord ++ tailWord_4170632) baseStart_4170632 baseEnd_4170632 := by
    simpa [prefixWord, tailWord_4170632, baseEnd_4170632] using wordTrace_append hprefix tailTrace_4170632
  have hstable : (prefixWord ++ tailWord_4170632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170632).length < 2 ^ (prefixWord ++ tailWord_4170632).sum := by decide
  have hdescent : baseEnd_4170632 < baseStart_4170632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170660 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_4170660 : Nat := 118140960795 + 4170660 * 2 ^ 59
def prefixEnd_4170660 : Nat := 4983230072969 + 3 ^ 40 * 4170660 * 2
def baseEnd_4170660 : Nat := 475900716995723890504331

theorem tailTrace_4170660 : CollatzResearch.WordTrace tailWord_4170660 prefixEnd_4170660 475900716995723890504331 := by
  unfold tailWord_4170660
  simp only [CollatzResearch.WordTrace]
  refine ⟨76058233535209293432322717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101410978046945724576430289 76058233535209293432322717)
  ·
    refine ⟨28521837575703485037121019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76058233535209293432322717 28521837575703485037121019)
    ·
      refine ⟨42782756363555227555681529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28521837575703485037121019 42782756363555227555681529)
      ·
        refine ⟨32087067272666420666761147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42782756363555227555681529 32087067272666420666761147)
        ·
          refine ⟨48130600908999631000141721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32087067272666420666761147 48130600908999631000141721)
          ·
            refine ⟨36097950681749723250106291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48130600908999631000141721 36097950681749723250106291)
            ·
              refine ⟨54146926022624584875159437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36097950681749723250106291 54146926022624584875159437)
              ·
                refine ⟨20305097258484219328184789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54146926022624584875159437 20305097258484219328184789)
                ·
                  refine ⟨475900716995723890504331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20305097258484219328184789 475900716995723890504331)
                  ·
                    rfl

theorem cell22_4170660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_4170660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170660 prefixEnd_4170660 := by exact prefixLift 4170660
  have htrace : WordTrace (prefixWord ++ tailWord_4170660) baseStart_4170660 baseEnd_4170660 := by
    simpa [prefixWord, tailWord_4170660, baseEnd_4170660] using wordTrace_append hprefix tailTrace_4170660
  have hstable : (prefixWord ++ tailWord_4170660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170660).length < 2 ^ (prefixWord ++ tailWord_4170660).sum := by decide
  have hdescent : baseEnd_4170660 < baseStart_4170660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170677 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 5]
def baseStart_4170677 : Nat := 118140960795 + 4170677 * 2 ^ 59
def prefixEnd_4170677 : Nat := 4983230072969 + 3 ^ 40 * 4170677 * 2
def baseEnd_4170677 : Nat := 475902656811529764612647

theorem tailTrace_4170677 : CollatzResearch.WordTrace tailWord_4170677 prefixEnd_4170677 475902656811529764612647 := by
  unfold tailWord_4170677
  simp only [CollatzResearch.WordTrace]
  refine ⟨152117087111356998768014285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101411391407571332512009523 152117087111356998768014285)
  ·
    refine ⟨57043907666758874538005357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152117087111356998768014285 57043907666758874538005357)
    ·
      refine ⟨21391465375034577951752009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57043907666758874538005357 21391465375034577951752009)
      ·
        refine ⟨16043599031275933463814007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21391465375034577951752009 16043599031275933463814007)
        ·
          refine ⟨24065398546913900195721011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16043599031275933463814007 24065398546913900195721011)
          ·
            refine ⟨36098097820370850293581517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24065398546913900195721011 36098097820370850293581517)
            ·
              refine ⟨13536786682639068860093069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36098097820370850293581517 13536786682639068860093069)
              ·
                refine ⟨5076295005989650822534901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13536786682639068860093069 5076295005989650822534901)
                ·
                  refine ⟨475902656811529764612647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5076295005989650822534901 475902656811529764612647)
                  ·
                    rfl

theorem cell22_4170677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_4170677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170677 prefixEnd_4170677 := by exact prefixLift 4170677
  have htrace : WordTrace (prefixWord ++ tailWord_4170677) baseStart_4170677 baseEnd_4170677 := by
    simpa [prefixWord, tailWord_4170677, baseEnd_4170677] using wordTrace_append hprefix tailTrace_4170677
  have hstable : (prefixWord ++ tailWord_4170677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170677).length < 2 ^ (prefixWord ++ tailWord_4170677).sum := by decide
  have hdescent : baseEnd_4170677 < baseStart_4170677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170737 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_4170737 : Nat := 118140960795 + 4170737 * 2 ^ 59
def prefixEnd_4170737 : Nat := 4983230072969 + 3 ^ 40 * 4170737 * 2
def baseEnd_4170737 : Nat := 1427728509660769137337757

theorem tailTrace_4170737 : CollatzResearch.WordTrace tailWord_4170737 prefixEnd_4170737 1427728509660769137337757 := by
  unfold tailWord_4170737
  simp only [CollatzResearch.WordTrace]
  refine ⟨152119275491139629015198465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101412850327426419343465643 152119275491139629015198465)
  ·
    refine ⟨114089456618354721761398849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152119275491139629015198465 114089456618354721761398849)
    ·
      refine ⟨85567092463766041321049137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114089456618354721761398849 85567092463766041321049137)
      ·
        refine ⟨64175319347824530990786853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85567092463766041321049137 64175319347824530990786853)
        ·
          refine ⟨12032872377717099560772535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64175319347824530990786853 12032872377717099560772535)
          ·
            refine ⟨18049308566575649341158803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12032872377717099560772535 18049308566575649341158803)
            ·
              refine ⟨27073962849863474011738205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18049308566575649341158803 27073962849863474011738205)
              ·
                refine ⟨10152736068698802754401827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27073962849863474011738205 10152736068698802754401827)
                ·
                  refine ⟨15229104103048204131602741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10152736068698802754401827 15229104103048204131602741)
                  ·
                    refine ⟨1427728509660769137337757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229104103048204131602741 1427728509660769137337757)
                    ·
                      rfl

theorem cell22_4170737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_4170737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170737 prefixEnd_4170737 := by exact prefixLift 4170737
  have htrace : WordTrace (prefixWord ++ tailWord_4170737) baseStart_4170737 baseEnd_4170737 := by
    simpa [prefixWord, tailWord_4170737, baseEnd_4170737] using wordTrace_append hprefix tailTrace_4170737
  have hstable : (prefixWord ++ tailWord_4170737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170737).length < 2 ^ (prefixWord ++ tailWord_4170737).sum := by decide
  have hdescent : baseEnd_4170737 < baseStart_4170737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170788 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_4170788 : Nat := 118140960795 + 4170788 * 2 ^ 59
def prefixEnd_4170788 : Nat := 4983230072969 + 3 ^ 40 * 4170788 * 2
def baseEnd_4170788 : Nat := 1427745968003022004312601

theorem tailTrace_4170788 : CollatzResearch.WordTrace tailWord_4170788 prefixEnd_4170788 1427745968003022004312601 := by
  unfold tailWord_4170788
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060567806977432362652509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101414090409303243150203345 76060567806977432362652509)
  ·
    refine ⟨28522712927616537135994691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76060567806977432362652509 28522712927616537135994691)
    ·
      refine ⟨42784069391424805703992037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28522712927616537135994691 42784069391424805703992037)
      ·
        refine ⟨8022013010892151069498507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42784069391424805703992037 8022013010892151069498507)
        ·
          refine ⟨12033019516338226604247761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022013010892151069498507 12033019516338226604247761)
          ·
            refine ⟨9024764637253669953185821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12033019516338226604247761 9024764637253669953185821)
            ·
              refine ⟨3384286738970126232444683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9024764637253669953185821 3384286738970126232444683)
              ·
                refine ⟨5076430108455189348667025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384286738970126232444683 5076430108455189348667025)
                ·
                  refine ⟨3807322581341392011500269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076430108455189348667025 3807322581341392011500269)
                  ·
                    refine ⟨1427745968003022004312601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3807322581341392011500269 1427745968003022004312601)
                    ·
                      rfl

theorem cell22_4170788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_4170788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170788 prefixEnd_4170788 := by exact prefixLift 4170788
  have htrace : WordTrace (prefixWord ++ tailWord_4170788) baseStart_4170788 baseEnd_4170788 := by
    simpa [prefixWord, tailWord_4170788, baseEnd_4170788] using wordTrace_append hprefix tailTrace_4170788
  have hstable : (prefixWord ++ tailWord_4170788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170788).length < 2 ^ (prefixWord ++ tailWord_4170788).sum := by decide
  have hdescent : baseEnd_4170788 < baseStart_4170788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170812 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_4170812 : Nat := 118140960795 + 4170812 * 2 ^ 59
def prefixEnd_4170812 : Nat := 4983230072969 + 3 ^ 40 * 4170812 * 2
def baseEnd_4170812 : Nat := 475918061231164647237509

theorem tailTrace_4170812 : CollatzResearch.WordTrace tailWord_4170812 prefixEnd_4170812 475918061231164647237509 := by
  unfold tailWord_4170812
  simp only [CollatzResearch.WordTrace]
  refine ⟨76061005482933958412089345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101414673977245277882785793 76061005482933958412089345)
  ·
    refine ⟨57045754112200468809067009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76061005482933958412089345 57045754112200468809067009)
    ·
      refine ⟨42784315584150351606800257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57045754112200468809067009 42784315584150351606800257)
      ·
        refine ⟨32088236688112763705100193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42784315584150351606800257 32088236688112763705100193)
        ·
          refine ⟨24066177516084572778825145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32088236688112763705100193 24066177516084572778825145)
          ·
            refine ⟨18049633137063429584118859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24066177516084572778825145 18049633137063429584118859)
            ·
              refine ⟨27074449705595144376178289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18049633137063429584118859 27074449705595144376178289)
              ·
                refine ⟨20305837279196358282133717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27074449705595144376178289 20305837279196358282133717)
                ·
                  refine ⟨475918061231164647237509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20305837279196358282133717 475918061231164647237509)
                  ·
                    rfl

theorem cell22_4170812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_4170812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170812 prefixEnd_4170812 := by exact prefixLift 4170812
  have htrace : WordTrace (prefixWord ++ tailWord_4170812) baseStart_4170812 baseEnd_4170812 := by
    simpa [prefixWord, tailWord_4170812, baseEnd_4170812] using wordTrace_append hprefix tailTrace_4170812
  have hstable : (prefixWord ++ tailWord_4170812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170812).length < 2 ^ (prefixWord ++ tailWord_4170812).sum := by decide
  have hdescent : baseEnd_4170812 < baseStart_4170812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170829 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4170829 : Nat := 118140960795 + 4170829 * 2 ^ 59
def prefixEnd_4170829 : Nat := 4983230072969 + 3 ^ 40 * 4170829 * 2
def baseEnd_4170829 : Nat := 475920001046970521345825

theorem tailTrace_4170829 : CollatzResearch.WordTrace tailWord_4170829 prefixEnd_4170829 475920001046970521345825 := by
  unfold tailWord_4170829
  simp only [CollatzResearch.WordTrace]
  refine ⟨152122631006806328727547541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101415087337870885818365027 152122631006806328727547541)
  ·
    refine ⟨7130748328444046659103791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152122631006806328727547541 7130748328444046659103791)
    ·
      refine ⟨10696122492666069988655687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7130748328444046659103791 10696122492666069988655687)
      ·
        refine ⟨16044183738999104982983531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696122492666069988655687 16044183738999104982983531)
        ·
          refine ⟨24066275608498657474475297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16044183738999104982983531 24066275608498657474475297)
          ·
            refine ⟨18049706706373993105856473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24066275608498657474475297 18049706706373993105856473)
            ·
              refine ⟨13537280029780494829392355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18049706706373993105856473 13537280029780494829392355)
              ·
                refine ⟨20305920044670742244088533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13537280029780494829392355 20305920044670742244088533)
                ·
                  refine ⟨475920001046970521345825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20305920044670742244088533 475920001046970521345825)
                  ·
                    rfl

theorem cell22_4170829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4170829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170829 prefixEnd_4170829 := by exact prefixLift 4170829
  have htrace : WordTrace (prefixWord ++ tailWord_4170829) baseStart_4170829 baseEnd_4170829 := by
    simpa [prefixWord, tailWord_4170829, baseEnd_4170829] using wordTrace_append hprefix tailTrace_4170829
  have hstable : (prefixWord ++ tailWord_4170829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170829).length < 2 ^ (prefixWord ++ tailWord_4170829).sum := by decide
  have hdescent : baseEnd_4170829 < baseStart_4170829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170872 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_4170872 : Nat := 118140960795 + 4170872 * 2 ^ 59
def prefixEnd_4170872 : Nat := 4983230072969 + 3 ^ 40 * 4170872 * 2
def baseEnd_4170872 : Nat := 1427774722919673785212343

theorem tailTrace_4170872 : CollatzResearch.WordTrace tailWord_4170872 prefixEnd_4170872 1427774722919673785212343 := by
  unfold tailWord_4170872
  simp only [CollatzResearch.WordTrace]
  refine ⟨76062099672825273535681435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101416132897100364714241913 76062099672825273535681435)
  ·
    refine ⟨114093149509237910303522153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76062099672825273535681435 114093149509237910303522153)
    ·
      refine ⟨85569862131928432727641615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114093149509237910303522153 85569862131928432727641615)
      ·
        refine ⟨128354793197892649091462423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85569862131928432727641615 128354793197892649091462423)
        ·
          refine ⟨192532189796838973637193635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128354793197892649091462423 192532189796838973637193635)
          ·
            refine ⟨288798284695258460455790453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192532189796838973637193635 288798284695258460455790453)
            ·
              refine ⟨27074839190180480667730355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288798284695258460455790453 27074839190180480667730355)
              ·
                refine ⟨40612258785270721001595533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27074839190180480667730355 40612258785270721001595533)
                ·
                  refine ⟨15229597044476520375598325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40612258785270721001595533 15229597044476520375598325)
                  ·
                    refine ⟨1427774722919673785212343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229597044476520375598325 1427774722919673785212343)
                    ·
                      rfl

theorem cell22_4170872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_4170872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170872 prefixEnd_4170872 := by exact prefixLift 4170872
  have htrace : WordTrace (prefixWord ++ tailWord_4170872) baseStart_4170872 baseEnd_4170872 := by
    simpa [prefixWord, tailWord_4170872, baseEnd_4170872] using wordTrace_append hprefix tailTrace_4170872
  have hstable : (prefixWord ++ tailWord_4170872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170872).length < 2 ^ (prefixWord ++ tailWord_4170872).sum := by decide
  have hdescent : baseEnd_4170872 < baseStart_4170872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170876 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_4170876 : Nat := 118140960795 + 4170876 * 2 ^ 59
def prefixEnd_4170876 : Nat := 4983230072969 + 3 ^ 40 * 4170876 * 2
def baseEnd_4170876 : Nat := 1427776092201419108112331

theorem tailTrace_4170876 : CollatzResearch.WordTrace tailWord_4170876 prefixEnd_4170876 1427776092201419108112331 := by
  unfold tailWord_4170876
  simp only [CollatzResearch.WordTrace]
  refine ⟨76062172618818027877254241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101416230158424037169672321 76062172618818027877254241)
  ·
    refine ⟨57046629464113520907940681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76062172618818027877254241 57046629464113520907940681)
    ·
      refine ⟨42784972098085140680955511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57046629464113520907940681 42784972098085140680955511)
      ·
        refine ⟨64177458147127711021433267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42784972098085140680955511 64177458147127711021433267)
        ·
          refine ⟨96266187220691566532149901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64177458147127711021433267 96266187220691566532149901)
          ·
            refine ⟨36099820207759337449556213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96266187220691566532149901 36099820207759337449556213)
            ·
              refine ⟨3384358144477437885895895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36099820207759337449556213 3384358144477437885895895)
              ·
                refine ⟨5076537216716156828843843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384358144477437885895895 5076537216716156828843843)
                ·
                  refine ⟨7614805825074235243265765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076537216716156828843843 7614805825074235243265765)
                  ·
                    refine ⟨1427776092201419108112331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7614805825074235243265765 1427776092201419108112331)
                    ·
                      rfl

theorem cell22_4170876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_4170876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170876 prefixEnd_4170876 := by exact prefixLift 4170876
  have htrace : WordTrace (prefixWord ++ tailWord_4170876) baseStart_4170876 baseEnd_4170876 := by
    simpa [prefixWord, tailWord_4170876, baseEnd_4170876] using wordTrace_append hprefix tailTrace_4170876
  have hstable : (prefixWord ++ tailWord_4170876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170876).length < 2 ^ (prefixWord ++ tailWord_4170876).sum := by decide
  have hdescent : baseEnd_4170876 < baseStart_4170876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170887 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_4170887 : Nat := 118140960795 + 4170887 * 2 ^ 59
def prefixEnd_4170887 : Nat := 4983230072969 + 3 ^ 40 * 4170887 * 2
def baseEnd_4170887 : Nat := 1427779857726218746087297

theorem tailTrace_4170887 : CollatzResearch.WordTrace tailWord_4170887 prefixEnd_4170887 1427779857726218746087297 := by
  unfold tailWord_4170887
  simp only [CollatzResearch.WordTrace]
  refine ⟨152124746440596204633158915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101416497627064136422105943 152124746440596204633158915)
  ·
    refine ⟨228187119660894306949738373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152124746440596204633158915 228187119660894306949738373)
    ·
      refine ⟨42785084936417682553075945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228187119660894306949738373 42785084936417682553075945)
      ·
        refine ⟨32088813702313261914806959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42785084936417682553075945 32088813702313261914806959)
        ·
          refine ⟨48133220553469892872210439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32088813702313261914806959 48133220553469892872210439)
          ·
            refine ⟨72199830830204839308315659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48133220553469892872210439 72199830830204839308315659)
            ·
              refine ⟨108299746245307258962473489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72199830830204839308315659 108299746245307258962473489)
              ·
                refine ⟨81224809683980444221855117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108299746245307258962473489 81224809683980444221855117)
                ·
                  refine ⟨30459303631492666583195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81224809683980444221855117 30459303631492666583195669)
                  ·
                    refine ⟨1427779857726218746087297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30459303631492666583195669 1427779857726218746087297)
                    ·
                      rfl

theorem cell22_4170887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_4170887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170887 prefixEnd_4170887 := by exact prefixLift 4170887
  have htrace : WordTrace (prefixWord ++ tailWord_4170887) baseStart_4170887 baseEnd_4170887 := by
    simpa [prefixWord, tailWord_4170887, baseEnd_4170887] using wordTrace_append hprefix tailTrace_4170887
  have hstable : (prefixWord ++ tailWord_4170887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170887).length < 2 ^ (prefixWord ++ tailWord_4170887).sum := by decide
  have hdescent : baseEnd_4170887 < baseStart_4170887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170906 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_4170906 : Nat := 118140960795 + 4170906 * 2 ^ 59
def prefixEnd_4170906 : Nat := 4983230072969 + 3 ^ 40 * 4170906 * 2
def baseEnd_4170906 : Nat := 1427786361814509029862239

theorem tailTrace_4170906 : CollatzResearch.WordTrace tailWord_4170906 prefixEnd_4170906 1427786361814509029862239 := by
  unfold tailWord_4170906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38031359856881842719525143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101416959618351580585400381 38031359856881842719525143)
  ·
    refine ⟨57047039785322764079287715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38031359856881842719525143 57047039785322764079287715)
    ·
      refine ⟨85570559677984146118931573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57047039785322764079287715 85570559677984146118931573)
      ·
        refine ⟨8022239969811013698649835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85570559677984146118931573 8022239969811013698649835)
        ·
          refine ⟨12033359954716520547974753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022239969811013698649835 12033359954716520547974753)
          ·
            refine ⟨9025019966037390410981065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12033359954716520547974753 9025019966037390410981065)
            ·
              refine ⟨6768764974528042808235799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025019966037390410981065 6768764974528042808235799)
              ·
                refine ⟨10153147461792064212353699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768764974528042808235799 10153147461792064212353699)
                ·
                  refine ⟨15229721192688096318530549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153147461792064212353699 15229721192688096318530549)
                  ·
                    refine ⟨1427786361814509029862239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229721192688096318530549 1427786361814509029862239)
                    ·
                      rfl

theorem cell22_4170906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_4170906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170906 prefixEnd_4170906 := by exact prefixLift 4170906
  have htrace : WordTrace (prefixWord ++ tailWord_4170906) baseStart_4170906 baseEnd_4170906 := by
    simpa [prefixWord, tailWord_4170906, baseEnd_4170906] using wordTrace_append hprefix tailTrace_4170906
  have hstable : (prefixWord ++ tailWord_4170906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170906).length < 2 ^ (prefixWord ++ tailWord_4170906).sum := by decide
  have hdescent : baseEnd_4170906 < baseStart_4170906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170957 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4170957 : Nat := 118140960795 + 4170957 * 2 ^ 59
def prefixEnd_4170957 : Nat := 4983230072969 + 3 ^ 40 * 4170957 * 2
def baseEnd_4170957 : Nat := 1427803820156761896837083

theorem tailTrace_4170957 : CollatzResearch.WordTrace tailWord_4170957 prefixEnd_4170957 1427803820156761896837083 := by
  unfold tailWord_4170957
  simp only [CollatzResearch.WordTrace]
  refine ⟨152127299550342606588207125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101418199700228404392138083 152127299550342606588207125)
  ·
    refine ⟨7130967166422309683822209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152127299550342606588207125 7130967166422309683822209)
    ·
      refine ⟨5348225374816732262866657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7130967166422309683822209 5348225374816732262866657)
      ·
        refine ⟨4011169031112549197149993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5348225374816732262866657 4011169031112549197149993)
        ·
          refine ⟨3008376773334411897862495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4011169031112549197149993 3008376773334411897862495)
          ·
            refine ⟨4512565160001617846793743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008376773334411897862495 4512565160001617846793743)
            ·
              refine ⟨6768847740002426770190615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512565160001617846793743 6768847740002426770190615)
              ·
                refine ⟨10153271610003640155285923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768847740002426770190615 10153271610003640155285923)
                ·
                  refine ⟨15229907415005460232928885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153271610003640155285923 15229907415005460232928885)
                  ·
                    refine ⟨1427803820156761896837083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229907415005460232928885 1427803820156761896837083)
                    ·
                      rfl

theorem cell22_4170957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4170957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4170957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4170957 prefixEnd_4170957 := by exact prefixLift 4170957
  have htrace : WordTrace (prefixWord ++ tailWord_4170957) baseStart_4170957 baseEnd_4170957 := by
    simpa [prefixWord, tailWord_4170957, baseEnd_4170957] using wordTrace_append hprefix tailTrace_4170957
  have hstable : (prefixWord ++ tailWord_4170957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170957).length < 2 ^ (prefixWord ++ tailWord_4170957).sum := by decide
  have hdescent : baseEnd_4170957 < baseStart_4170957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171054 : List Nat := [4, 1, 3, 14]
def baseStart_4171054 : Nat := 118140960795 + 4171054 * 2 ^ 59
def prefixEnd_4171054 : Nat := 4983230072969 + 3 ^ 40 * 4171054 * 2
def baseEnd_4171054 : Nat := 1958624177282696813665

theorem tailTrace_4171054 : CollatzResearch.WordTrace tailWord_4171054 prefixEnd_4171054 1958624177282696813665 := by
  unfold tailWord_4171054
  simp only [CollatzResearch.WordTrace]
  refine ⟨19016354678873899019311027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101420558287327461436325477 19016354678873899019311027)
  ·
    refine ⟨28524532018310848528966541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19016354678873899019311027 28524532018310848528966541)
    ·
      refine ⟨10696699506866568198362453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28524532018310848528966541 10696699506866568198362453)
      ·
        refine ⟨1958624177282696813665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 10696699506866568198362453 1958624177282696813665)
        ·
          rfl

theorem cell22_4171054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 14].length) (baseStart_4171054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171054 prefixEnd_4171054 := by exact prefixLift 4171054
  have htrace : WordTrace (prefixWord ++ tailWord_4171054) baseStart_4171054 baseEnd_4171054 := by
    simpa [prefixWord, tailWord_4171054, baseEnd_4171054] using wordTrace_append hprefix tailTrace_4171054
  have hstable : (prefixWord ++ tailWord_4171054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171054).length < 2 ^ (prefixWord ++ tailWord_4171054).sum := by decide
  have hdescent : baseEnd_4171054 < baseStart_4171054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171058 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_4171058 : Nat := 118140960795 + 4171058 * 2 ^ 59
def prefixEnd_4171058 : Nat := 4983230072969 + 3 ^ 40 * 4171058 * 2
def baseEnd_4171058 : Nat := 1427838394520831300061773

theorem tailTrace_4171058 : CollatzResearch.WordTrace tailWord_4171058 prefixEnd_4171058 1427838394520831300061773 := by
  unfold tailWord_4171058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38032745830744175209408457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101420655548651133891755885 38032745830744175209408457)
  ·
    refine ⟨28524559373058131407056343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38032745830744175209408457 28524559373058131407056343)
    ·
      refine ⟨42786839059587197110584515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28524559373058131407056343 42786839059587197110584515)
      ·
        refine ⟨64180258589380795665876773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42786839059587197110584515 64180258589380795665876773)
        ·
          refine ⟨12033798485508899187351895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64180258589380795665876773 12033798485508899187351895)
          ·
            refine ⟨18050697728263348781027843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033798485508899187351895 18050697728263348781027843)
            ·
              refine ⟨27076046592395023171541765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18050697728263348781027843 27076046592395023171541765)
              ·
                refine ⟨5076758736074066844664081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27076046592395023171541765 5076758736074066844664081)
                ·
                  refine ⟨3807569052055550133498061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076758736074066844664081 3807569052055550133498061)
                  ·
                    refine ⟨1427838394520831300061773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3807569052055550133498061 1427838394520831300061773)
                    ·
                      rfl

theorem cell22_4171058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_4171058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171058 prefixEnd_4171058 := by exact prefixLift 4171058
  have htrace : WordTrace (prefixWord ++ tailWord_4171058) baseStart_4171058 baseEnd_4171058 := by
    simpa [prefixWord, tailWord_4171058, baseEnd_4171058] using wordTrace_append hprefix tailTrace_4171058
  have hstable : (prefixWord ++ tailWord_4171058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171058).length < 2 ^ (prefixWord ++ tailWord_4171058).sum := by decide
  have hdescent : baseEnd_4171058 < baseStart_4171058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171071 : List Nat := [1, 1, 2, 2, 4, 4, 1, 7]
def baseStart_4171071 : Nat := 118140960795 + 4171071 * 2 ^ 59
def prefixEnd_4171071 : Nat := 4983230072969 + 3 ^ 40 * 4171071 * 2
def baseEnd_4171071 : Nat := 158649204965167066609637

theorem tailTrace_4171071 : CollatzResearch.WordTrace tailWord_4171071 prefixEnd_4171071 158649204965167066609637 := by
  unfold tailWord_4171071
  simp only [CollatzResearch.WordTrace]
  refine ⟨152131457471929604057857067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101420971647953069371904711 152131457471929604057857067)
  ·
    refine ⟨228197186207894406086785601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152131457471929604057857067 228197186207894406086785601)
    ·
      refine ⟨171147889655920804565089201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228197186207894406086785601 171147889655920804565089201)
      ·
        refine ⟨128360917241940603423816901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171147889655920804565089201 128360917241940603423816901)
        ·
          refine ⟨24067671982863863141965669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128360917241940603423816901 24067671982863863141965669)
          ·
            refine ⟨4512688496786974339118563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24067671982863863141965669 4512688496786974339118563)
            ·
              refine ⟨6769032745180461508677845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512688496786974339118563 6769032745180461508677845)
              ·
                refine ⟨158649204965167066609637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6769032745180461508677845 158649204965167066609637)
                ·
                  rfl

theorem cell22_4171071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 7].length) (baseStart_4171071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171071 prefixEnd_4171071 := by exact prefixLift 4171071
  have htrace : WordTrace (prefixWord ++ tailWord_4171071) baseStart_4171071 baseEnd_4171071 := by
    simpa [prefixWord, tailWord_4171071, baseEnd_4171071] using wordTrace_append hprefix tailTrace_4171071
  have hstable : (prefixWord ++ tailWord_4171071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171071).length < 2 ^ (prefixWord ++ tailWord_4171071).sum := by decide
  have hdescent : baseEnd_4171071 < baseStart_4171071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171116 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_4171116 : Nat := 118140960795 + 4171116 * 2 ^ 59
def prefixEnd_4171116 : Nat := 4983230072969 + 3 ^ 40 * 4171116 * 2
def baseEnd_4171116 : Nat := 475952749702046160703865

theorem tailTrace_4171116 : CollatzResearch.WordTrace tailWord_4171116 prefixEnd_4171116 475952749702046160703865 := by
  unfold tailWord_4171116
  simp only [CollatzResearch.WordTrace]
  refine ⟨76066549378383288371622601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101422065837844384495496801 76066549378383288371622601)
  ·
    refine ⟨57049912033787466278716951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76066549378383288371622601 57049912033787466278716951)
    ·
      refine ⟨85574868050681199418075427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57049912033787466278716951 85574868050681199418075427)
      ·
        refine ⟨128362302076021799127113141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85574868050681199418075427 128362302076021799127113141)
        ·
          refine ⟨12033965819627043668166857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128362302076021799127113141 12033965819627043668166857)
          ·
            refine ⟨9025474364720282751125143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12033965819627043668166857 9025474364720282751125143)
            ·
              refine ⟨13538211547080424126687715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025474364720282751125143 13538211547080424126687715)
              ·
                refine ⟨20307317320620636190031573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13538211547080424126687715 20307317320620636190031573)
                ·
                  refine ⟨475952749702046160703865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20307317320620636190031573 475952749702046160703865)
                  ·
                    rfl

theorem cell22_4171116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_4171116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171116 prefixEnd_4171116 := by exact prefixLift 4171116
  have htrace : WordTrace (prefixWord ++ tailWord_4171116) baseStart_4171116 baseEnd_4171116 := by
    simpa [prefixWord, tailWord_4171116, baseEnd_4171116] using wordTrace_append hprefix tailTrace_4171116
  have hstable : (prefixWord ++ tailWord_4171116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171116).length < 2 ^ (prefixWord ++ tailWord_4171116).sum := by decide
  have hdescent : baseEnd_4171116 < baseStart_4171116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171133 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 5]
def baseStart_4171133 : Nat := 118140960795 + 4171133 * 2 ^ 59
def prefixEnd_4171133 : Nat := 4983230072969 + 3 ^ 40 * 4171133 * 2
def baseEnd_4171133 : Nat := 475954689517852034812181

theorem tailTrace_4171133 : CollatzResearch.WordTrace tailWord_4171133 prefixEnd_4171133 475954689517852034812181 := by
  unfold tailWord_4171133
  simp only [CollatzResearch.WordTrace]
  refine ⟨152133718797704988646614053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101422479198469992431076035 152133718797704988646614053)
  ·
    refine ⟨28525072274569685371240135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152133718797704988646614053 28525072274569685371240135)
    ·
      refine ⟨42787608411854528056860203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28525072274569685371240135 42787608411854528056860203)
      ·
        refine ⟨64181412617781792085290305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42787608411854528056860203 64181412617781792085290305)
        ·
          refine ⟨48136059463336344063967729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64181412617781792085290305 48136059463336344063967729)
          ·
            refine ⟨36102044597502258047975797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48136059463336344063967729 36102044597502258047975797)
            ·
              refine ⟨3384566681015836691997731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36102044597502258047975797 3384566681015836691997731)
              ·
                refine ⟨5076850021523755037996597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384566681015836691997731 5076850021523755037996597)
                ·
                  refine ⟨475954689517852034812181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5076850021523755037996597 475954689517852034812181)
                  ·
                    rfl

theorem cell22_4171133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_4171133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171133 prefixEnd_4171133 := by exact prefixLift 4171133
  have htrace : WordTrace (prefixWord ++ tailWord_4171133) baseStart_4171133 baseEnd_4171133 := by
    simpa [prefixWord, tailWord_4171133, baseEnd_4171133] using wordTrace_append hprefix tailTrace_4171133
  have hstable : (prefixWord ++ tailWord_4171133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171133).length < 2 ^ (prefixWord ++ tailWord_4171133).sum := by decide
  have hdescent : baseEnd_4171133 < baseStart_4171133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171191 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 4, 4]
def baseStart_4171191 : Nat := 118140960795 + 4171191 * 2 ^ 59
def prefixEnd_4171191 : Nat := 4983230072969 + 3 ^ 40 * 4171191 * 2
def baseEnd_4171191 : Nat := 1427883923138863286486365

theorem tailTrace_4171191 : CollatzResearch.WordTrace tailWord_4171191 prefixEnd_4171191 1427883923138863286486365 := by
  unfold tailWord_4171191
  simp only [CollatzResearch.WordTrace]
  refine ⟨152135834231494864552225427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101423889487663243034816951 152135834231494864552225427)
  ·
    refine ⟨228203751347242296828338141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152135834231494864552225427 228203751347242296828338141)
    ·
      refine ⟨85576406755215861310626803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228203751347242296828338141 85576406755215861310626803)
      ·
        refine ⟨128364610132823791965940205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85576406755215861310626803 128364610132823791965940205)
        ·
          refine ⟨48136728799808921987227577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128364610132823791965940205 48136728799808921987227577)
          ·
            refine ⟨36102546599856691490420683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48136728799808921987227577 36102546599856691490420683)
            ·
              refine ⟨54153819899785037235631025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36102546599856691490420683 54153819899785037235631025)
              ·
                refine ⟨40615364924838777926723269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54153819899785037235631025 40615364924838777926723269)
                ·
                  refine ⟨7615380923407270861260613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40615364924838777926723269 7615380923407270861260613)
                  ·
                    refine ⟨1427883923138863286486365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615380923407270861260613 1427883923138863286486365)
                    ·
                      rfl

theorem cell22_4171191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_4171191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171191 prefixEnd_4171191 := by exact prefixLift 4171191
  have htrace : WordTrace (prefixWord ++ tailWord_4171191) baseStart_4171191 baseEnd_4171191 := by
    simpa [prefixWord, tailWord_4171191, baseEnd_4171191] using wordTrace_append hprefix tailTrace_4171191
  have hstable : (prefixWord ++ tailWord_4171191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171191).length < 2 ^ (prefixWord ++ tailWord_4171191).sum := by decide
  have hdescent : baseEnd_4171191 < baseStart_4171191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171208 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_4171208 : Nat := 118140960795 + 4171208 * 2 ^ 59
def prefixEnd_4171208 : Nat := 4983230072969 + 3 ^ 40 * 4171208 * 2
def baseEnd_4171208 : Nat := 1427889742586280908811313

theorem tailTrace_4171208 : CollatzResearch.WordTrace tailWord_4171208 prefixEnd_4171208 1427889742586280908811313 := by
  unfold tailWord_4171208
  simp only [CollatzResearch.WordTrace]
  refine ⟨76068227136216638227797139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101424302848288850970396185 76068227136216638227797139)
  ·
    refine ⟨114102340704324957341695709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76068227136216638227797139 114102340704324957341695709)
    ·
      refine ⟨42788377764121859003135891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114102340704324957341695709 42788377764121859003135891)
      ·
        refine ⟨64182566646182788504703837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42788377764121859003135891 64182566646182788504703837)
        ·
          refine ⟨24068462492318545689263939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64182566646182788504703837 24068462492318545689263939)
          ·
            refine ⟨36102693738477818533895909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24068462492318545689263939 36102693738477818533895909)
            ·
              refine ⟨6769255075964590975105483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36102693738477818533895909 6769255075964590975105483)
              ·
                refine ⟨10153882613946886462658225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769255075964590975105483 10153882613946886462658225)
                ·
                  refine ⟨7615411960460164846993669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10153882613946886462658225 7615411960460164846993669)
                  ·
                    refine ⟨1427889742586280908811313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615411960460164846993669 1427889742586280908811313)
                    ·
                      rfl

theorem cell22_4171208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_4171208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171208 prefixEnd_4171208 := by exact prefixLift 4171208
  have htrace : WordTrace (prefixWord ++ tailWord_4171208) baseStart_4171208 baseEnd_4171208 := by
    simpa [prefixWord, tailWord_4171208, baseEnd_4171208] using wordTrace_append hprefix tailTrace_4171208
  have hstable : (prefixWord ++ tailWord_4171208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171208).length < 2 ^ (prefixWord ++ tailWord_4171208).sum := by decide
  have hdescent : baseEnd_4171208 < baseStart_4171208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171285 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 5]
def baseStart_4171285 : Nat := 118140960795 + 4171285 * 2 ^ 59
def prefixEnd_4171285 : Nat := 4983230072969 + 3 ^ 40 * 4171285 * 2
def baseEnd_4171285 : Nat := 475972033753292791545359

theorem tailTrace_4171285 : CollatzResearch.WordTrace tailWord_4171285 prefixEnd_4171285 475972033753292791545359 := by
  unfold tailWord_4171285
  simp only [CollatzResearch.WordTrace]
  refine ⟨152139262693154318606147309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101426175128769545737431539 152139262693154318606147309)
  ·
    refine ⟨57052223509932869477305241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152139262693154318606147309 57052223509932869477305241)
    ·
      refine ⟨42789167632449652107978931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57052223509932869477305241 42789167632449652107978931)
      ·
        refine ⟨64183751448674478161968397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42789167632449652107978931 64183751448674478161968397)
        ·
          refine ⟨24068906793252929310738149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64183751448674478161968397 24068906793252929310738149)
          ·
            refine ⟨4512920023734924245763403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24068906793252929310738149 4512920023734924245763403)
            ·
              refine ⟨6769380035602386368645105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512920023734924245763403 6769380035602386368645105)
              ·
                refine ⟨5077035026701789776483829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769380035602386368645105 5077035026701789776483829)
                ·
                  refine ⟨475972033753292791545359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5077035026701789776483829 475972033753292791545359)
                  ·
                    rfl

theorem cell22_4171285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_4171285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171285 prefixEnd_4171285 := by exact prefixLift 4171285
  have htrace : WordTrace (prefixWord ++ tailWord_4171285) baseStart_4171285 baseEnd_4171285 := by
    simpa [prefixWord, tailWord_4171285, baseEnd_4171285] using wordTrace_append hprefix tailTrace_4171285
  have hstable : (prefixWord ++ tailWord_4171285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171285).length < 2 ^ (prefixWord ++ tailWord_4171285).sum := by decide
  have hdescent : baseEnd_4171285 < baseStart_4171285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171298 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4171298 : Nat := 118140960795 + 4171298 * 2 ^ 59
def prefixEnd_4171298 : Nat := 4983230072969 + 3 ^ 40 * 4171298 * 2
def baseEnd_4171298 : Nat := 1427920551425550674061037

theorem tailTrace_4171298 : CollatzResearch.WordTrace tailWord_4171298 prefixEnd_4171298 1427920551425550674061037 := by
  unfold tailWord_4171298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38034934210526805456592637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101426491228071481217580365 38034934210526805456592637)
  ·
    refine ⟨14263100328947552046222239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38034934210526805456592637 14263100328947552046222239)
    ·
      refine ⟨21394650493421328069333359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14263100328947552046222239 21394650493421328069333359)
      ·
        refine ⟨32091975740131992104000039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21394650493421328069333359 32091975740131992104000039)
        ·
          refine ⟨48137963610197988156000059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32091975740131992104000039 48137963610197988156000059)
          ·
            refine ⟨72206945415296982234000089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48137963610197988156000059 72206945415296982234000089)
            ·
              refine ⟨54155209061472736675500067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72206945415296982234000089 54155209061472736675500067)
              ·
                refine ⟨81232813592209105013250101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54155209061472736675500067 81232813592209105013250101)
                ·
                  refine ⟨7615576274269603594992197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81232813592209105013250101 7615576274269603594992197)
                  ·
                    refine ⟨1427920551425550674061037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615576274269603594992197 1427920551425550674061037)
                    ·
                      rfl

theorem cell22_4171298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4171298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171298 prefixEnd_4171298 := by exact prefixLift 4171298
  have htrace : WordTrace (prefixWord ++ tailWord_4171298) baseStart_4171298 baseEnd_4171298 := by
    simpa [prefixWord, tailWord_4171298, baseEnd_4171298] using wordTrace_append hprefix tailTrace_4171298
  have hstable : (prefixWord ++ tailWord_4171298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171298).length < 2 ^ (prefixWord ++ tailWord_4171298).sum := by decide
  have hdescent : baseEnd_4171298 < baseStart_4171298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171315 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 1, 4]
def baseStart_4171315 : Nat := 118140960795 + 4171315 * 2 ^ 59
def prefixEnd_4171315 : Nat := 4983230072969 + 3 ^ 40 * 4171315 * 2
def baseEnd_4171315 : Nat := 1427926370872968296385985

theorem tailTrace_4171315 : CollatzResearch.WordTrace tailWord_4171315 prefixEnd_4171315 1427926370872968296385985 := by
  unfold tailWord_4171315
  simp only [CollatzResearch.WordTrace]
  refine ⟨152140356883045633729739399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101426904588697089153159599 152140356883045633729739399)
  ·
    refine ⟨228210535324568450594609099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152140356883045633729739399 228210535324568450594609099)
    ·
      refine ⟨342315802986852675891913649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228210535324568450594609099 342315802986852675891913649)
      ·
        refine ⟨256736852240139506918935237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342315802986852675891913649 256736852240139506918935237)
        ·
          refine ⟨48138159795026157547300357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256736852240139506918935237 48138159795026157547300357)
          ·
            refine ⟨9025904961567404540118817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48138159795026157547300357 9025904961567404540118817)
            ·
              refine ⟨6769428721175553405089113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025904961567404540118817 6769428721175553405089113)
              ·
                refine ⟨5077071540881665053816835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769428721175553405089113 5077071540881665053816835)
                ·
                  refine ⟨7615607311322497580725253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077071540881665053816835 7615607311322497580725253)
                  ·
                    refine ⟨1427926370872968296385985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615607311322497580725253 1427926370872968296385985)
                    ·
                      rfl

theorem cell22_4171315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 4].length) (baseStart_4171315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171315 prefixEnd_4171315 := by exact prefixLift 4171315
  have htrace : WordTrace (prefixWord ++ tailWord_4171315) baseStart_4171315 baseEnd_4171315 := by
    simpa [prefixWord, tailWord_4171315, baseEnd_4171315] using wordTrace_append hprefix tailTrace_4171315
  have hstable : (prefixWord ++ tailWord_4171315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171315).length < 2 ^ (prefixWord ++ tailWord_4171315).sum := by decide
  have hdescent : baseEnd_4171315 < baseStart_4171315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
